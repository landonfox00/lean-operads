/-
# Endomorphisms at the inner operations of a graded composite

For endomorphisms `a`, `b` of parities `q`, `q'` of a graded linear species `N`, the maps
`1 ∘' a` and `1 ∘' b` acting at the inner operations of `M ∘ N`, one at a time with the Koszul
signs (`GrComposite.leafMap`), have the graded commutator acting the same way
(`GrComposite.leafMap_comm`):

  `[1 ∘' a, 1 ∘' b] = 1 ∘' [a, b]`.

The terms acting at two different inner operations cancel in pairs, with the sign of passing the
two maps past each other.
-/
import Operad.GrComposite
import Operad.FreeGrKunneth

universe u v w

namespace Operad

open Function Sym GerBV

namespace GrComposite

variable {R : Type u} [CommRing R]
  {M : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M A)] [GrSpecies R M]
  {N : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N A)] [GrSpecies R N]
  {q q' : Bool}

/-! ## Two endomorphisms at the inner operations -/

section Comm

lemma ltB_asymm {A : Type} (L : LinOrd A) {a b : A} (h : ltB L a b = true) :
    ltB L b a = false := by
  rw [ltB_eq_true] at h
  by_contra h'
  rw [Bool.not_eq_false, ltB_eq_true] at h'
  exact L.irrefl a (L.trans _ _ _ h h')

/-- **Two endomorphisms at different inner operations** commute up to the sign of passing them
past each other. -/
lemma leafLin_comm_ne (gm : GrSpEnd R N q) (gn : GrSpEnd R N q') {A : Type} [DecidableEq A]
    (L : LinOrd A) {j k : A} (hjk : j ≠ k) {B : A → Type} [∀ a, Fintype (B a)]
    [∀ a, DecidableEq (B a)] (a : A) {c : Bool} {y : N (B a)}
    (hy : GrSpecies.par (R := R) c y = y) :
    leafLin gm L k a (leafLin gn L j a y)
      = (if (a = k ∧ ltB L k j = true) ∨ (a = j ∧ ltB L j k = true) then σ R (q && q') else 1)
        • leafLin gn L j a (leafLin gm L k a y) := by
  have hgm : GrSpecies.par (R := R) (xor c q) (gm.app _ y) = gm.app _ y := by
    rw [← gm.app_par, hy]
  have hgn : GrSpecies.par (R := R) (xor c q') (gn.app _ y) = gn.app _ y := by
    rw [← gn.app_par, hy]
  unfold leafLin
  by_cases hak : a = k
  · subst hak
    have haj : a ≠ j := fun h => hjk h.symm
    rw [if_pos rfl, if_neg haj]
    by_cases hl : ltB L a j = true
    · rw [if_pos hl, if_pos (Or.inl ⟨rfl, hl⟩), GrSpecies.tw_hom q' hy, map_smul,
        GrSpecies.tw_hom q' hgm, smul_smul]
      congr 1
      cases q <;> cases q' <;> cases c <;> simp
    · rw [if_neg hl, if_neg (show ¬((a = a ∧ ltB L a j = true) ∨ (a = j ∧ ltB L j a = true))
        from fun h => h.elim (fun h' => hl h'.2) (fun h' => haj h'.1)), one_smul]
      rfl
  · by_cases haj : a = j
    · subst haj
      rw [if_neg hak, if_pos rfl]
      by_cases hl : ltB L a k = true
      · rw [if_pos hl, if_pos (Or.inr ⟨rfl, hl⟩), GrSpecies.tw_hom q hgn, GrSpecies.tw_hom q hy,
          map_smul, smul_smul]
        congr 1
        cases q <;> cases q' <;> cases c <;> simp
      · rw [if_neg hl, if_neg (show ¬((a = k ∧ ltB L k a = true) ∨ (a = a ∧ ltB L a k = true))
          from fun h => h.elim (fun h' => hak h'.1) (fun h' => hl h'.2)), one_smul]
        rfl
    · rw [if_neg hak, if_neg haj, if_neg (show ¬((a = k ∧ ltB L k j = true) ∨ (a = j ∧ ltB L j k = true))
        from fun h => h.elim (fun h' => hak h'.1) (fun h' => haj h'.1)), one_smul]
      by_cases h1 : ltB L a k = true <;> by_cases h2 : ltB L a j = true <;>
        simp only [h1, h2, ↓reduceIte, Bool.false_eq_true, LinearMap.id_apply, GrSpecies.tw_tw,
          Bool.xor_comm]

/-- **The same endomorphisms at the same inner operation.** -/
lemma leafLin_comm_self (gm : GrSpEnd R N q) (gn : GrSpEnd R N q') {A : Type} [DecidableEq A]
    (L : LinOrd A) (j : A) {B : A → Type} [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    (y : ∀ a, N (B a)) :
    (fun a => leafLin gm L j a (leafLin gn L j a (y a)))
      = update (fun a => leafLin (gm.gcomm gn) L j a (y a)) j (gm.app _ (gn.app _ (y j))) := by
  funext a
  by_cases haj : a = j
  · subst haj
    simp only [update_self]
    unfold leafLin
    simp
  · rw [update_of_ne haj]
    unfold leafLin
    simp only [if_neg haj]
    cases ltB L a j <;> simp [GrSpecies.tw_tw]

lemma leafLin_comm_self' (gm : GrSpEnd R N q) (gn : GrSpEnd R N q') {A : Type} [DecidableEq A]
    (L : LinOrd A) (j : A) {B : A → Type} [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    (y : ∀ a, N (B a)) :
    (fun a => leafLin gn L j a (leafLin gm L j a (y a)))
      = update (fun a => leafLin (gm.gcomm gn) L j a (y a)) j (gn.app _ (gm.app _ (y j))) := by
  funext a
  by_cases haj : a = j
  · subst haj
    simp only [update_self]
    unfold leafLin
    simp
  · rw [update_of_ne haj]
    unfold leafLin
    simp only [if_neg haj]
    cases ltB L a j <;> simp [GrSpecies.tw_tw, Bool.xor_comm]

variable {S : Type} [Fintype S] [DecidableEq S]

lemma prod_sign_ne {A : Type} [Fintype A] [DecidableEq A] (L : LinOrd A) {j k : A} (hjk : j ≠ k)
    (s : R) :
    ∏ a : A, (if (a = k ∧ ltB L k j = true) ∨ (a = j ∧ ltB L j k = true) then s else 1) = s := by
  rcases L.total j k hjk with h | h
  · have h1 : ltB L j k = true := (ltB_eq_true L j k).2 h
    have h2 := ltB_asymm L h1
    simp only [h1, h2, Bool.false_eq_true, and_false, false_or, and_true]
    rw [Finset.prod_ite_eq' Finset.univ j, if_pos (Finset.mem_univ _)]
  · have h1 : ltB L k j = true := (ltB_eq_true L k j).2 h
    have h2 := ltB_asymm L h1
    simp only [h1, h2, Bool.false_eq_true, and_false, or_false, and_true]
    rw [Finset.prod_ite_eq' Finset.univ k, if_pos (Finset.mem_univ _)]

/-- **Two endomorphisms at different inner operations of a homogeneous generator.** -/
lemma mk_leafGen_leafGen_ne (gm : GrSpEnd R N q) (gn : GrSpEnd R N q') (g : GrCompGen M N S)
    {c : g.A → Bool} (hy : ∀ a, GrSpecies.par (R := R) (c a) (g.y a) = g.y a) {j k : g.A}
    (hjk : j ≠ k) :
    mk R (leafGen gm (leafGen gn g j) k)
      = σ R (q && q') • mk R (leafGen gn (leafGen gm g k) j) := by
  set G : GrCompGen M N S := ⟨g.A, g.B, g.L, GrSpecies.tw (R := R) q'
    (GrSpecies.tw (R := R) q g.m), g.y, g.e⟩
  have hm : GrSpecies.tw (R := R) q (GrSpecies.tw (R := R) q' g.m)
      = GrSpecies.tw (R := R) q' (GrSpecies.tw (R := R) q g.m) := by
    rw [GrSpecies.tw_tw, GrSpecies.tw_tw, Bool.xor_comm]
  have hfun : (fun a => leafLin gm g.L k a (leafLin gn g.L j a (g.y a)))
      = fun a => (if (a = k ∧ ltB g.L k j = true) ∨ (a = j ∧ ltB g.L j k = true)
          then σ R (q && q') else 1) • leafLin gn g.L j a (leafLin gm g.L k a (g.y a)) :=
    funext fun a => leafLin_comm_ne gm gn g.L hjk a (hy a)
  have h := (mkY (R := R) G).map_smul_univ
    (fun a => if (a = k ∧ ltB g.L k j = true) ∨ (a = j ∧ ltB g.L j k = true)
      then σ R (q && q') else 1)
    (fun a => leafLin gn g.L j a (leafLin gm g.L k a (g.y a)))
  rw [prod_sign_ne g.L hjk] at h
  show mk R ⟨g.A, g.B, g.L, GrSpecies.tw (R := R) q (GrSpecies.tw (R := R) q' g.m),
      fun a => leafLin gm g.L k a (leafLin gn g.L j a (g.y a)), g.e⟩
    = σ R (q && q') • mk R ⟨g.A, g.B, g.L, GrSpecies.tw (R := R) q' (GrSpecies.tw (R := R) q g.m),
      fun a => leafLin gn g.L j a (leafLin gm g.L k a (g.y a)), g.e⟩
  rw [hm, hfun]
  exact h

/-- **The same endomorphisms at the same inner operation** give the graded commutator. -/
lemma mk_leafGen_leafGen_self (gm : GrSpEnd R N q) (gn : GrSpEnd R N q') (g : GrCompGen M N S)
    (j : g.A) :
    mk R (leafGen gm (leafGen gn g j) j)
      = σ R (q && q') • mk R (leafGen gn (leafGen gm g j) j)
        + mk R (leafGen (gm.gcomm gn) g j) := by
  set G : GrCompGen M N S := leafGen (gm.gcomm gn) g j
  have h1 : mk R (leafGen gm (leafGen gn g j) j)
      = mkY G (update G.y j (gm.app _ (gn.app _ (g.y j)))) := by
    show mk R ⟨g.A, g.B, g.L, GrSpecies.tw (R := R) q (GrSpecies.tw (R := R) q' g.m), _, g.e⟩ = _
    rw [GrSpecies.tw_tw, leafLin_comm_self gm gn g.L j g.y]
    rfl
  have h2 : mk R (leafGen gn (leafGen gm g j) j)
      = mkY G (update G.y j (gn.app _ (gm.app _ (g.y j)))) := by
    show mk R ⟨g.A, g.B, g.L, GrSpecies.tw (R := R) q' (GrSpecies.tw (R := R) q g.m), _, g.e⟩ = _
    rw [GrSpecies.tw_tw, Bool.xor_comm, leafLin_comm_self' gm gn g.L j g.y]
    rfl
  have hy3 : update G.y j (gm.app _ (gn.app _ (g.y j))
      - σ R (q && q') • gn.app _ (gm.app _ (g.y j))) = G.y := by
    funext a
    by_cases haj : a = j
    · rw [haj, update_self]
      show _ = leafLin (gm.gcomm gn) g.L j j (g.y j)
      unfold leafLin
      simp
    · rw [update_of_ne haj]
  have h3 : mk R G = mkY G (update G.y j (gm.app _ (gn.app _ (g.y j))
      - σ R (q && q') • gn.app _ (gm.app _ (g.y j)))) := by
    rw [hy3]
    rfl
  rw [h1, h2, h3, MultilinearMap.map_update_sub, MultilinearMap.map_update_smul]
  abel

/-- **The graded commutator of two endomorphisms at the inner operations** is the commutator
acting at the inner operations: `[1 ∘' a, 1 ∘' b] = 1 ∘' [a, b]`. -/
theorem leafMap_comm (gm : GrSpEnd R N q) (gn : GrSpEnd R N q') (x : GrComposite R M N S) :
    leafMap R M gm (leafMap R M gn x)
      = σ R (q && q') • leafMap R M gn (leafMap R M gm x) + leafMap R M (gm.gcomm gn) x := by
  have h : (leafMap R M gm).comp (leafMap (S := S) R M gn)
      = (σ R (q && q') • (leafMap R M gn).comp (leafMap R M gm) + leafMap R M (gm.gcomm gn) :
        GrComposite R M N S →ₗ[R] GrComposite R M N S) :=
    hom_ext fun g => by
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply]
      rw [mk_eq_sum (R := R) g]
      simp only [map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun c _ => ?_
      set g' := parGen (R := R) g p c
      have hy : ∀ a, GrSpecies.par (R := R) (c a) (g'.y a) = g'.y a := fun a => by
        show GrSpecies.par (R := R) (c a) (GrSpecies.par (R := R) (c a) (g.y a)) = _
        rw [GrSpecies.par_par, if_pos rfl]
      simp only [leafMap_mk, leafFun, map_sum, Finset.smul_sum]
      have hF : ∀ j k : g'.A, mk R (leafGen gm (leafGen gn g' j) k)
          = σ R (q && q') • mk R (leafGen gn (leafGen gm g' k) j)
            + if j = k then mk R (leafGen (gm.gcomm gn) g' j) else 0 := fun j k => by
        by_cases hjk : j = k
        · subst hjk
          rw [if_pos rfl]
          exact mk_leafGen_leafGen_self gm gn g' j
        · rw [if_neg hjk, add_zero]
          exact mk_leafGen_leafGen_ne gm gn g' hy hjk
      simp only [hF, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [add_left_inj]
      show (∑ x : g.A, ∑ y : g.A, σ R (q && q') • mk R (leafGen gn (leafGen gm g' y) x))
        = ∑ x : g.A, ∑ y : g.A, σ R (q && q') • mk R (leafGen gn (leafGen gm g' x) y)
      exact Finset.sum_comm
  exact LinearMap.congr_fun h x

end Comm

/-! ## Morphisms and projections at the inner operations -/

section Proj

variable {N' : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N' A)] [GrSpecies R N']
  {N'' : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N'' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N'' A)] [GrSpecies R N'']
  {S : Type} [Fintype S] [DecidableEq S]

omit [GrSpecies R M] in
lemma _root_.Operad.GrSpeciesHom.app_tw (ψ : GrSpeciesHom R N N') (e : Bool) {A : Type}
    [Fintype A] [DecidableEq A] (y : N A) :
    ψ.app A (GrSpecies.tw (R := R) e y) = GrSpecies.tw (R := R) e (ψ.app A y) := by
  simp only [GrSpecies.tw_apply, map_add, map_smul, ψ.app_par]

/-- **Composites of morphisms at the inner operations.** -/
lemma map₂_map₂ (ψ₁ : GrSpeciesHom R N' N'') (ψ₂ : GrSpeciesHom R N N')
    (ψ₃ : GrSpeciesHom R N N'')
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (y : N A), ψ₁.app A (ψ₂.app A y) = ψ₃.app A y)
    (x : GrComposite R M N S) :
    (map₂ idSpHom ψ₁).app S ((map₂ idSpHom ψ₂).app S x) = (map₂ idSpHom ψ₃).app S x := by
  have h' : ((map₂ (idSpHom (M := M)) ψ₁).app S).comp ((map₂ idSpHom ψ₂).app S)
      = (map₂ idSpHom ψ₃).app S := hom_ext fun g => by
    simp only [LinearMap.comp_apply, map₂_mk]
    show mk R ⟨g.A, g.B, g.L, g.m, fun a => ψ₁.app _ (ψ₂.app _ (g.y a)), g.e⟩
      = mk R ⟨g.A, g.B, g.L, g.m, fun a => ψ₃.app _ (g.y a), g.e⟩
    simp only [h]
  exact LinearMap.congr_fun h' x

lemma leafLin_app (ψ : GrSpeciesHom R N N') (gm : GrSpEnd R N q) (gm' : GrSpEnd R N' q)
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (y : N A),
      ψ.app A (gm.app A y) = gm'.app A (ψ.app A y))
    {A : Type} [DecidableEq A] (L : LinOrd A) (j : A) {B : A → Type} [∀ a, Fintype (B a)]
    [∀ a, DecidableEq (B a)] (a : A) (y : N (B a)) :
    ψ.app _ (leafLin gm L j a y) = leafLin gm' L j a (ψ.app _ y) := by
  unfold leafLin
  split_ifs
  · exact h _ y
  · exact ψ.app_tw q y
  · rfl

/-- **Morphisms at the inner operations commute with endomorphisms they intertwine.** -/
lemma map₂_leafMap (φ : SymSpeciesHom R M M)
    (hφ : ∀ (A : Type) [Fintype A] [DecidableEq A] (m : M A),
      φ.app A (GrSpecies.tw (R := R) q m) = GrSpecies.tw (R := R) q (φ.app A m))
    (ψ : GrSpeciesHom R N N') (gm : GrSpEnd R N q) (gm' : GrSpEnd R N' q)
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (y : N A),
      ψ.app A (gm.app A y) = gm'.app A (ψ.app A y))
    (x : GrComposite R M N S) :
    (map₂ φ ψ).app S (leafMap R M gm x) = leafMap R M gm' ((map₂ φ ψ).app S x) := by
  have h' : ((map₂ φ ψ).app S).comp (leafMap R M gm)
      = (leafMap R M gm').comp ((map₂ φ ψ).app S) := hom_ext fun g => by
    simp only [LinearMap.comp_apply, leafMap_mk, leafFun, map_sum, map₂_mk]
    refine Finset.sum_congr rfl fun j _ => ?_
    show mk R ⟨g.A, g.B, g.L, φ.app _ (GrSpecies.tw (R := R) q g.m),
        fun a => ψ.app _ (leafLin gm g.L j a (g.y a)), g.e⟩
      = mk R ⟨g.A, g.B, g.L, GrSpecies.tw (R := R) q (φ.app _ g.m),
        fun a => leafLin gm' g.L j a (ψ.app _ (g.y a)), g.e⟩
    rw [hφ]
    simp only [leafLin_app ψ gm gm' h]
  exact LinearMap.congr_fun h' x

/-- Endomorphisms with the same components act the same way. -/
lemma leafMap_congr {gm gm' : GrSpEnd R N q}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (y : N A), gm.app A y = gm'.app A y)
    (x : GrComposite R M N S) : leafMap R M gm x = leafMap R M gm' x := by
  have : gm = gm' := by
    cases gm
    cases gm'
    congr
    funext A _ _
    exact LinearMap.ext (h A)
  rw [this]

/-- **A vanishing endomorphism acts by zero.** -/
lemma leafMap_eq_zero {gm : GrSpEnd R N q}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (y : N A), gm.app A y = 0)
    (x : GrComposite R M N S) : leafMap R M gm x = 0 := by
  have h' : leafMap (S := S) R M gm = 0 := hom_ext fun g => by
    rw [leafMap_mk, LinearMap.zero_apply, leafFun]
    refine Finset.sum_eq_zero fun j _ => mk_of_y_eq_zero _ (a := j) ?_
    show leafLin gm g.L j j (g.y j) = 0
    unfold leafLin
    rw [if_pos rfl]
    exact h _ _
  rw [h', LinearMap.zero_apply]

variable (π : GrSpEnd R N false)
  (hπ : ∀ (A : Type) [Fintype A] [DecidableEq A] (y : N A), π.app A (π.app A y) = π.app A y)
include hπ

/-- The components of a generator split by an idempotent at the inner operations in `T`. -/
lemma leafMap_compl_piecewise (g : GrCompGen M N S) (T : Finset g.A) :
    leafMap R M (FreeGrL.GrSpEnd.compl R N π) (mk R { g with y := (T.piecewise
        (fun a => g.y a - π.app _ (g.y a)) (fun a => π.app _ (g.y a))) })
      = (T.card : R) • mk R { g with y := (T.piecewise
        (fun a => g.y a - π.app _ (g.y a)) (fun a => π.app _ (g.y a))) } := by
  set yT : ∀ a, N (g.B a) := T.piecewise (fun a => g.y a - π.app _ (g.y a))
    (fun a => π.app _ (g.y a))
  rw [leafMap_mk, leafFun]
  have hj : ∀ j : g.A, mk R (leafGen (FreeGrL.GrSpEnd.compl R N π) { g with y := yT } j)
      = if j ∈ T then mk R { g with y := yT } else 0 := fun j => by
    have hy : (fun a => leafLin (FreeGrL.GrSpEnd.compl R N π) g.L j a (yT a))
        = update yT j (yT j - π.app _ (yT j)) := by
      funext a
      by_cases haj : a = j
      · subst haj
        rw [update_self]
        unfold leafLin
        rw [if_pos rfl]
        rfl
      · rw [update_of_ne haj]
        unfold leafLin
        rw [if_neg haj]
        split_ifs
        · exact GrSpecies.tw_false _
        · rfl
    show mk R ⟨g.A, g.B, g.L, GrSpecies.tw (R := R) false g.m,
      fun a => leafLin (FreeGrL.GrSpEnd.compl R N π) g.L j a (yT a), g.e⟩ = _
    rw [GrSpecies.tw_false, hy]
    by_cases hjT : j ∈ T
    · rw [if_pos hjT]
      have : yT j - π.app _ (yT j) = yT j := by
        simp only [yT, Finset.piecewise_eq_of_mem _ _ _ hjT, map_sub, hπ, sub_self, sub_zero]
      rw [this, update_eq_self]
    · rw [if_neg hjT]
      have : yT j - π.app _ (yT j) = 0 := by
        simp only [yT, Finset.piecewise_eq_of_notMem _ _ _ hjT, hπ, sub_self]
      refine mk_of_y_eq_zero _ (a := j) ?_
      show update yT j (yT j - π.app _ (yT j)) j = 0
      rw [update_self, this]
  simp only [hj]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, ← Nat.cast_smul_eq_nsmul R]

omit hπ in
lemma map₂_toHom_mk (g : GrCompGen M N S) :
    (map₂ idSpHom π.toHom).app S (mk R g)
      = mk R { g with y := fun a => π.app _ (g.y a) } := by
  rw [map₂_mk]
  rfl

/-- **An element minus its projection lies in the positive eigenspaces** of the count of the inner
operations outside the image of the projection. -/
theorem sub_map₂_mem (x : GrComposite R M N S) :
    x - (map₂ idSpHom π.toHom).app S x
      ∈ ⨆ j : ℕ, Module.End.eigenspace (leafMap R M (FreeGrL.GrSpEnd.compl R N π)) ((j + 1 : ℕ) : R) := by
  induction x using induction_on with
  | h0 => simp
  | hadd x y hx hy =>
    rw [map_add, add_sub_add_comm]
    exact Submodule.add_mem _ hx hy
  | hsmul c x hx =>
    rw [map_smul, ← smul_sub]
    exact Submodule.smul_mem _ c hx
  | hmk g =>
    have hsplit : g.y = (fun a => g.y a - π.app _ (g.y a)) + fun a => π.app _ (g.y a) := by
      funext a
      simp
    have h1 : mk R g = ∑ T : Finset g.A, mk R { g with y := (T.piecewise
        (fun a => g.y a - π.app _ (g.y a)) (fun a => π.app _ (g.y a))) } := by
      have := (mkY (R := R) g).map_add_univ (fun a => g.y a - π.app _ (g.y a))
        (fun a => π.app _ (g.y a))
      rw [← hsplit] at this
      exact this
    rw [map₂_toHom_mk, h1, ← Finset.add_sum_erase _ _ (Finset.mem_univ ∅),
      Finset.piecewise_empty, add_sub_cancel_left]
    refine Submodule.sum_mem _ fun T hT => ?_
    have hpos : 0 < T.card := Finset.card_pos.2
      (Finset.nonempty_iff_ne_empty.2 (Finset.ne_of_mem_erase hT))
    refine Submodule.mem_iSup_of_mem (T.card - 1) (Module.End.mem_eigenspace_iff.2 ?_)
    rw [leafMap_compl_piecewise π hπ, Nat.sub_add_cancel hpos]

end Proj

/-! ## The number of inputs of the outer operation -/

section Outer

variable {N' : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N' A)] [GrSpecies R N']
  {S : Type} [Fintype S] [DecidableEq S]

variable (R M) in
/-- Multiplication by the number of inputs. -/
noncomputable def cardHom : SymSpeciesHom R M M where
  app A _ _ := (Fintype.card A : R) • LinearMap.id
  app_map {A B} _ _ _ _ σ m := by
    simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, Fintype.card_congr σ]

variable (R M N) in
/-- **The number of inputs of the outer operation**, as an endomorphism of `M ∘ N`. -/
noncomputable def outerN (S : Type) [Fintype S] [DecidableEq S] :
    GrComposite R M N S →ₗ[R] GrComposite R M N S :=
  (map₂ (cardHom R M) (GrSpEnd.id R N).toHom).app S

lemma outerN_mk (g : GrCompGen M N S) : outerN R M N S (mk R g) = (Fintype.card g.A : R) • mk R g := by
  rw [outerN, map₂_mk, ← mk_smul_m]
  rfl

lemma outerN_map₂ (ψ : GrSpeciesHom R N N') (x : GrComposite R M N S) :
    outerN R M N' S ((map₂ idSpHom ψ).app S x) = (map₂ idSpHom ψ).app S (outerN R M N S x) := by
  have h : (outerN R M N' S).comp ((map₂ idSpHom ψ).app S)
      = ((map₂ idSpHom ψ).app S).comp (outerN R M N S) := hom_ext fun g => by
    simp only [LinearMap.comp_apply, outerN_mk, map_smul, map₂_mk]
  exact LinearMap.congr_fun h x

lemma outerN_leafMap (gm : GrSpEnd R N q) (x : GrComposite R M N S) :
    outerN R M N S (leafMap R M gm x) = leafMap R M gm (outerN R M N S x) :=
  map₂_leafMap (cardHom R M) (fun A _ _ m => by
    simp only [cardHom, LinearMap.smul_apply, LinearMap.id_apply, map_smul])
    (GrSpEnd.id R N).toHom gm gm (fun _ _ _ _ => rfl) x

variable (R M N) in
/-- **The composites with an outer operation of `k` inputs.** -/
noncomputable abbrev outerEig (S : Type) [Fintype S] [DecidableEq S] (k : ℕ) :
    Submodule R (GrComposite R M N S) :=
  Module.End.eigenspace (outerN R M N S) (k : R)

lemma mk_mem_outerEig (g : GrCompGen M N S) : mk R g ∈ outerEig R M N S (Fintype.card g.A) :=
  Module.End.mem_eigenspace_iff.2 (outerN_mk g)

lemma map₂_mem_outerEig (ψ : GrSpeciesHom R N N') {k : ℕ} {x : GrComposite R M N S}
    (hx : x ∈ outerEig R M N S k) : (map₂ idSpHom ψ).app S x ∈ outerEig R M N' S k :=
  Module.End.mem_eigenspace_iff.2 (by rw [outerN_map₂, Module.End.mem_eigenspace_iff.1 hx,
    map_smul])

lemma leafMap_mem_outerEig (gm : GrSpEnd R N q) {k : ℕ} {x : GrComposite R M N S}
    (hx : x ∈ outerEig R M N S k) : leafMap R M gm x ∈ outerEig R M N S k :=
  Module.End.mem_eigenspace_iff.2 (by rw [outerN_leafMap, Module.End.mem_eigenspace_iff.1 hx,
    map_smul])

end Outer

/-! ## Künneth for the differentials at the inner operations -/

section Kunneth

variable {N' : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N' A)] [GrSpecies R N']
  {S : Type} [Fintype S] [DecidableEq S]
  {d : GrSpEnd R N true} (s : Splitting d)

namespace Splitting

/-- The projection at the inner operations kills the differential. -/
lemma map₂_leafMap_d (x : GrComposite R M N S) :
    (map₂ idSpHom s.p.toHom).app S (leafMap R M d x) = 0 := by
  rw [map₂_leafMap idSpHom (fun _ _ _ _ => rfl) s.p.toHom d (GrSpEnd.zero R N true)
    (fun A _ _ y => by rw [GrSpEnd.toHom_app, s.pd, GrSpEnd.zero_app]),
    leafMap_eq_zero (fun _ _ _ _ => rfl)]

/-- The differential kills the image of the projection. -/
lemma leafMap_d_map₂ (x : GrComposite R M N S) :
    leafMap R M d ((map₂ idSpHom s.p.toHom).app S x) = 0 := by
  rw [← map₂_leafMap idSpHom (fun _ _ _ _ => rfl) s.p.toHom (GrSpEnd.zero R N true) d
    (fun A _ _ y => by simp only [GrSpEnd.toHom_app, GrSpEnd.zero_app, map_zero, s.dp]),
    leafMap_eq_zero (fun _ _ _ _ => rfl), map_zero]

lemma map₂_map₂_p (x : GrComposite R M N S) :
    (map₂ idSpHom s.p.toHom).app S ((map₂ idSpHom s.p.toHom).app S x)
      = (map₂ idSpHom s.p.toHom).app S x :=
  map₂_map₂ _ _ _ (fun A _ _ y => s.pp A y) x

/-- **The derivation trick at the inner operations**: `d h + h d = 1 - p`. -/
lemma leaf_contract (x : GrComposite R M N S) :
    leafMap R M d (leafMap R M s.h x) + leafMap R M s.h (leafMap R M d x)
      = leafMap R M (FreeGrL.GrSpEnd.compl R N s.p) x := by
  rw [leafMap_comm d s.h, Bool.and_self, σ_true, neg_one_smul,
    show ∀ a b : GrComposite R M N S, -a + b + a = b from fun a b => by abel]
  refine leafMap_congr (fun A _ _ y => ?_) x
  rw [GrSpEnd.gcomm_app, Bool.and_self, σ_true, neg_one_smul, sub_neg_eq_add, s.dh]
  rfl

lemma leaf_compl_d (x : GrComposite R M N S) :
    leafMap R M (FreeGrL.GrSpEnd.compl R N s.p) (leafMap R M d x)
      = leafMap R M d (leafMap R M (FreeGrL.GrSpEnd.compl R N s.p) x) := by
  rw [leafMap_comm, Bool.false_and, σ_false, one_smul,
    leafMap_eq_zero (gm := (FreeGrL.GrSpEnd.compl R N s.p).gcomm d) (fun A _ _ y => by
      rw [GrSpEnd.gcomm_app, FreeGrL.GrSpEnd.compl_app, FreeGrL.GrSpEnd.compl_app, map_sub,
        s.pd, s.dp, Bool.false_and, σ_false, one_smul]
      abel), add_zero]

/-- **The projection at the inner operations is a retraction with acyclic kernel** on the
composites with an outer operation of `k` inputs, over a `ℚ`-algebra. -/
theorem leafRetract [Algebra ℚ R] (k : ℕ) :
    QIso.Retract (outerEig R M N S k) (leafMap R M d) ((map₂ idSpHom s.p.toHom).app S) where
  mem x hx := map₂_mem_outerEig _ hx
  memD x hx := leafMap_mem_outerEig _ hx
  rr x := Splitting.map₂_map₂_p s x
  rD x := Splitting.map₂_leafMap_d s x
  Dr x := Splitting.leafMap_d_map₂ s x
  acyc x hx hδx hpx := by
    have hpos := sub_map₂_mem (M := M) s.p s.pp x
    rw [hpx, sub_zero] at hpos
    obtain ⟨z, hz, hδz⟩ := exists_eq_of_contract
      (leafMap R M (FreeGrL.GrSpEnd.compl R N s.p)) (leafMap R M d) (leafMap R M s.h)
      (outerN R M N S) (k : R) (fun y => Splitting.leaf_compl_d s y)
      (fun y => (outerN_leafMap _ y).symm) (fun y => outerN_leafMap _ y)
      (fun y => Splitting.leaf_contract s y) hpos hδx (Module.End.mem_eigenspace_iff.1 hx)
    exact ⟨z, Module.End.mem_eigenspace_iff.2 hz, hδz⟩

end Splitting

variable {d' : GrSpEnd R N' true} (s' : Splitting d')

/-- **Künneth at the inner operations**: a morphism `g` commuting with the differentials, whose
reduction `p' g p` to the representatives of the homology is inverted by `k` on the composites
with an outer operation of `n` inputs, is a quasi-isomorphism there. -/
theorem qiso_leaf [Algebra ℚ R] (g : GrSpeciesHom R N N')
    (hg : ∀ (A : Type) [Fintype A] [DecidableEq A] (y : N A),
      g.app A (d.app A y) = d'.app A (g.app A y))
    (k : GrSpeciesHom R N' N) (n : ℕ)
    (hKG : ∀ x ∈ outerEig R M N S n, (map₂ idSpHom k).app S
      ((map₂ idSpHom (s'.p.toHom.comp (g.comp s.p.toHom))).app S x)
        = (map₂ idSpHom s.p.toHom).app S x)
    (hGK : ∀ y ∈ outerEig R M N' S n,
      (map₂ idSpHom (s'.p.toHom.comp (g.comp s.p.toHom))).app S ((map₂ idSpHom k).app S y)
        = (map₂ idSpHom s'.p.toHom).app S y) :
    QIso.Surj (outerEig R M N S n) (outerEig R M N' S n) (leafMap R M d) (leafMap R M d')
        ((map₂ idSpHom g).app S)
      ∧ QIso.Inj (outerEig R M N S n) (outerEig R M N' S n) (leafMap R M d) (leafMap R M d')
        ((map₂ idSpHom g).app S) := by
  have hr := Splitting.leafRetract s (M := M) (S := S) n
  have hr' := Splitting.leafRetract s' (M := M) (S := S) n
  have hFS : ∀ x ∈ outerEig R M N S n, (map₂ idSpHom g).app S x ∈ outerEig R M N' S n :=
    fun x hx => map₂_mem_outerEig _ hx
  have hFD : ∀ x, (map₂ idSpHom g).app S (leafMap R M d x)
      = leafMap R M d' ((map₂ idSpHom g).app S x) :=
    fun x => map₂_leafMap idSpHom (fun _ _ _ _ => rfl) g d d' hg x
  have hG : ∀ x, (map₂ idSpHom s'.p.toHom).app S ((map₂ idSpHom g).app S
      ((map₂ idSpHom s.p.toHom).app S x))
        = (map₂ idSpHom (s'.p.toHom.comp (g.comp s.p.toHom))).app S x := fun x => by
    rw [map₂_map₂ (M := M) (S := S) g s.p.toHom (g.comp s.p.toHom) (fun _ _ _ _ => rfl),
      map₂_map₂ (M := M) (S := S) s'.p.toHom (g.comp s.p.toHom)
        (s'.p.toHom.comp (g.comp s.p.toHom)) (fun _ _ _ _ => rfl)]
  exact ⟨QIso.surj_of_retract hr hr' hFS hFD hG (fun y hy => map₂_mem_outerEig _ hy) hGK,
    QIso.inj_of_retract hr hr' hFD hG hKG⟩

end Kunneth

end GrComposite

end Operad
