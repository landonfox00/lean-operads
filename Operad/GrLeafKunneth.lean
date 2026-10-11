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

end GrComposite

end Operad
