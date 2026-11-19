/-
# The hypercommutative operad in arity five: `dim HyperCom(5) = 34`

**`dim HyperCom(5) = 34`** over a field in which `2` and `3` are invertible
(`HyperCom.finrank_five`). The thirty-four operations `HyperCom.basis34` span over any
commutative ring (`Operad.HyperComFive`); here they are shown to be independent
(`HyperCom.linearIndependent_basis34`), in two hypercommutative algebras.

* **The algebra on `R × R`** of `Operad.HyperComModel`, with one of the scalars `c₃`, `c₄`,
  `c₅` equal to `1` and the others to `0`, on the inputs equal to `1` on a set `D` and to
  `(0, 1)` elsewhere (`HyperCom.wD`). The first coordinates of the values
  (`HyperCom.ev5`) form a triangular system: the iterated product for `D` everything,
  `m₃(x₀ x₁ x₂, x₃, x₄)` for `D` empty, `m₂(m₃(m₂(x_i, x_j), x_k, x_l), x_e)` for `D = {e}`,
  `m₃(x_S) · x_d · x_e` for `D = {d, e}` (`HyperCom.ev5_tt5`); then `m₄(x₀ x₁, …)` and
  `m₂(m₄(…), x_k)` with `c₄`, and `m₅` with `c₅`. So in a relation between the thirty-four
  operations, over any commutative ring, the coefficients of all but the ten operations
  `m₃(m₃(x_S), x_d, x_e)` vanish (`HyperCom.coef_eq_zero`). These ten vanish in this algebra
  (`HyperCom.ev5_qOp5`).
* **The algebra on `R[x]/(x³)`** of `Operad.HyperComCubic`, on the inputs equal to `x` on a
  pair `D` and to `x²` elsewhere. The value of `m₃(m₃(x_S), x_d, x_e)` has the constant
  coefficient `1` if `S` contains exactly one input of `D`, and `0` otherwise
  (`HyperCom.evA_qOp5`). The matrix of the triples and the pairs meeting in one input is the
  adjacency matrix `A` of the triangular graph on the ten pairs, with `A² + A - 2 = 4 J`; so
  `6 A⁻¹ = 3 A + 3 - 2 J`, an identity of integers checked by `decide` (`HyperCom.cert5`), and
  the ten coefficients vanish when `6` is invertible (`HyperCom.tri_eq_zero`).

The fields of characteristic two and three are not covered: there the algebra on `R[x]/(x³)`
does not separate the ten operations `m₃(m₃(x_S), x_d, x_e)`. The thirty-four operations span
in every characteristic, so `dim HyperCom(5) ≤ 34` there.
-/
import Operad.HyperComFive

universe u

namespace Operad

open Sym Finset SetOperad

namespace HyperCom

open HCAlg

variable {R : Type u} [CommRing R]

local notation "I" => SymOperadIdeal.span R (hcRel R)

/-! ## The values in the algebra on `R × R` -/

/-- The value of a WDVV composite in the model. -/
lemma model_wTerm (c : ℕ → R) {n : ℕ} (S : Finset (Fin n)) (w : Fin n → R × R) :
    (modelAlg c).app (Fin n) ((I).proj _ (wTerm (R := R) S)) w
      = wVal (R × R) (modelOps R c) S w :=
  hcHom_wTerm (modelOps R c) S w

/-- The inputs equal to `1` on `D` and to `(0, 1)` elsewhere. -/
def wD (D : Finset (Fin 5)) : Fin 5 → R × R := fun x => if x ∈ D then 1 else uH

lemma wD_mem {D : Finset (Fin 5)} {x : Fin 5} (h : x ∈ D) : wD (R := R) D x = 1 := if_pos h

lemma wD_notMem {D : Finset (Fin 5)} {x : Fin 5} (h : x ∉ D) : wD (R := R) D x = uH := if_neg h

lemma hL_wD (D : Finset (Fin 5)) (x : Fin 5) :
    hL R (wD (R := R) D x) = if x ∈ D then 0 else 1 := by
  by_cases h : x ∈ D
  · rw [wD_mem h, if_pos h, hL_one]
  · rw [wD_notMem h, if_neg h, hL_uH]

lemma fst_wD (D : Finset (Fin 5)) (x : Fin 5) :
    (wD (R := R) D x).1 = if x ∈ D then 1 else 0 := by
  by_cases h : x ∈ D
  · rw [wD_mem h, if_pos h]
    rfl
  · rw [wD_notMem h, if_neg h]
    rfl

/-- The functional is `1` on a product of inputs not all equal to `1`, and `0` otherwise. -/
lemma prod_hL_wD (D T : Finset (Fin 5)) :
    ∏ x ∈ T, hL R (wD (R := R) D x) = if Disjoint T D then 1 else 0 := by
  by_cases h : Disjoint T D
  · rw [if_pos h]
    refine Finset.prod_eq_one fun x hx => ?_
    rw [hL_wD, if_neg (Finset.disjoint_left.1 h hx)]
  · rw [if_neg h]
    obtain ⟨x, hxT, hxD⟩ := Finset.not_disjoint_iff.1 h
    refine Finset.prod_eq_zero hxT ?_
    rw [hL_wD, if_pos hxD]

/-- **The first coordinate of the value in the model**, a linear functional on the operations
of arity five. -/
noncomputable def ev5 (c : ℕ → R) (w : Fin 5 → R × R) : HyperComOp R (Fin 5) →ₗ[R] R where
  toFun x := ((modelAlg c).app (Fin 5) x w).1
  map_add' x y := by rw [map_add, MultilinearMap.add_apply, Prod.fst_add]
  map_smul' s x := by
    rw [map_smul, MultilinearMap.smul_apply, Prod.smul_fst, RingHom.id_apply]

lemma ev5_apply (c : ℕ → R) (w : Fin 5 → R × R) (x : HyperComOp R (Fin 5)) :
    ev5 c w x = ((modelAlg c).app (Fin 5) x w).1 := rfl

/-- The value of `m₅`. -/
lemma ev5_m5 (c : ℕ → R) (w : Fin 5 → R × R) :
    ev5 c w (opGen 5 (by norm_num)) = c 5 * ∏ i, hL R (w i) := by
  rw [ev5_apply, model_opGen, modelOps_of_ne c _ (by norm_num), Prod.smul_fst, Prod.fst_one,
    smul_eq_mul, mul_one]

lemma tOp5_eq (k : Fin 5) : tOp5 R {k}ᶜ = (I).proj _ (wTerm (R := R) ({k}ᶜ : Finset (Fin 5))) :=
  (proj_wTerm_eq_twoOp _ (by rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin])
    (by rw [compl_compl, Finset.card_singleton]) _ _ 0).symm

lemma pOp5_eq : pOp5 R {0, 1} = (I).proj _ (wTerm (R := R) ({0, 1} : Finset (Fin 5))) :=
  (proj_wTerm_eq_twoOp _ (by decide) (by decide) _ _ 0).symm

lemma qOp5_eq (S : Tri) : qOp5 R S.1 = (I).proj _ (wTerm (R := R) S.1) :=
  (proj_wTerm_eq_twoOp _ S.2 (by rw [Finset.card_compl, S.2, Fintype.card_fin]) _ _ 0).symm

/-- **The operations `m₃(m₃(x_S), …)` vanish in the model.** -/
lemma ev5_qOp5 (c : ℕ → R) (w : Fin 5 → R × R) (S : Tri) : ev5 c w (qOp5 R S.1) = 0 := by
  have hc : (S.1)ᶜ.card = 2 := by rw [Finset.card_compl, S.2, Fintype.card_fin]
  rw [ev5_apply, qOp5_eq, model_wTerm, wVal_model, S.2, hc, if_pos ⟨by omega, by omega⟩,
    modelInn_of_ne c (by omega), modelOut_of_ne c (by omega), map_smul, hL_one, smul_zero,
    zero_mul, mul_zero, zero_smul]
  rfl

/-- The value of `m₂(m₄(…), x_k)`. -/
lemma ev5_tOp5 (c : ℕ → R) (w : Fin 5 → R × R) (k : Fin 5) :
    ev5 c w (tOp5 R {k}ᶜ) = c 4 * (∏ x ∈ ({k}ᶜ : Finset (Fin 5)), hL R (w x)) * (w k).1 := by
  have h4 : ({k}ᶜ : Finset (Fin 5)).card = 4 := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  rw [ev5_apply, tOp5_eq, model_wTerm, wVal_model, compl_compl, h4, Finset.card_singleton,
    if_pos ⟨by omega, by omega⟩, modelInn_of_ne c (by omega), modelOut_two,
    Finset.prod_singleton, Prod.fst_mul, Prod.smul_fst, Prod.fst_one, smul_eq_mul, mul_one]

/-- The value of `m₄(m₂(x₀, x₁), …)`. -/
lemma ev5_pOp5 (c : ℕ → R) (w : Fin 5 → R × R) :
    ev5 c w (pOp5 R {0, 1})
      = c 4 * (hL R (w 0 * w 1) * ∏ x ∈ ({0, 1}ᶜ : Finset (Fin 5)), hL R (w x)) := by
  have h3 : ({0, 1}ᶜ : Finset (Fin 5)).card = 3 := by decide
  rw [ev5_apply, pOp5_eq, model_wTerm, wVal_model, h3, show ({0, 1} : Finset (Fin 5)).card = 2
    from by decide, if_pos ⟨by omega, by omega⟩, modelInn_two, modelOut_of_ne c (by omega),
    Finset.prod_pair (by decide), Prod.smul_fst, Prod.fst_one, smul_eq_mul, mul_one]

/-- The value of the iterated product of three inputs. -/
lemma model_t3 (c : ℕ → R) (v : Fin 3 → R × R) :
    (modelAlg c).app _ (t3 R) v = ∏ i, v i := by
  rw [t3, alg_map, c22, alg_comp, model_opGen, modelOps_two c _ rfl, modelOps_two c _ rfl,
    Fin.prod_univ_two, Fin.prod_univ_two, feed_self, feed_of_ne (by decide),
    ← Equiv.prod_comp (Fintype.equivFinOfCardEq card_W) v, Fintype.prod_sum_type,
    Fin.prod_univ_two, Fintype.prod_subsingleton _ slotOne, _root_.mul_comm]
  rfl

/-- The value of `m₂(m₃(m₂(x_i, x_j), x_k, x_l), x_e)`. -/
lemma model_eOp5 (c : ℕ → R) (w : Fin 5 → R × R) (e : Fin 5) :
    (modelAlg c).app _ (eOp5 R e) w
      = (modelAlg c).app _ (pOp R 0 1) (fun t => w (eE e (Sum.inr t))) * w e := by
  rw [eOp5, alg_map, alg_comp, model_opGen, modelOps_two c _ rfl, Fin.prod_univ_two, feed_self,
    feed_of_ne (by decide)]
  exact congrArg (fun z => _ * w z) (eE_outer e)

/-- The value of `m₃(x_S) · x_d · x_e`, for a relabelling sending the inner inputs onto `S`. -/
lemma model_tt5 (c : ℕ → R) (w : Fin 5 → R × R) (S : Tri) :
    ∃ E : Without (Fin 3) 0 ⊕ Fin 3 ≃ Fin 5,
      Finset.univ.image (fun b => E (Sum.inr b)) = S.1 ∧
      (modelAlg c).app _ (tt5 R S.1) w
        = ((c 3 * ∏ b, hL R (w (E (Sum.inr b)))) • (1 : R × R))
          * w (E (Sum.inl ⟨1, by decide⟩)) * w (E (Sum.inl ⟨2, by decide⟩)) := by
  obtain ⟨E, hE⟩ := exists_equiv_image S.1 S.2
    (show (S.1)ᶜ.card = 2 by rw [Finset.card_compl, S.2, Fintype.card_fin])
  refine ⟨E, hE, ?_⟩
  rw [← hE, ← map_comp_bin_m3 (by simp) isBin_t3 0 E, alg_map, alg_comp, model_t3,
    model_opGen, modelOps_of_ne c _ (by norm_num), Fin.prod_univ_three, feed_self,
    feed_of_ne (by decide), feed_of_ne (by decide)]

/-- The value of `m₃(x₀ x₁ x₂, x₃, x₄)`, for a relabelling. -/
lemma model_bq5 (c : ℕ → R) (w : Fin 5 → R × R) :
    ∃ E : Without (Fin 3) 0 ⊕ Fin 3 ≃ Fin 5,
      (modelAlg c).app _ (bq5 R {0, 1, 2}) w
        = (c 3 * (hL R (∏ b, w (E (Sum.inr b)))
          * (hL R (w (E (Sum.inl ⟨1, by decide⟩)))
            * hL R (w (E (Sum.inl ⟨2, by decide⟩)))))) • (1 : R × R) := by
  obtain ⟨E, hE⟩ := exists_equiv_image ({0, 1, 2} : Finset (Fin 5)) (q := 3) (p := 2)
    (by decide) (by decide)
  refine ⟨E, ?_⟩
  rw [← hE, ← map_comp_m3_bin (by simp) isBin_t3 0 E, alg_map, alg_comp, model_opGen,
    modelOps_of_ne c _ (by norm_num), model_t3, Fin.prod_univ_three, feed_self,
    feed_of_ne (by decide), feed_of_ne (by decide), _root_.mul_assoc]

/-- The value of the iterated product in the model, on equal inputs. -/
lemma model_bin5_const (c : ℕ → R) (u : R × R) :
    (modelAlg c).app _ (bin5 R) (fun _ => u) = u * u * u * u * u := by
  obtain ⟨e⟩ : Nonempty (Without (Fin 2) 0 ⊕ Fin 4 ≃ Fin 5) :=
    ⟨Fintype.equivFinOfCardEq card_W24⟩
  rw [isBin_bin5.eq ((isBin_m2.comp isBin_bin4 0).map e), alg_map, alg_comp, model_opGen,
    modelOps_two c _ rfl, Fin.prod_univ_two, feed_self, feed_of_ne (by decide)]
  exact congrArg (· * u) (model_bin4_const c u)

lemma wD_univ : wD (R := R) Finset.univ = fun _ => 1 :=
  funext fun x => wD_mem (Finset.mem_univ x)

lemma wD_empty : wD (R := R) ∅ = fun _ => uH :=
  funext fun x => wD_notMem (Finset.notMem_empty x)

lemma ev5_bin5_const (c : ℕ → R) (u : R × R) :
    ev5 c (fun _ => u) (bin5 R) = u.1 * u.1 * u.1 * u.1 * u.1 := by
  rw [ev5_apply, model_bin5_const, Prod.fst_mul, Prod.fst_mul, Prod.fst_mul, Prod.fst_mul]

lemma ev5_bq5_const (c : ℕ → R) (u : R × R) :
    ev5 c (fun _ => u) (bq5 R {0, 1, 2}) = c 3 * (hL R (u * u * u) * (hL R u * hL R u)) := by
  obtain ⟨E, hE⟩ := model_bq5 c (fun _ => u)
  rw [ev5_apply, hE, Fin.prod_univ_three, Prod.smul_fst, Prod.fst_one, smul_eq_mul, mul_one]

lemma ev5_eOp5 (c : ℕ → R) (w : Fin 5 → R × R) (e : Fin 5) :
    ev5 c w (eOp5 R e)
      = ((modelAlg c).app _ (pOp R 0 1) (fun t => w (eE e (Sum.inr t)))).1 * (w e).1 := by
  rw [ev5_apply, model_eOp5, Prod.fst_mul]

lemma ev5_eOp5_const (c : ℕ → R) (u : R × R) (e : Fin 5) :
    ev5 c (fun _ => u) (eOp5 R e) = c 3 * (hL R (u * u) * (hL R u * hL R u)) * u.1 := by
  rw [ev5_eOp5, model_pOp_const, Prod.smul_fst, Prod.fst_one, smul_eq_mul, mul_one]

/-- The value of `m₃(x_S) · x_d · x_e` on the inputs equal to `1` on `D`: `c₃` if `D` is the
complement of `S`, and zero otherwise. -/
lemma ev5_tt5 (c : ℕ → R) (D : Finset (Fin 5)) (S : Tri) :
    ev5 c (wD D) (tt5 R S.1) = if D = (S.1)ᶜ then c 3 else 0 := by
  obtain ⟨E, hE, hv⟩ := model_tt5 c (wD D) S
  have hin : ∀ b, E (Sum.inr b) ∈ S.1 := fun b => by
    rw [← hE]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ b)
  have hout : ∀ a, E (Sum.inl a) ∉ S.1 := fun a ha => by
    rw [← hE] at ha
    obtain ⟨b, -, hb⟩ := Finset.mem_image.1 ha
    exact Sum.inr_ne_inl (E.injective hb)
  have hprod : ∏ b, hL R (wD (R := R) D (E (Sum.inr b))) = if Disjoint S.1 D then 1 else 0 := by
    rw [← prod_hL_wD, ← hE,
      Finset.prod_image (fun a _ b _ h => Sum.inr_injective (E.injective h))]
  rw [ev5_apply, hv, Prod.fst_mul, Prod.fst_mul, Prod.smul_fst, Prod.fst_one, smul_eq_mul,
    mul_one, fst_wD, fst_wD, hprod]
  by_cases hD : D = (S.1)ᶜ
  · rw [if_pos hD, hD, if_pos disjoint_compl_right, if_pos (Finset.mem_compl.2 (hout _)),
      if_pos (Finset.mem_compl.2 (hout _)), mul_one, mul_one, mul_one]
  · rw [if_neg hD]
    by_cases hdis : Disjoint S.1 D
    · have hsub : D ⊆ (S.1)ᶜ := fun x hx =>
        Finset.mem_compl.2 fun hxS => Finset.disjoint_left.1 hdis hxS hx
      obtain ⟨y, hyS, hyD⟩ : ∃ y, y ∈ (S.1)ᶜ ∧ y ∉ D := by
        by_contra hcon
        exact hD (Finset.Subset.antisymm hsub fun y hy => by
          by_contra hyD
          exact hcon ⟨y, hy, hyD⟩)
      obtain ⟨z, rfl⟩ := E.surjective y
      rcases z with ⟨a, ha⟩ | b
      · have ha' : a = 1 ∨ a = 2 := by
          revert ha
          fin_cases a <;> simp
        rcases ha' with rfl | rfl
        · rw [if_neg hyD, mul_zero, zero_mul]
        · rw [if_neg hyD, mul_zero]
      · exact absurd (hin b) (Finset.mem_compl.1 hyS)
    · rw [if_neg hdis, mul_zero, zero_mul, zero_mul]

/-! ### The values on the inputs of the certificate -/

lemma ev5_bin5_univ (c : ℕ → R) : ev5 c (wD Finset.univ) (bin5 R) = 1 := by
  rw [wD_univ, ev5_bin5_const, Prod.fst_one, mul_one, mul_one, mul_one, mul_one]

lemma ev5_bq5_univ (c : ℕ → R) : ev5 c (wD Finset.univ) (bq5 R {0, 1, 2}) = 0 := by
  rw [wD_univ, ev5_bq5_const, hL_one, mul_zero, mul_zero, mul_zero]

lemma ev5_bq5_empty (c : ℕ → R) : ev5 c (wD ∅) (bq5 R {0, 1, 2}) = c 3 := by
  rw [wD_empty, ev5_bq5_const, uH_mul, uH_mul, hL_uH, mul_one, mul_one, mul_one]

lemma ev5_eOp5_univ (c : ℕ → R) (e : Fin 5) : ev5 c (wD Finset.univ) (eOp5 R e) = 0 := by
  rw [wD_univ, ev5_eOp5_const, hL_one, mul_zero, mul_zero, mul_zero, zero_mul]

lemma ev5_eOp5_empty (c : ℕ → R) (e : Fin 5) : ev5 c (wD ∅) (eOp5 R e) = 0 := by
  rw [wD_empty, ev5_eOp5_const]
  exact mul_zero _

lemma ev5_eOp5_single (c : ℕ → R) (e₀ e : Fin 5) :
    ev5 c (wD {e₀}) (eOp5 R e) = if e = e₀ then c 3 else 0 := by
  rw [ev5_eOp5, fst_wD]
  by_cases h : e = e₀
  · subst h
    have hw : (fun t => wD (R := R) {e} (eE e (Sum.inr t))) = fun _ => uH := funext fun t =>
      wD_notMem fun ht => Sum.inr_ne_inl
        ((eE e).injective ((Finset.mem_singleton.1 ht).trans (eE_outer e).symm))
    rw [hw, model_pOp_const, if_pos (Finset.mem_singleton_self e), if_pos rfl, uH_mul, hL_uH,
      mul_one, mul_one, mul_one, Prod.smul_fst, Prod.fst_one, smul_eq_mul, mul_one, mul_one]
  · rw [if_neg (fun hm => h (Finset.mem_singleton.1 hm)), if_neg h, mul_zero]

lemma ev5_tt5_of_card (c : ℕ → R) (D : Finset (Fin 5)) (S : Tri) (hD : D.card ≠ 2) :
    ev5 c (wD D) (tt5 R S.1) = 0 := by
  rw [ev5_tt5, if_neg]
  rintro rfl
  exact hD (by rw [Finset.card_compl, S.2, Fintype.card_fin])

lemma ev5_tt5_compl (c : ℕ → R) (S₀ S : Tri) :
    ev5 c (wD (S₀.1)ᶜ) (tt5 R S.1) = if S = S₀ then c 3 else 0 := by
  rw [ev5_tt5]
  by_cases h : S = S₀
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg fun hc => h (Subtype.ext (compl_injective hc).symm)]

lemma ev5_pOp5_empty (c : ℕ → R) : ev5 c (wD ∅) (pOp5 R {0, 1}) = c 4 := by
  rw [ev5_pOp5, prod_hL_wD, if_pos (Finset.disjoint_empty_right _), wD_empty, uH_mul, hL_uH,
    mul_one, mul_one]

lemma ev5_tOp5_empty (c : ℕ → R) (k : Fin 5) : ev5 c (wD ∅) (tOp5 R {k}ᶜ) = 0 := by
  rw [ev5_tOp5, fst_wD, if_neg (Finset.notMem_empty k), mul_zero]

lemma ev5_tOp5_single (c : ℕ → R) (k₀ k : Fin 5) :
    ev5 c (wD {k₀}) (tOp5 R {k}ᶜ) = if k = k₀ then c 4 else 0 := by
  rw [ev5_tOp5, prod_hL_wD, fst_wD]
  by_cases h : k = k₀
  · subst h
    rw [if_pos disjoint_compl_left, if_pos (Finset.mem_singleton_self k), if_pos rfl, mul_one,
      mul_one]
  · rw [if_neg (fun hm => h (Finset.mem_singleton.1 hm)), if_neg h, mul_zero]

lemma ev5_m5_empty (c : ℕ → R) : ev5 c (wD ∅) (opGen 5 (by norm_num)) = c 5 := by
  rw [ev5_m5, prod_hL_wD, if_pos (Finset.disjoint_empty_right _), mul_one]

/-- The scalars `1` in arity `m` and `0` in the other arities. -/
def cK (m : ℕ) : ℕ → R := fun n => if n = m then 1 else 0

lemma cK_self (m : ℕ) : cK (R := R) m m = 1 := if_pos rfl

lemma cK_of_ne {m n : ℕ} (h : n ≠ m) : cK (R := R) m n = 0 := if_neg h

lemma ev5_m5_cK {m : ℕ} (hm : 5 ≠ m) (w : Fin 5 → R × R) :
    ev5 (cK m) w (opGen 5 (by norm_num)) = 0 := by
  rw [ev5_m5, cK_of_ne hm, zero_mul]

lemma ev5_pOp5_cK {m : ℕ} (hm : 4 ≠ m) (w : Fin 5 → R × R) :
    ev5 (cK m) w (pOp5 R {0, 1}) = 0 := by
  rw [ev5_pOp5, cK_of_ne hm, zero_mul]

lemma ev5_tOp5_cK {m : ℕ} (hm : 4 ≠ m) (w : Fin 5 → R × R) (k : Fin 5) :
    ev5 (cK m) w (tOp5 R {k}ᶜ) = 0 := by
  rw [ev5_tOp5, cK_of_ne hm, zero_mul, zero_mul]

/-! ## The coefficients of a relation -/

lemma sum_basis34 (a : Fin 4 ⊕ (Tri ⊕ Tri) ⊕ (Fin 5 ⊕ Fin 5) → R)
    (F : HyperComOp R (Fin 5) →ₗ[R] R) :
    F (∑ i, a i • basis34 R i)
      = (a (Sum.inl 0) * F (bin5 R) + a (Sum.inl 1) * F (opGen 5 (by norm_num))
          + a (Sum.inl 2) * F (bq5 R {0, 1, 2}) + a (Sum.inl 3) * F (pOp5 R {0, 1}))
        + (((∑ S : Tri, a (Sum.inr (Sum.inl (Sum.inl S))) * F (tt5 R S.1))
            + ∑ S : Tri, a (Sum.inr (Sum.inl (Sum.inr S))) * F (qOp5 R S.1))
          + ((∑ e, a (Sum.inr (Sum.inr (Sum.inl e))) * F (eOp5 R e))
            + ∑ k, a (Sum.inr (Sum.inr (Sum.inr k))) * F (tOp5 R {k}ᶜ))) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type,
    Fin.sum_univ_four]
  simp only [map_add, map_sum, LinearMap.map_smul, smul_eq_mul, basis34, Sum.elim_inl,
    Sum.elim_inr]
  rfl

/-- **The coefficients of a relation between the thirty-four operations vanish, except those
of the operations `m₃(m₃(x_S), …)`**: the values in the algebra on `R × R`, with one of the
scalars `c₃`, `c₄`, `c₅` equal to `1` and the others to `0`, on inputs equal to `1` or
`(0, 1)`. -/
theorem coef_eq_zero {a : Fin 4 ⊕ (Tri ⊕ Tri) ⊕ (Fin 5 ⊕ Fin 5) → R}
    (h : ∑ i, a i • basis34 R i = 0) :
    (∀ i : Fin 4, a (Sum.inl i) = 0) ∧ (∀ S : Tri, a (Sum.inr (Sum.inl (Sum.inl S))) = 0) ∧
      (∀ e : Fin 5, a (Sum.inr (Sum.inr (Sum.inl e))) = 0) ∧
        ∀ k : Fin 5, a (Sum.inr (Sum.inr (Sum.inr k))) = 0 := by
  have key : ∀ (c : ℕ → R) (w : Fin 5 → R × R),
      (a (Sum.inl 0) * ev5 c w (bin5 R) + a (Sum.inl 1) * ev5 c w (opGen 5 (by norm_num))
          + a (Sum.inl 2) * ev5 c w (bq5 R {0, 1, 2}) + a (Sum.inl 3) * ev5 c w (pOp5 R {0, 1}))
        + (((∑ S : Tri, a (Sum.inr (Sum.inl (Sum.inl S))) * ev5 c w (tt5 R S.1))
            + ∑ S : Tri, a (Sum.inr (Sum.inl (Sum.inr S))) * ev5 c w (qOp5 R S.1))
          + ((∑ e, a (Sum.inr (Sum.inr (Sum.inl e))) * ev5 c w (eOp5 R e))
            + ∑ k, a (Sum.inr (Sum.inr (Sum.inr k))) * ev5 c w (tOp5 R {k}ᶜ))) = 0 :=
    fun c w => by
      have hk := congrArg (ev5 c w) h
      rwa [sum_basis34, map_zero] at hk
  have n53 : (5 : ℕ) ≠ 3 := by norm_num
  have n43 : (4 : ℕ) ≠ 3 := by norm_num
  have n54 : (5 : ℕ) ≠ 4 := by norm_num
  have n45 : (4 : ℕ) ≠ 5 := by norm_num
  have cu : (Finset.univ : Finset (Fin 5)).card ≠ 2 := by decide
  have ce : (∅ : Finset (Fin 5)).card ≠ 2 := by decide
  have cs : ∀ e : Fin 5, ({e} : Finset (Fin 5)).card ≠ 2 := fun e => by
    rw [Finset.card_singleton]
    decide
  have h0 : a (Sum.inl 0) = 0 := by
    have := key (cK 3) (wD Finset.univ)
    simpa only [ev5_bin5_univ, ev5_m5_cK n53, ev5_bq5_univ, ev5_pOp5_cK n43,
      ev5_tt5_of_card _ _ _ cu, ev5_qOp5, ev5_eOp5_univ, ev5_tOp5_cK n43, mul_zero, mul_one,
      Finset.sum_const_zero, add_zero] using this
  have h2 : a (Sum.inl 2) = 0 := by
    have := key (cK 3) (wD ∅)
    simpa only [h0, zero_mul, ev5_m5_cK n53, ev5_bq5_empty, cK_self, ev5_pOp5_cK n43,
      ev5_tt5_of_card _ _ _ ce, ev5_qOp5, ev5_eOp5_empty, ev5_tOp5_cK n43, mul_zero, mul_one,
      Finset.sum_const_zero, add_zero, zero_add] using this
  have hee : ∀ e : Fin 5, a (Sum.inr (Sum.inr (Sum.inl e))) = 0 := fun e₀ => by
    have := key (cK 3) (wD {e₀})
    simpa only [h0, h2, zero_mul, ev5_m5_cK n53, ev5_pOp5_cK n43, ev5_tt5_of_card _ _ _ (cs e₀),
      ev5_qOp5, ev5_eOp5_single, cK_self, ev5_tOp5_cK n43, mul_zero, mul_one,
      Finset.sum_const_zero, add_zero, zero_add, mul_ite, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] using this
  have htt : ∀ S : Tri, a (Sum.inr (Sum.inl (Sum.inl S))) = 0 := fun S₀ => by
    have := key (cK 3) (wD (S₀.1)ᶜ)
    simpa only [h0, h2, hee, zero_mul, ev5_m5_cK n53, ev5_pOp5_cK n43, ev5_tt5_compl, cK_self,
      ev5_qOp5, ev5_tOp5_cK n43, mul_zero, mul_one, Finset.sum_const_zero, add_zero, zero_add,
      mul_ite, Finset.sum_ite_eq', Finset.mem_univ, if_true] using this
  have h3 : a (Sum.inl 3) = 0 := by
    have := key (cK 4) (wD ∅)
    simpa only [h0, h2, hee, htt, zero_mul, ev5_m5_cK n54, ev5_pOp5_empty, cK_self, ev5_qOp5,
      ev5_tOp5_empty, mul_zero, mul_one, Finset.sum_const_zero, add_zero, zero_add] using this
  have ht5 : ∀ k : Fin 5, a (Sum.inr (Sum.inr (Sum.inr k))) = 0 := fun k₀ => by
    have := key (cK 4) (wD {k₀})
    simpa only [h0, h2, h3, hee, htt, zero_mul, ev5_m5_cK n54, ev5_qOp5, ev5_tOp5_single,
      cK_self, mul_zero, mul_one, Finset.sum_const_zero, add_zero, zero_add, mul_ite,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] using this
  have h1 : a (Sum.inl 1) = 0 := by
    have := key (cK 5) (wD ∅)
    simpa only [h0, h2, h3, hee, htt, ht5, zero_mul, ev5_m5_empty, cK_self, ev5_qOp5, mul_zero,
      mul_one, Finset.sum_const_zero, add_zero, zero_add] using this
  refine ⟨fun i => ?_, htt, hee, ht5⟩
  fin_cases i
  exacts [h0, h1, h2, h3]

/-! ## The values in the algebra on `R[x]/(x³)` -/

/-- The algebra structure of the model on `R[x]/(x³)`. -/
noncomputable abbrev cubAlg : SymAlgebra R (HyperComOp R) (Cub R) :=
  (HyperComOp.algebraEquiv R (Cub R)).symm HCAlg.cub

lemma cub_wTerm {n : ℕ} (S : Finset (Fin n)) (w : Fin n → Cub R) :
    (cubAlg (R := R)).app (Fin n) ((I).proj _ (wTerm (R := R) S)) w
      = wVal (Cub R) (cubOps R) S w :=
  hcHom_wTerm (cubOps R) S w

/-- The class of `x`. -/
def zC : Cub R := ⟨0, 1, 0⟩

/-- The inputs equal to `x` on `D` and to `x²` elsewhere. -/
def vD (D : Finset (Fin 5)) : Fin 5 → Cub R := fun x => if x ∈ D then zC else ⟨0, 0, 1⟩

lemma sh_vD (D : Finset (Fin 5)) (x : Fin 5) :
    Cub.sh R (vD (R := R) D x) = if x ∈ D then 1 else zC := by
  unfold vD
  split_ifs <;> rfl

lemma prod_sh_vD (D T : Finset (Fin 5)) :
    ∏ x ∈ T, Cub.sh R (vD (R := R) D x) = zC ^ (T.filter fun x => x ∉ D).card := by
  simp only [sh_vD]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]

lemma zC_pow_two : (zC : Cub R) ^ 2 = ⟨0, 0, 1⟩ := by
  rw [pow_two]
  ext <;> simp [zC]

lemma zC_pow_three : (zC : Cub R) ^ 3 = 0 := by
  rw [pow_succ, zC_pow_two]
  ext <;> simp [zC]

/-- **The constant coefficient of the value in the model**, a linear functional on the
operations of arity five. -/
noncomputable def evA (w : Fin 5 → Cub R) : HyperComOp R (Fin 5) →ₗ[R] R where
  toFun x := ((cubAlg (R := R)).app (Fin 5) x w).a
  map_add' x y := by rw [map_add, MultilinearMap.add_apply, Cub.add_a]
  map_smul' s x := by
    rw [map_smul, MultilinearMap.smul_apply, Cub.smul_a, RingHom.id_apply, smul_eq_mul]

lemma card_filter_pair : ∀ S D : Finset (Fin 5), S.card = 3 → D.card = 2 →
    (S.filter fun x => x ∉ D).card = 3 - (S ∩ D).card ∧
      (Sᶜ.filter fun x => x ∉ D).card = (S ∩ D).card ∧ (S ∩ D).card ≤ 2 := by
  decide

/-- **The value of `m₃(m₃(x_S), …)` on the inputs equal to `x` on a pair `D` and to `x²`
elsewhere** has the constant coefficient `1` if `S` contains exactly one input of `D`, and `0`
otherwise. -/
lemma evA_qOp5 (D : Finset (Fin 5)) (hD : D.card = 2) (S : Tri) :
    evA (vD D) (qOp5 R S.1) = if (S.1 ∩ D).card = 1 then 1 else 0 := by
  have hc : (S.1)ᶜ.card = 2 := by rw [Finset.card_compl, S.2, Fintype.card_fin]
  obtain ⟨h1, h2, h3⟩ := card_filter_pair S.1 D S.2 hD
  show ((cubAlg (R := R)).app (Fin 5) (qOp5 R S.1) (vD D)).a = _
  rw [qOp5_eq, cub_wTerm, wVal_cub, S.2, hc, if_pos ⟨by omega, by omega⟩, prod_sh_vD,
    prod_sh_vD, h1, h2]
  show (Cub.sh R (Cub.sh R (Cub.sh R (zC ^ (3 - (S.1 ∩ D).card))) * zC ^ (S.1 ∩ D).card)).a = _
  obtain h | h | h : (S.1 ∩ D).card = 0 ∨ (S.1 ∩ D).card = 1 ∨ (S.1 ∩ D).card = 2 := by omega
  · rw [h, if_neg (by norm_num), zC_pow_three]
    simp
  · rw [h, if_pos rfl, show 3 - 1 = 2 from rfl, zC_pow_two, pow_one]
    simp [zC]
  · rw [h, if_neg (by norm_num), show 3 - 2 = 1 from rfl, pow_one, zC_pow_two]
    simp [zC]

/-! ## The ten operations `m₃(m₃(x_S), …)` -/

/-- The coefficients of the certificate: for a pair `D` and a triple `S₀`. -/
def kap5 (D S₀ : Finset (Fin 5)) : ℤ :=
  3 * (if (S₀ ∩ D).card = 1 then 1 else 0) + 3 * (if D = S₀ᶜ then 1 else 0) - 2

/-- **The certificate**: the matrix of the triples and the pairs meeting in one input has an
inverse up to the factor `6`. -/
lemma cert5 : ∀ S S₀ : Finset (Fin 5), S.card = 3 → S₀.card = 3 →
    ∑ D ∈ (Finset.univ.filter fun D : Finset (Fin 5) => D.card = 2),
        kap5 D S₀ * (if (S ∩ D).card = 1 then 1 else 0)
      = if S = S₀ then 6 else 0 := by
  decide

/-- **A family on the triples whose sums over the triples meeting a pair in one input vanish is
zero**, over a field in which `2` and `3` are invertible. -/
theorem tri_eq_zero {K : Type u} [Field K] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {b : Tri → K}
    (hb : ∀ D : Finset (Fin 5), D.card = 2 →
      ∑ S : Tri, b S * (if (S.1 ∩ D).card = 1 then 1 else 0) = 0) (S₀ : Tri) : b S₀ = 0 := by
  have h6 : (6 : K) ≠ 0 := by
    have h : (6 : K) = 2 * 3 := by norm_num
    rw [h]
    exact mul_ne_zero h2 h3
  have e1 : ∀ S : Tri, (if S = S₀ then (6 : K) else 0)
      = ∑ D ∈ (Finset.univ.filter fun D : Finset (Fin 5) => D.card = 2),
          (kap5 D S₀.1 : K) * (if (S.1 ∩ D).card = 1 then 1 else 0) := fun S => by
    have h := congrArg (Int.cast : ℤ → K) (cert5 S.1 S₀.1 S.2 S₀.2)
    push_cast at h
    rw [h]
    simp only [Subtype.ext_iff]
  have hsum : ∑ S : Tri, b S * (if S = S₀ then (6 : K) else 0) = b S₀ * 6 := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have key : b S₀ * 6 = 0 := by
    rw [← hsum]
    have h : ∀ S : Tri, b S * (if S = S₀ then (6 : K) else 0)
        = ∑ D ∈ (Finset.univ.filter fun D : Finset (Fin 5) => D.card = 2),
            (kap5 D S₀.1 : K) * (b S * (if (S.1 ∩ D).card = 1 then 1 else 0)) := fun S => by
      rw [e1 S, Finset.mul_sum]
      exact Finset.sum_congr rfl fun D _ => by ring
    rw [Finset.sum_congr rfl fun S _ => h S, Finset.sum_comm]
    refine Finset.sum_eq_zero fun D hD => ?_
    rw [← Finset.mul_sum, hb D (Finset.mem_filter.1 hD).2, mul_zero]
  exact (mul_eq_zero.1 key).resolve_right h6

/-! ## The dimension -/

section Dim

variable (K : Type u) [Field K]

/-- **The thirty-four operations of arity five are linearly independent**, over a field in
which `2` and `3` are invertible: the algebra on `K × K` separates all but the ten operations
`m₃(m₃(x_S), …)`, and the algebra on `K[x]/(x³)` separates those. -/
theorem linearIndependent_basis34 (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    LinearIndependent K (basis34 K) := by
  rw [Fintype.linearIndependent_iff]
  intro a h
  obtain ⟨h4, htt, hee, ht5⟩ := coef_eq_zero h
  have hqq : ∀ S : Tri, a (Sum.inr (Sum.inl (Sum.inr S))) = 0 :=
    tri_eq_zero h2 h3 fun D hD => by
      have hk := congrArg (evA (vD D)) h
      rw [sum_basis34, map_zero] at hk
      simpa only [h4, htt, hee, ht5, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
        evA_qOp5 D hD] using hk
  rintro (i | (S | S) | (e | k))
  exacts [h4 i, htt S, hqq S, hee e, ht5 k]

lemma card_Tri : Fintype.card Tri = 10 := by decide

/-- **`dim HyperCom(5) = 34`**, on the inputs `Fin 5`, over a field in which `2` and `3` are
invertible. -/
theorem finrank_fin_five (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    Module.finrank K (HyperComOp K (Fin 5)) = 34 := by
  rw [← finrank_top, ← span_basis34 (R := K),
    finrank_span_eq_card (linearIndependent_basis34 K h2 h3), Fintype.card_sum,
    Fintype.card_sum, Fintype.card_sum, Fintype.card_sum, card_Tri, Fintype.card_fin,
    Fintype.card_fin]

variable {K}

/-- **The hypercommutative operad has thirty-four operations of arity five**, over a field in
which `2` and `3` are invertible. -/
theorem finrank_five {A : Type} [Fintype A] [DecidableEq A] (h2 : (2 : K) ≠ 0)
    (h3 : (3 : K) ≠ 0) (hA : Fintype.card A = 5) :
    Module.finrank K (HyperComOp K A) = 34 := by
  rw [← (SymOperad.mapEquiv (R := K) (P := HyperComOp K)
    (Fintype.equivFinOfCardEq hA).symm).finrank_eq, finrank_fin_five K h2 h3]

end Dim

end HyperCom

end Operad
