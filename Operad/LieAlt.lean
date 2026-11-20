/-
# The Koszul dual cooperad of `Lie` in the signed linear orders: the alternating line

Over a field `K` of characteristic zero, the image of `Lie^¡` in the cooperad of signed linear
orders (`LieDual.toOrd`) is, on `n + 1` inputs, the line of the alternating sum of the linear
orders (`LieDual.alt`).

* In arity two the image is antisymmetric (`LieDual.coef_ord2_swap`): the generators of `Lie`
  are the antisymmetric functions.
* Decomposing at a window of two inputs, the coefficients of the two orders of the window are
  opposite (`LieDual.coef_comp_swap`). Hence exchanging two adjacent inputs of an order changes
  the sign of its coefficient (`LieDual.coef_swap`), and **the coefficients alternate**
  (`LieDual.coef_perm`), the exchanges of two adjacent inputs generating the permutations.
* **The image lies on the alternating line** (`LieDual.toOrd_eq`), and **`Lie^¡` contains the
  alternating sum** (`LieDual.exists_nu`): `Lie^¡` is nonzero on `n + 1` inputs, by
  `LieDual.finrank_dual_lie` for `n ≥ 1` and by the coaugmentation for `n = 0`. The generator
  `LieDual.nu K n` is the element whose image is the alternating sum (`LieDual.toOrd_nu`).
-/
import Operad.LieDual
import Operad.OrdTwisting

universe u

namespace Operad

open Sym GerBV
open scoped TensorProduct

namespace LieDual

open SymPresComLie

variable {K : Type u} [Field K] [CharZero K]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-! ## Coefficients -/

/-- **The coefficient of a linear order** in the image of an element of `Lie^¡`. -/
noncomputable def coef (x : Koszul.Dual K (ELie K) (rLie K) A) (L : NOrd A) : K :=
  (show NOrd A →₀ K from (toOrd K).app A x) L

lemma coef_map (e : A ≃ B) (x : Koszul.Dual K (ELie K) (rLie K) A) (L : NOrd B) :
    coef (SymSpecies.map (R := K) e x) L = coef x (SetOperad.map e.symm L) := by
  show (show NOrd B →₀ K from (toOrd K).app B (SymSpecies.map (R := K) e x)) L = _
  rw [(toOrd K).app_map]
  exact Lin.mapL_apply e _ L

/-- **In arity two the image of `Lie^¡` is antisymmetric.** -/
lemma coef_ord2_swap (x : Koszul.Dual K (ELie K) (rLie K) A) (τ : Fin 2 ≃ A) :
    coef x (OrdCo.ord2 ((Equiv.swap 0 1).trans τ)) = -coef x (OrdCo.ord2 τ) := by
  set f : ELie K A := FreeGrL.genCoef K (GrSpecies.Shift (ELie K) K) A
    ((Koszul.dualSub K (ELie K) (rLie K)).incl A x) with hf
  have h1 : (OrdCo.gen K).app A ((toOrd K).app A x) = (jLie K).app A f := by
    rw [← OrdCo.genCoef_toCut, ← OrdCo.incl_toDual, toDual_toOrd]
    exact FreeGrL.genCoef_mapSp (Koszul.shiftHom (jLie K)) _
  have h2 : ∀ ρ : Fin 2 ≃ A, coef x (OrdCo.ord2 ρ) = f.1 ρ.symm := fun ρ =>
    congrFun (congrArg (fun g : SymPresB.Reg2 K A => (g : (Fin 2 ≃ A) → K)) h1) ρ
  rw [h2, h2]
  exact f.2 τ.symm

omit [CharZero K] in
/-- A coefficient identity on the second factor passes to the tensors in the image. -/
lemma tens_map_neg {M N X Y : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] (X →₀ K)) (g : N →ₗ[K] (Y →₀ K)) (p : X) (q q' : Y)
    (hg : ∀ x, g x q' = -g x q) (t : M ⊗[K] N) {T : (X →₀ K) ⊗[K] (Y →₀ K)}
    (hT : T = TensorProduct.map f g t) : tens K X Y T (p, q') = -tens K X Y T (p, q) := by
  subst hT
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul u x =>
    rw [TensorProduct.map_tmul, tens_tmul_apply, tens_tmul_apply, hg]
    ring
  | add s t hs ht =>
    rw [map_add, map_add, Finsupp.add_apply, Finsupp.add_apply, hs, ht]
    ring

/-- **The coefficients of a composite with the two orders on two inputs are opposite.** -/
lemma coef_comp_swap (i : A) (z : Koszul.Dual K (ELie K) (rLie K) (Without A i ⊕ B))
    (p : NOrd A) (τ : Fin 2 ≃ B) :
    coef z (SetOperad.comp i p (OrdCo.ord2 ((Equiv.swap 0 1).trans τ)))
      = -coef z (SetOperad.comp i p (OrdCo.ord2 τ)) := by
  have h1' := (toOrd K).decomp_app (B := B) i
  have h1 := LinearMap.congr_fun h1' z
  obtain ⟨w, hw⟩ : ∃ w : NOrd (Without A i ⊕ B) →₀ K, w = (toOrd K).app (Without A i ⊕ B) z :=
    ⟨_, rfl⟩
  have key := tens_map_neg ((toOrd K).app A) ((toOrd K).app B) p (OrdCo.ord2 τ)
    (OrdCo.ord2 ((Equiv.swap 0 1).trans τ)) (fun x => coef_ord2_swap x τ)
    (GrCooperad.decomp (R := K) (C := Koszul.Dual K (ELie K) (rLie K)) (B := B) i z)
    (T := SgnLin.decompT K NOrd.sgnD i w) (by rw [hw]; exact h1)
  have e1 := SgnLin.decompT_apply (R := K) (δ := NOrd.sgnD) i w (p, OrdCo.ord2 τ)
  have e2 := SgnLin.decompT_apply (R := K) (δ := NOrd.sgnD) i w
    (p, OrdCo.ord2 ((Equiv.swap 0 1).trans τ))
  have hs : SgnData.sgn i (NOrd.sgnD.app A p)
        (NOrd.sgnD.app B (OrdCo.ord2 ((Equiv.swap 0 1).trans τ)))
      = SgnData.sgn i (NOrd.sgnD.app A p) (NOrd.sgnD.app B (OrdCo.ord2 τ)) := rfl
  rw [hs] at e2
  have h3 : σ K (SgnData.sgn i (NOrd.sgnD.app A p) (NOrd.sgnD.app B (OrdCo.ord2 τ)))
      * (w (SetOperad.comp i p (OrdCo.ord2 τ))
        + w (SetOperad.comp i p (OrdCo.ord2 ((Equiv.swap 0 1).trans τ)))) = 0 := by
    rw [mul_add]
    exact (congrArg₂ (· + ·) e1 e2).symm.trans (add_eq_zero_iff_neg_eq.2 key.symm)
  have h4 := (mul_eq_zero.1 h3).resolve_left (OrdCo.σ_ne_zero K _)
  show (show NOrd (Without A i ⊕ B) →₀ K from (toOrd K).app (Without A i ⊕ B) z) _
    = -(show NOrd (Without A i ⊕ B) →₀ K from (toOrd K).app (Without A i ⊕ B) z) _
  rw [← hw]
  exact eq_neg_of_add_eq_zero_right h4

/-! ## Exchanging two adjacent inputs -/

/-- The exchange of the two inserted inputs of a composite of standard orders is the exchange of
two adjacent positions. -/
lemma posEquivF_swap {n : ℕ} (k : Fin n) :
    ((posEquivF k 2 (n + 1) rfl).symm.trans
        (compEquiv (Equiv.refl (Fin n)) (Equiv.swap (0 : Fin 2) 1) k)).trans
          (posEquivF k 2 (n + 1) rfl)
      = Equiv.swap k.castSucc k.succ := by
  refine Equiv.ext fun x => ?_
  obtain ⟨u, rfl⟩ := (posEquivF k 2 (n + 1) rfl).surjective x
  show posEquivF k 2 (n + 1) rfl (compEquiv (Equiv.refl (Fin n)) (Equiv.swap (0 : Fin 2) 1) k
    ((posEquivF k 2 (n + 1) rfl).symm (posEquivF k 2 (n + 1) rfl u))) = _
  rw [Equiv.symm_apply_apply]
  have e0 : posEquivF k 2 (n + 1) rfl (Sum.inr 0) = k.castSucc :=
    Fin.ext (by rw [posEquivF_inr]; simp)
  have e1 : posEquivF k 2 (n + 1) rfl (Sum.inr 1) = k.succ :=
    Fin.ext (by rw [posEquivF_inr]; simp)
  rcases u with a | j
  · show posEquivF k 2 (n + 1) rfl (Sum.inl a) = _
    have hak : (a.1 : ℕ) ≠ k := fun h => a.2 (Fin.ext h)
    rw [Equiv.swap_apply_of_ne_of_ne]
    · intro he
      have h1 := congrArg Fin.val he
      rw [Fin.val_castSucc] at h1
      rcases Nat.lt_or_gt_of_ne hak with h | h
      · have h2 := posEquivF_inl_of_lt (l := 2) (m := n + 1) k rfl a h
        omega
      · have h2 := posEquivF_inl_of_gt (l := 2) (m := n + 1) k rfl a h
        omega
    · intro he
      have h1 := congrArg Fin.val he
      rw [Fin.val_succ] at h1
      rcases Nat.lt_or_gt_of_ne hak with h | h
      · have h2 := posEquivF_inl_of_lt (l := 2) (m := n + 1) k rfl a h
        omega
      · have h2 := posEquivF_inl_of_gt (l := 2) (m := n + 1) k rfl a h
        omega
  · show posEquivF k 2 (n + 1) rfl (Sum.inr (Equiv.swap (0 : Fin 2) 1 j)) = _
    obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    · rw [Equiv.swap_apply_left, e0, e1, Equiv.swap_apply_left]
    · rw [Equiv.swap_apply_right, e0, e1, Equiv.swap_apply_right]

/-- **Exchanging two adjacent inputs of an order changes the sign of its coefficient.** -/
lemma coef_swap {n : ℕ} (y : Koszul.Dual K (ELie K) (rLie K) (Fin (n + 1)))
    (π : Equiv.Perm (Fin (n + 1))) (k : Fin n) :
    coef y (SetOperad.map (π * Equiv.swap k.castSucc k.succ) (OrdCo.sd n))
      = -coef y (SetOperad.map π (OrdCo.sd n)) := by
  have hn : 0 < n := k.pos
  obtain ⟨E, hE⟩ : ∃ E, E = posEquivF k 2 (n + 1) rfl := ⟨_, rfl⟩
  have hstd : SetOperad.map E (SetOperad.comp k (NOrd.std n hn) (NOrd.std 2 (by decide)))
      = OrdCo.sd n := by
    rw [hE]
    exact Subtype.ext (map_posEquivF (l := 2) (m := n + 1) k rfl)
  have h := coef_comp_swap k (SymSpecies.map (R := K) (E.trans π).symm y) (NOrd.std n hn)
    (Equiv.refl (Fin 2))
  rw [coef_map, coef_map, Equiv.symm_symm] at h
  have hX : SetOperad.comp k (NOrd.std n hn) (NOrd.std 2 (by decide))
      = SetOperad.map E.symm (OrdCo.sd n) := by
    rw [← hstd, ← SetOperad.map_trans, Equiv.self_trans_symm, SetOperad.map_refl]
  have h1 : SetOperad.map (E.trans π)
        (SetOperad.comp k (NOrd.std n hn) (OrdCo.ord2 (Equiv.refl (Fin 2))))
      = SetOperad.map π (OrdCo.sd n) := by
    rw [OrdCo.ord2, SetOperad.map_refl, SetOperad.map_trans, hstd]
  have hc : SetOperad.comp k (NOrd.std n hn)
        (SetOperad.map (Equiv.swap (0 : Fin 2) 1) (NOrd.std 2 (by decide)))
      = SetOperad.map (compEquiv (Equiv.refl (Fin n)) (Equiv.swap (0 : Fin 2) 1) k)
        (SetOperad.comp k (NOrd.std n hn) (NOrd.std 2 (by decide))) := by
    have h0 := SetOperad.map_comp (S := NOrd) (Equiv.refl (Fin n)) (Equiv.swap (0 : Fin 2) 1) k
      (NOrd.std n hn) (NOrd.std 2 (by decide))
    rw [SetOperad.map_refl] at h0
    exact h0.symm
  have hp : ((E.symm.trans (compEquiv (Equiv.refl (Fin n)) (Equiv.swap (0 : Fin 2) 1) k)).trans
      (E.trans π)) = π * Equiv.swap k.castSucc k.succ := by
    subst hE
    exact Equiv.ext fun x => congrArg π (Equiv.congr_fun (posEquivF_swap k) x)
  have h2 : SetOperad.map (E.trans π) (SetOperad.comp k (NOrd.std n hn)
        (OrdCo.ord2 ((Equiv.swap 0 1).trans (Equiv.refl (Fin 2)))))
      = SetOperad.map (π * Equiv.swap k.castSucc k.succ) (OrdCo.sd n) := by
    rw [OrdCo.ord2, Equiv.trans_refl, hc, hX, ← SetOperad.map_trans]
    exact (SetOperad.map_trans
      (E.symm.trans (compEquiv (Equiv.refl (Fin n)) (Equiv.swap (0 : Fin 2) 1) k)) (E.trans π)
      (OrdCo.sd n)).symm.trans (congrArg (fun e => SetOperad.map e (OrdCo.sd n)) hp)
  rw [h1, h2] at h
  exact h

/-- **The coefficients of an element of `Lie^¡` alternate.** -/
theorem coef_perm {n : ℕ} (y : Koszul.Dual K (ELie K) (rLie K) (Fin (n + 1)))
    (τ π : Equiv.Perm (Fin (n + 1))) :
    coef y (SetOperad.map (π * τ) (OrdCo.sd n))
      = ((Equiv.Perm.sign τ : ℤ) : K) * coef y (SetOperad.map π (OrdCo.sd n)) := by
  have hτ : τ ∈ Submonoid.closure
      (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    exact Submonoid.mem_top _
  induction hτ using Submonoid.closure_induction generalizing π with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    have hne : k.castSucc ≠ k.succ := fun h => by
      have := congrArg Fin.val h
      simp at this
    rw [coef_swap, Equiv.Perm.sign_swap hne]
    simp
  | one => simp
  | mul a b _ _ ha hb =>
    rw [← mul_assoc, hb, ha, Equiv.Perm.sign_mul]
    push_cast
    ring

/-! ## The alternating line -/

variable (K) in
/-- **The alternating sum of the linear orders** on `n + 1` inputs. -/
noncomputable def alt (n : ℕ) : OrdCo K (Fin (n + 1)) :=
  ∑ τ : Equiv.Perm (Fin (n + 1)),
    ((Equiv.Perm.sign τ : ℤ) : K) • SgnLin.bas NOrd.sgnD K (SetOperad.map τ (OrdCo.sd n))

omit [CharZero K] in
/-- The coefficients of the alternating sum are the signs. -/
lemma alt_apply (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    (show NOrd (Fin (n + 1)) →₀ K from alt K n) (SetOperad.map π (OrdCo.sd n))
      = ((Equiv.Perm.sign π : ℤ) : K) := by
  classical
  show Finsupp.lapply (R := K) (M := K) (SetOperad.map π (OrdCo.sd n))
    (∑ τ : Equiv.Perm (Fin (n + 1)), ((Equiv.Perm.sign τ : ℤ) : K) •
      (Finsupp.single (SetOperad.map τ (OrdCo.sd n)) (1 : K) : NOrd (Fin (n + 1)) →₀ K)) = _
  rw [_root_.map_sum, Finset.sum_eq_single π]
  · rw [LinearMap.map_smul, Finsupp.lapply_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  · intro τ _ hτ
    rw [LinearMap.map_smul, Finsupp.lapply_apply, Finsupp.single_eq_of_ne, smul_zero]
    exact fun h => hτ (LinOrd.eq_of_map_eq (congrArg Subtype.val h).symm)
  · exact fun h => absurd (Finset.mem_univ π) h

/-- **The image of `Lie^¡` in the signed linear orders lies on the alternating line.** -/
theorem toOrd_eq {n : ℕ} (y : Koszul.Dual K (ELie K) (rLie K) (Fin (n + 1))) :
    (toOrd K).app (Fin (n + 1)) y = coef y (OrdCo.sd n) • alt K n := by
  refine (Finsupp.ext fun L => ?_ :
    (show NOrd (Fin (n + 1)) →₀ K from (toOrd K).app (Fin (n + 1)) y)
      = (show NOrd (Fin (n + 1)) →₀ K from coef y (OrdCo.sd n) • alt K n))
  obtain ⟨π, rfl⟩ : ∃ π : Equiv.Perm (Fin (n + 1)), SetOperad.map π (OrdCo.sd n) = L := by
    obtain ⟨e, he⟩ := LinOrd.exists_map_eq (LinOrd.std (n + 1)) L.1 rfl
    exact ⟨e, Subtype.ext he⟩
  show coef y (SetOperad.map π (OrdCo.sd n)) = coef y (OrdCo.sd n)
    * (show NOrd (Fin (n + 1)) →₀ K from alt K n) (SetOperad.map π (OrdCo.sd n))
  rw [alt_apply, mul_comm]
  have h := coef_perm y π 1
  rw [one_mul] at h
  rw [h]
  exact congrArg (fun L => _ * coef y L) (SetOperad.map_refl _)

variable (K) in
/-- **`Lie^¡` contains the alternating sum.** -/
theorem exists_nu (n : ℕ) : ∃ ν : Koszul.Dual K (ELie K) (rLie K) (Fin (n + 1)),
    (toOrd K).app (Fin (n + 1)) ν = alt K n := by
  obtain ⟨y, hy⟩ : ∃ y : Koszul.Dual K (ELie K) (rLie K) (Fin (n + 1)), y ≠ 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨SymSpecies.map (R := K) (Equiv.ofUnique Unit (Fin 1))
        (GrCooperad.Coaug.one (R := K) (C := Koszul.Dual K (ELie K) (rLie K))), fun h => ?_⟩
      have h1 := congrArg (SymSpecies.map (R := K) (Equiv.ofUnique Unit (Fin 1)).symm) h
      rw [← SymSpecies.map_trans, Equiv.self_trans_symm, SymSpecies.map_refl, map_zero] at h1
      have h2 := GrCooperad.Coaug.counit_one (R := K) (C := Koszul.Dual K (ELie K) (rLie K))
      rw [h1, map_zero] at h2
      exact zero_ne_one h2
    · haveI : Nontrivial (Koszul.Dual K (ELie K) (rLie K) (Fin (n + 1))) :=
        Module.nontrivial_of_finrank_pos (R := K)
          (by rw [finrank_dual_lie K (by omega)]; exact one_pos)
      exact exists_ne 0
  have hc : coef y (OrdCo.sd n) ≠ 0 := fun h =>
    hy (toOrd_injective K (Fin (n + 1)) ((toOrd_eq y).trans (by
      rw [h, zero_smul]
      exact (LinearMap.map_zero ((toOrd K).app (Fin (n + 1)))).symm)))
  refine ⟨(coef y (OrdCo.sd n))⁻¹ • y, ?_⟩
  rw [LinearMap.map_smul, toOrd_eq, smul_smul, inv_mul_cancel₀ hc, one_smul]

variable (K) in
/-- **The generator of `Lie^¡`** on `n + 1` inputs: the element whose image is the alternating
sum of the linear orders. -/
noncomputable def nu (n : ℕ) : Koszul.Dual K (ELie K) (rLie K) (Fin (n + 1)) :=
  Classical.choose (exists_nu K n)

lemma toOrd_nu (n : ℕ) : (toOrd K).app (Fin (n + 1)) (nu K n) = alt K n :=
  Classical.choose_spec (exists_nu K n)

end LieDual

end Operad
