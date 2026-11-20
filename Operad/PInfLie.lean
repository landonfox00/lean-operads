/-
# `Lie∞`-algebras: Koszul signs, unshuffles and the generalized Jacobi expressions

The computations in the endomorphism operad of a super module `V` over a field `K` behind
`PInfLie.pinfEquiv` (`Operad/PInfLieEquiv.lean`).

* **The Koszul sign of a permutation of the inputs** (`PInfLie.ks`), for a tuple of parities:
  the product of the signs of the pairs of inputs it exchanges, an instance of `GrEnd.rsg`. It
  is a cocycle (`PInfLie.ks_mul`), and on the exchange of two adjacent inputs it is the sign of
  their two parities (`PInfLie.ks_swap`).
* **Relabelling and décalage** (`PInfLie.dec_sv_map`): on homogeneous inputs, the décalage of an
  operation relabelled by a permutation `τ`, with the sign of `τ`, is the décalage at the
  permuted inputs with the Koszul sign of `τ` for the shifted parities. Proved for the exchanges
  of two adjacent inputs (`PInfLie.dec_sv_swap`) and extended by the cocycle property.
* **An operation alternates iff its décalage is graded symmetric** for the shifted parities
  (`PInfLie.dec_symm`, `PInfLie.map_of_dec_symm`).
* **Unshuffles** (`PInfLie.unsh`): the permutation listing the inputs of a subset in increasing
  order, then the others in increasing order. Its Koszul sign is `LInf.usgn`
  (`PInfLie.ks_unsh`).
* **The terms of the generalized Jacobi expression** (`PInfLie.dec_sv_term`,
  `PInfLie.dec_sv_sum`): for an odd invariant family `γ` on the signed linear orders, the
  décalage of the sum over the nonempty subsets `S` of the planar terms at the initial windows,
  moved to `S` by the unshuffles with their signs, is `LInf.jac` of the operations of `γ` in the
  bar convention (`PInfLie.lfam`), on homogeneous inputs.
-/
import Operad.LieTwisting
import Operad.PInfAssEquiv
import Operad.LInfinity

universe u v

namespace Operad

open Sym GerBV GrEnd
open scoped TensorProduct

namespace PInfLie

open OrdCo PInfAss

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V] [SuperMod K V]

/-! ## The Koszul sign of a permutation -/

variable (K) in
/-- **The Koszul sign of a permutation of the inputs**, for the parities `p`: the product of the
signs of the pairs of inputs it exchanges. -/
noncomputable def ks (N : ℕ) (τ : Equiv.Perm (Fin N)) (p : Fin N → Bool) : K :=
  rsg K (LinOrd.map τ (LinOrd.std N)) (LinOrd.std N) p

lemma ks_one (N : ℕ) (p : Fin N → Bool) : ks K N 1 p = 1 := by
  have h : LinOrd.map (1 : Equiv.Perm (Fin N)) (LinOrd.std N) = LinOrd.std N :=
    LinOrd.ext fun a b => Iff.rfl
  rw [ks, h, rsg_self]

/-- **The Koszul signs of the permutations are a cocycle.** -/
lemma ks_mul (N : ℕ) (τ τ' : Equiv.Perm (Fin N)) (p : Fin N → Bool) :
    ks K N (τ * τ') p = ks K N τ p * ks K N τ' fun a => p (τ a) := by
  have h : LinOrd.map (τ * τ') (LinOrd.std N) = LinOrd.map τ (LinOrd.map τ' (LinOrd.std N)) :=
    LinOrd.ext fun a b => Iff.rfl
  rw [ks, ks, ks, h, ← rsg_map τ (LinOrd.map τ' (LinOrd.std N)) (LinOrd.std N) p, mul_comm,
    rsg_trans]

/-- The values of the exchange of two adjacent inputs. -/
lemma swap_val {N : ℕ} (i : ℕ) (h : i + 1 < N) (x : Fin N) :
    ((Equiv.swap (⟨i, by omega⟩ : Fin N) ⟨i + 1, h⟩ x : Fin N) : ℕ)
      = if (x : ℕ) = i then i + 1 else if (x : ℕ) = i + 1 then i else x := by
  by_cases h1 : (x : ℕ) = i
  · have hx : x = ⟨i, by omega⟩ := Fin.ext h1
    rw [hx, Equiv.swap_apply_left, if_pos rfl]
  · by_cases h2 : (x : ℕ) = i + 1
    · have hx : x = ⟨i + 1, h⟩ := Fin.ext h2
      rw [hx, Equiv.swap_apply_right, if_neg (show ¬ i + 1 = i from by omega), if_pos rfl]
    · rw [Equiv.swap_apply_of_ne_of_ne (fun e => h1 (congrArg Fin.val e))
        (fun e => h2 (congrArg Fin.val e)), if_neg h1, if_neg h2]

/-- **The Koszul sign of the exchange of two adjacent inputs.** -/
lemma ks_swap {N : ℕ} (i : ℕ) (h : i + 1 < N) (p : Fin N → Bool) :
    ks K N (Equiv.swap ⟨i, by omega⟩ ⟨i + 1, h⟩) p
      = σ K (p ⟨i, by omega⟩ && p ⟨i + 1, h⟩) := by
  classical
  have hlt : ∀ a b : Fin N, (LinOrd.map (Equiv.swap (⟨i, by omega⟩ : Fin N) ⟨i + 1, h⟩)
      (LinOrd.std N)).lt a b ↔
        ((Equiv.swap (⟨i, by omega⟩ : Fin N) ⟨i + 1, h⟩ a : Fin N) : ℕ)
          < ((Equiv.swap (⟨i, by omega⟩ : Fin N) ⟨i + 1, h⟩ b : Fin N) : ℕ) := fun a b => by
    rw [LinOrd.map_lt, Equiv.symm_swap]
    exact Iff.rfl
  unfold ks rsg
  rw [Finset.prod_eq_single (⟨i + 1, h⟩ : Fin N)]
  · rw [Finset.prod_eq_single (⟨i, by omega⟩ : Fin N)]
    · rw [if_pos, Bool.and_comm]
      refine ⟨(hlt _ _).2 ?_, Fin.mk_lt_mk.2 (Nat.lt_succ_self i)⟩
      rw [swap_val, swap_val]
      simp
    · intro b _ hb
      refine if_neg fun hc => ?_
      have h1 := (hlt _ _).1 hc.1
      have h2 : (b : ℕ) < i + 1 := hc.2
      have hbi : (b : ℕ) ≠ i := fun e => hb (Fin.ext e)
      rw [swap_val, swap_val] at h1
      simp only [show ¬ i + 1 = i from by omega, if_false, if_true] at h1
      split_ifs at h1 <;> omega
    · exact fun hn => absurd (Finset.mem_univ _) hn
  · intro a _ ha
    refine Finset.prod_eq_one fun b _ => if_neg fun hc => ?_
    have h1 := (hlt _ _).1 hc.1
    have h2 : (b : ℕ) < a := hc.2
    have hai : (a : ℕ) ≠ i + 1 := fun e => ha (Fin.ext e)
    rw [swap_val, swap_val] at h1
    split_ifs at h1 <;> omega
  · exact fun hn => absurd (Finset.mem_univ _) hn

/-! ## The décalage signs under the exchange of two adjacent inputs -/

lemma σ_bodd_succ (m : ℕ) (x : Bool) :
    σ K (m.bodd && x) * σ K ((m + 1).bodd && x) = σ K x := by
  rw [Nat.bodd_succ]
  cases m.bodd <;> cases x <;> simp [σ]

/-- The décalage signs of a tuple of parities and of its exchange at two adjacent inputs differ
by the signs of the two parities. -/
lemma decφ_swap {N : ℕ} (i : ℕ) (h : i + 1 < N) (c : Fin N → Bool) :
    decφ K N c * decφ K N (fun a => c (Equiv.swap (⟨i, by omega⟩ : Fin N) ⟨i + 1, h⟩ a))
      = σ K (c ⟨i, by omega⟩) * σ K (c ⟨i + 1, h⟩) := by
  unfold decφ
  have hre : ∏ k : Fin N, σ K ((N + k + 1).bodd
        && c (Equiv.swap (⟨i, by omega⟩ : Fin N) ⟨i + 1, h⟩ k))
      = ∏ k : Fin N, σ K ((N + ((Equiv.swap (⟨i, by omega⟩ : Fin N) ⟨i + 1, h⟩ k : Fin N) : ℕ)
          + 1).bodd && c k) := by
    refine Fintype.prod_equiv (Equiv.swap (⟨i, by omega⟩ : Fin N) ⟨i + 1, h⟩) _ _ fun k => ?_
    rw [Equiv.swap_apply_self]
  rw [hre, ← Finset.prod_mul_distrib,
    Finset.prod_eq_mul (⟨i, by omega⟩ : Fin N) ⟨i + 1, h⟩
      (fun e => by have := congrArg Fin.val e; simp at this)]
  · rw [swap_val, swap_val]
    simp only [if_true, show ¬ i + 1 = i from by omega, if_false]
    rw [show N + (i + 1) + 1 = N + i + 1 + 1 from rfl, σ_bodd_succ, mul_comm
      (σ K ((N + i + 1 + 1).bodd && c ⟨i + 1, h⟩)), σ_bodd_succ]
  · intro k _ hk
    have h1 : (k : ℕ) ≠ i := fun e => hk.1 (Fin.ext e)
    have h2 : (k : ℕ) ≠ i + 1 := fun e => hk.2 (Fin.ext e)
    rw [swap_val, if_neg h1, if_neg h2]
    exact LInf.σ_mul_self _
  · exact fun hn => absurd (Finset.mem_univ _) hn
  · exact fun hn => absurd (Finset.mem_univ _) hn

/-! ## Relabelling and décalage -/

omit [Field K] in
lemma sign_core_swap [Field K] (a b : Bool) :
    σ K a * σ K b * (-1 * σ K (a && b)) = σ K (!a && !b) := by
  cases a <;> cases b <;> simp [σ]

/-- **The décalage of an operation relabelled by the exchange of two adjacent inputs, with the
sign of the exchange**: on homogeneous inputs, the décalage at the exchanged inputs with the
Koszul sign of the exchange for the shifted parities. -/
lemma dec_sv_swap {N : ℕ} (i : ℕ) (h : i + 1 < N) (G : EndGr K V (Fin N))
    {c : Fin N → Bool} {x : Fin N → V} (hx : IsHom (R := K) c x) :
    dec N (EndGr.sv (((Equiv.Perm.sign (Equiv.swap (⟨i, by omega⟩ : Fin N) ⟨i + 1, h⟩) : ℤ) : K)
        • GrOperad.map (R := K) (Equiv.swap (⟨i, by omega⟩ : Fin N) ⟨i + 1, h⟩) G)) x
      = ks K N (Equiv.swap ⟨i, by omega⟩ ⟨i + 1, h⟩) (fun a => !c a) •
        dec N (EndGr.sv G) (fun a => x (Equiv.swap (⟨i, by omega⟩ : Fin N) ⟨i + 1, h⟩ a)) := by
  obtain ⟨s, hs⟩ : ∃ s : Equiv.Perm (Fin N), s = Equiv.swap ⟨i, by omega⟩ ⟨i + 1, h⟩ := ⟨_, rfl⟩
  have hne : (⟨i, by omega⟩ : Fin N) ≠ ⟨i + 1, h⟩ := fun e => by
    have := congrArg Fin.val e
    simp at this
  have hsign : ((Equiv.Perm.sign s : ℤ) : K) = -1 := by
    rw [hs, Equiv.Perm.sign_swap hne]
    simp
  have hxs : IsHom (R := K) (fun a => c (s a)) fun a => x (s a) := fun a => hx (s a)
  have hmap : LinOrd.map s (LinOrd.map s.symm (LinOrd.std N)) = LinOrd.std N :=
    LinOrd.ext fun a b => by simp
  have hφ : rsg K (LinOrd.std N) (LinOrd.map s.symm (LinOrd.std N)) (fun a => c (s a))
      = ks K N s c := by
    rw [ks, ← rsg_map s (LinOrd.std N) (LinOrd.map s.symm (LinOrd.std N)) c, hmap]
  have hsv : EndGr.sv (((Equiv.Perm.sign s : ℤ) : K) • GrOperad.map (R := K) s G)
      = ((Equiv.Perm.sign s : ℤ) : K) • EndOp.mapL K V s (GrEnd.twist K V
          (rsg K (LinOrd.std N) (LinOrd.map s.symm (LinOrd.std N))) (EndGr.sv G)) := by
    show ((Equiv.Perm.sign s : ℤ) : K) • EndOp.mapL K V s
      (G.fam (LinOrd.map s.symm (LinOrd.std N))) = _
    rw [EndGr.fam_compat G (LinOrd.std N) (LinOrd.map s.symm (LinOrd.std N))]
    rfl
  rw [← hs, hsv, dec_apply_hom hx, dec_apply_hom hxs, MultilinearMap.smul_apply,
    EndOp.mapL_apply, twist_apply_hom hxs, hφ, hsign, smul_smul, smul_smul, smul_smul]
  congr 1
  have hd := decφ_swap (K := K) i h c
  rw [← hs] at hd
  have hk : ks K N s c = σ K (c ⟨i, by omega⟩ && c ⟨i + 1, h⟩) := by
    rw [hs]
    exact ks_swap i h c
  have hk' : ks K N s (fun a => !c a) = σ K (!c ⟨i, by omega⟩ && !c ⟨i + 1, h⟩) := by
    rw [hs]
    exact ks_swap i h _
  have hsq := decφ_mul_self K N (fun a => c (s a))
  have e1 : ks K N s (fun a => !c a)
      = decφ K N c * decφ K N (fun a => c (s a)) * (-1 * ks K N s c) := by
    rw [hk, hk', hd]
    exact (sign_core_swap _ _).symm
  rw [e1]
  linear_combination (-(decφ K N c * -1 * ks K N s c)) * hsq

/-- **The décalage of a relabelled operation, with the sign of the permutation**: on homogeneous
inputs, the décalage at the permuted inputs with the Koszul sign of the permutation for the
shifted parities. -/
theorem dec_sv_map {n : ℕ} (τ : Equiv.Perm (Fin (n + 1))) (G : EndGr K V (Fin (n + 1)))
    {c : Fin (n + 1) → Bool} {x : Fin (n + 1) → V} (hx : IsHom (R := K) c x) :
    dec (n + 1) (EndGr.sv (((Equiv.Perm.sign τ : ℤ) : K) • GrOperad.map (R := K) τ G)) x
      = ks K (n + 1) τ (fun a => !c a) • dec (n + 1) (EndGr.sv G) (fun a => x (τ a)) := by
  have hτ : τ ∈ Submonoid.closure
      (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    exact Submonoid.mem_top _
  induction hτ using Submonoid.closure_induction generalizing G c x with
  | mem s hs =>
    obtain ⟨k, rfl⟩ := hs
    exact dec_sv_swap (k : ℕ) (by have := k.2; omega) G hx
  | one =>
    rw [ks_one, one_smul, Equiv.Perm.sign_one]
    show dec (n + 1) (EndGr.sv ((((1 : ℤˣ) : ℤ) : K) • GrOperad.map (R := K) (Equiv.refl _) G)) x
      = _
    rw [GrOperad.map_refl]
    simp
  | mul a b _ _ ha hb =>
    have h1 : ((Equiv.Perm.sign (a * b) : ℤ) : K) • GrOperad.map (R := K) (a * b) G
        = ((Equiv.Perm.sign a : ℤ) : K) • GrOperad.map (R := K) a
          (((Equiv.Perm.sign b : ℤ) : K) • GrOperad.map (R := K) b G) := by
      rw [LinearMap.map_smul, smul_smul, Equiv.Perm.sign_mul,
        show (a * b : Equiv.Perm (Fin (n + 1))) = b.trans a from rfl, GrOperad.map_trans]
      push_cast
      rfl
    rw [h1, ha _ hx, hb G (fun k => hx (a k)), smul_smul, ks_mul]
    rfl

/-! ## Alternating operations and graded symmetric décalages -/

/-- **The décalage of an alternating operation is graded symmetric**, for the shifted
parities. -/
theorem dec_symm {n : ℕ} {G : EndGr K V (Fin (n + 1))}
    (hG : ∀ τ : Equiv.Perm (Fin (n + 1)),
      GrOperad.map (R := K) τ G = ((Equiv.Perm.sign τ : ℤ) : K) • G)
    (τ : Equiv.Perm (Fin (n + 1))) {c : Fin (n + 1) → Bool} {x : Fin (n + 1) → V}
    (hx : IsHom (R := K) c x) :
    ks K (n + 1) τ (fun a => !c a) • dec (n + 1) (EndGr.sv G) (fun a => x (τ a))
      = dec (n + 1) (EndGr.sv G) x := by
  rw [← dec_sv_map τ G hx, hG, smul_smul]
  have hs : ((Equiv.Perm.sign τ : ℤ) : K) * ((Equiv.Perm.sign τ : ℤ) : K) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  rw [hs, one_smul]

/-- **An operation whose décalage is graded symmetric under the exchanges of two adjacent inputs
alternates.** -/
theorem map_of_dec_symm {n : ℕ} {G : EndGr K V (Fin (n + 1))}
    (hG : ∀ (i : ℕ) (h : i + 1 < n + 1) (c : Fin (n + 1) → Bool) (x : Fin (n + 1) → V),
      IsHom (R := K) c x →
        dec (n + 1) (EndGr.sv G)
            (fun a => x (Equiv.swap (⟨i, by omega⟩ : Fin (n + 1)) ⟨i + 1, h⟩ a))
          = σ K (!c ⟨i, by omega⟩ && !c ⟨i + 1, h⟩) • dec (n + 1) (EndGr.sv G) x)
    (τ : Equiv.Perm (Fin (n + 1))) :
    GrOperad.map (R := K) τ G = ((Equiv.Perm.sign τ : ℤ) : K) • G := by
  have hτ : τ ∈ Submonoid.closure
      (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    exact Submonoid.mem_top _
  induction hτ using Submonoid.closure_induction with
  | mem s hs =>
    obtain ⟨k, rfl⟩ := hs
    have hk : (k : ℕ) + 1 < n + 1 := by have := k.2; omega
    have hne : (⟨k, by omega⟩ : Fin (n + 1)) ≠ ⟨k + 1, hk⟩ := fun e => by
      have := congrArg Fin.val e
      simp at this
    have hsign : ((Equiv.Perm.sign (Equiv.swap (⟨k, by omega⟩ : Fin (n + 1)) ⟨k + 1, hk⟩)
        : ℤ) : K) = -1 := by
      rw [Equiv.Perm.sign_swap hne]
      simp
    have key : ((Equiv.Perm.sign (Equiv.swap (⟨k, by omega⟩ : Fin (n + 1)) ⟨k + 1, hk⟩) : ℤ) : K)
        • GrOperad.map (R := K) (Equiv.swap (⟨k, by omega⟩ : Fin (n + 1)) ⟨k + 1, hk⟩) G = G := by
      refine EndGr.ext_sv ?_
      have hd : dec (n + 1) (EndGr.sv (((Equiv.Perm.sign
          (Equiv.swap (⟨k, by omega⟩ : Fin (n + 1)) ⟨k + 1, hk⟩) : ℤ) : K)
            • GrOperad.map (R := K) (Equiv.swap (⟨k, by omega⟩ : Fin (n + 1)) ⟨k + 1, hk⟩) G))
          = dec (n + 1) (EndGr.sv G) := ext_hom fun c x hx => by
        rw [dec_sv_swap (k : ℕ) hk G hx, ks_swap, hG k hk c x hx, smul_smul, LInf.σ_mul_self,
          one_smul]
      exact (dec_dec _ _).symm.trans ((congrArg (dec (n + 1)) hd).trans (dec_dec _ _))
    show GrOperad.map (R := K) (Equiv.swap (⟨k, by omega⟩ : Fin (n + 1)) ⟨k + 1, hk⟩) G
      = ((Equiv.Perm.sign (Equiv.swap (⟨k, by omega⟩ : Fin (n + 1)) ⟨k + 1, hk⟩) : ℤ) : K) • G
    rw [hsign] at key ⊢
    rw [neg_one_smul] at key ⊢
    exact neg_eq_iff_eq_neg.1 key
  | one =>
    show GrOperad.map (R := K) (Equiv.refl _) G = _
    rw [GrOperad.map_refl, Equiv.Perm.sign_one]
    simp
  | mul a b _ _ ha hb =>
    have hm : GrOperad.map (R := K) (a * b) G
        = GrOperad.map (R := K) a (GrOperad.map (R := K) b G) := by
      rw [← GrOperad.map_trans]
      rfl
    rw [hm, hb, LinearMap.map_smul, ha, smul_smul, Equiv.Perm.sign_mul]
    push_cast
    rw [mul_comm]

/-! ## Unshuffles -/

section Unsh

variable {N : ℕ}

lemma card_compl_fin (S : Finset (Fin N)) : Sᶜ.card = N - S.card := by
  rw [Finset.card_compl, Fintype.card_fin]

/-- The unshuffle of a subset, as a function: the inputs of the subset in increasing order, then
the others in increasing order. -/
noncomputable def unshFun (S : Finset (Fin N)) (k : Fin N) : Fin N :=
  if h : (k : ℕ) < S.card then S.orderEmbOfFin rfl ⟨k, h⟩
  else Sᶜ.orderEmbOfFin rfl ⟨k - S.card, by
    have := k.2
    rw [card_compl_fin]
    omega⟩

lemma unshFun_of_lt (S : Finset (Fin N)) (k : Fin N) (h : (k : ℕ) < S.card) :
    unshFun S k = S.orderEmbOfFin rfl ⟨k, h⟩ := dif_pos h

lemma unshFun_of_ge (S : Finset (Fin N)) (k : Fin N) (h : S.card ≤ (k : ℕ)) :
    unshFun S k = Sᶜ.orderEmbOfFin rfl ⟨k - S.card, by
      have := k.2
      rw [card_compl_fin]
      omega⟩ := dif_neg (not_lt.2 h)

lemma unshFun_mem_iff (S : Finset (Fin N)) (k : Fin N) : unshFun S k ∈ S ↔ (k : ℕ) < S.card := by
  constructor
  · intro h
    by_contra hk
    rw [unshFun_of_ge S k (not_lt.1 hk)] at h
    exact Finset.mem_compl.1 (Finset.orderEmbOfFin_mem Sᶜ rfl _) h
  · intro h
    rw [unshFun_of_lt S k h]
    exact Finset.orderEmbOfFin_mem S rfl _

lemma unshFun_lt_of_lt (S : Finset (Fin N)) {u w : Fin N} (huw : u < w)
    (h : (w : ℕ) < S.card ∨ S.card ≤ (u : ℕ)) : unshFun S u < unshFun S w := by
  have huw' : (u : ℕ) < w := huw
  rcases h with h | h
  · rw [unshFun_of_lt S u (by omega), unshFun_of_lt S w h]
    exact (S.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.2 huw')
  · rw [unshFun_of_ge S u h, unshFun_of_ge S w (by omega)]
    exact (Sᶜ.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.2 (by omega))

lemma unshFun_injective (S : Finset (Fin N)) : Function.Injective (unshFun S) := by
  intro a b hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hlt : (a : ℕ) < b := h
    by_cases hc : (b : ℕ) < S.card ∨ S.card ≤ (a : ℕ)
    · exact absurd hab (unshFun_lt_of_lt S h hc).ne
    · have ha : unshFun S a ∈ S := (unshFun_mem_iff S a).2 (by omega)
      rw [hab, unshFun_mem_iff] at ha
      omega
  · have hlt : (b : ℕ) < a := h
    by_cases hc : (a : ℕ) < S.card ∨ S.card ≤ (b : ℕ)
    · exact absurd hab.symm (unshFun_lt_of_lt S h hc).ne
    · have hb : unshFun S b ∈ S := (unshFun_mem_iff S b).2 (by omega)
      rw [← hab, unshFun_mem_iff] at hb
      omega

/-- **The unshuffle of a subset of the inputs**: the permutation listing the inputs of the subset
in increasing order, then the others in increasing order. -/
noncomputable def unsh (S : Finset (Fin N)) : Equiv.Perm (Fin N) :=
  Equiv.ofBijective (unshFun S) (Finite.injective_iff_bijective.1 (unshFun_injective S))

lemma unsh_apply (S : Finset (Fin N)) (k : Fin N) : unsh S k = unshFun S k := rfl

/-- The unshuffle of a subset carries the initial window onto the subset. -/
lemma map_ini_unsh (S : Finset (Fin N)) :
    (AltGen.ini N S.card).map (unsh S).toEmbedding = S := by
  ext x
  rw [Finset.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact (unshFun_mem_iff S k).2 (AltGen.mem_ini.1 hk)
  · intro hx
    obtain ⟨k, rfl⟩ := (unsh S).surjective x
    exact ⟨k, AltGen.mem_ini.2 ((unshFun_mem_iff S k).1 hx), rfl⟩

/-- **The Koszul sign of an unshuffle** is the sign of `LInf.usgn`. -/
theorem ks_unsh (S : Finset (Fin N)) (p : Fin N → Bool) :
    ks K N (unsh S) p = LInf.usgn (R := K) p S := by
  classical
  have hcond : ∀ a b : Fin N, ((LinOrd.map (unsh S) (LinOrd.std N)).lt a b ∧ (LinOrd.std N).lt b a)
      ↔ (a ∈ S ∧ b ∉ S ∧ b < a) := fun a b => by
    obtain ⟨u, rfl⟩ := (unsh S).surjective a
    obtain ⟨w, rfl⟩ := (unsh S).surjective b
    rw [LinOrd.map_lt, Equiv.symm_apply_apply, Equiv.symm_apply_apply, LinOrd.std_lt, LinOrd.std_lt,
      unsh_apply, unsh_apply, unshFun_mem_iff, unshFun_mem_iff]
    constructor
    · rintro ⟨huw, hlt⟩
      have huw' : (u : ℕ) < w := huw
      by_cases hc : (w : ℕ) < S.card ∨ S.card ≤ (u : ℕ)
      · exact absurd hlt (unshFun_lt_of_lt S huw hc).asymm
      · exact ⟨by omega, by omega, hlt⟩
    · rintro ⟨hu, hw, hlt⟩
      exact ⟨Fin.lt_def.2 (by omega), hlt⟩
  unfold ks rsg LInf.usgn
  refine (Finset.prod_subset (Finset.subset_univ S) fun a _ ha =>
    Finset.prod_eq_one fun b _ => if_neg fun hc => ha ((hcond a b).1 hc).1).symm.trans ?_
  refine Finset.prod_congr rfl fun a ha => ?_
  refine (Finset.prod_subset (Finset.subset_univ (Sᶜ.filter (· < a))) fun b _ hb =>
    if_neg fun hc => hb (Finset.mem_filter.2
      ⟨Finset.mem_compl.2 ((hcond a b).1 hc).2.1, ((hcond a b).1 hc).2.2⟩)).symm.trans ?_
  exact Finset.prod_congr rfl fun b hb => if_pos ((hcond a b).2
    ⟨ha, Finset.mem_compl.1 (Finset.mem_filter.1 hb).1, (Finset.mem_filter.1 hb).2⟩)

lemma oe_cast {S : Finset (Fin N)} {k : ℕ} (hk : S.card = k) (a : Fin k) :
    S.orderEmbOfFin hk a = S.orderEmbOfFin rfl (Fin.cast hk.symm a) := by
  subst hk
  rfl

end Unsh

/-! ## The terms of the generalized Jacobi expression -/

variable (K V) in
/-- **The family of operations of every arity** of a family in the bar convention: the operation
of arity `k + 1` is the `k`-th one, and the operation of arity zero vanishes. -/
def lfam (b : AInf.Fam K V) : LInf.LFam K V
  | 0 => 0
  | k + 1 => b k

/-- **A term of the convolution product at a generator, in the bar convention**: on homogeneous
inputs, the décalage of the planar term at the initial window, moved to a subset by its unshuffle
with the sign, is the term of the generalized Jacobi expression at the subset. -/
theorem dec_sv_term (γ : GrOperad.Inv K (ConvOp K (OrdCo K) (EndGr K V)))
    (hγ : GrOperad.Inv.IsPar true γ) (n : ℕ) (S : Finset (Fin (n + 1))) (hS : S.Nonempty)
    {c : Fin (n + 1) → Bool} {x : Fin (n + 1) → V} (hx : IsHom (R := K) c x) :
    dec (n + 1) (EndGr.sv (((Equiv.Perm.sign (unsh S) : ℤ) : K) • GrOperad.map (R := K) (unsh S)
        (NOrd.plTN γ γ (n + 1) (n + 1 - S.card, 0)))) x
      = LInf.usgn (R := K) (fun a => !c a) S •
        lfam K V (barFam γ) (Sᶜ.card + 1)
          (Fin.cons (lfam K V (barFam γ) S.card (LInf.restr x S)) (LInf.restr x Sᶜ)) := by
  have hl := hS.card_pos
  have hle : S.card ≤ n + 1 := (Finset.card_le_univ S).trans (Fintype.card_fin _).le
  obtain ⟨m', hm'⟩ : ∃ m', S.card = m' + 1 := ⟨S.card - 1, by omega⟩
  have hj : Sᶜ.card = n + 1 - S.card := card_compl_fin S
  rw [dec_sv_map (unsh S) _ hx, ks_unsh, LInf.term_eq (lfam K V (barFam γ)) x S hm' hj]
  congr 1
  have hy : IsHom (R := K) (fun a => c (unsh S a)) fun a => x (unsh S a) := fun a => hx _
  have hg : parML K V (m' + 1).bodd (EndGr.sv (famOf γ m')) = EndGr.sv (famOf γ m') :=
    (EndGr.sv_par _ _).symm.trans (congrArg EndGr.sv ((isPar_iff γ).1 hγ m'))
  have hcast : n + 1 - S.card + 1 - 1 + (m' + 1) = n + 1 := by omega
  rw [NOrd.plTN, dif_pos ⟨Nat.zero_le _, by show n + 1 - S.card < n + 1; omega⟩,
    dec_apply_hom hy,
    sv_plT γ γ (n + 1 - S.card) m' _ hg (by show n + 1 - (n + 1 - S.card) = m' + 1; omega) _ _ hy,
    smul_smul, decφ_mul_self, one_smul, AInf.acast_of_eq hcast, End.reindex_apply,
    End.kcompFin, End.compFin_apply, End.twist_apply]
  refine congrArg (barFam γ (n + 1 - S.card)) (funext fun t => ?_)
  rw [End.twistFn_of_ge _ _ _ t (Nat.zero_le _), LinearMap.id_apply]
  refine Fin.cases ?_ (fun r => ?_) t
  · refine (End.cfTuple_of_eq _ _ _ (0 : Fin (n + 1 - S.card + 1)) rfl).trans ?_
    rw [Fin.cons_zero]
    refine congrArg (barFam γ m') (funext fun s => ?_)
    have hs : ((0 : ℕ) + (s : ℕ)) < S.card := by have := s.2; omega
    show x (unsh S ⟨(0 : ℕ) + s, _⟩) = x (S.orderEmbOfFin hm' s)
    rw [unsh_apply, unshFun_of_lt S _ hs, oe_cast hm' s]
    exact congrArg (fun k => x (S.orderEmbOfFin rfl k)) (Fin.ext (Nat.zero_add _))
  · refine (End.cfTuple_of_gt _ _ _ r.succ (Nat.succ_pos _)).trans ?_
    rw [Fin.cons_succ]
    have hr : S.card ≤ (r : ℕ) + 1 + (m' + 1) - 1 := by omega
    show x (unsh S ⟨(r : ℕ) + 1 + (m' + 1) - 1, _⟩) = x (Sᶜ.orderEmbOfFin hj r)
    rw [unsh_apply, unshFun_of_ge S _ hr, oe_cast hj r]
    exact congrArg (fun k => x (Sᶜ.orderEmbOfFin rfl k)) (Fin.ext (by
      show (r : ℕ) + 1 + (m' + 1) - 1 - S.card = r
      omega))

/-- **The convolution square at a generator, in the bar convention, is the generalized Jacobi
expression**, on homogeneous inputs. -/
theorem dec_sv_sum (γ : GrOperad.Inv K (ConvOp K (OrdCo K) (EndGr K V)))
    (hγ : GrOperad.Inv.IsPar true γ) (n : ℕ) {c : Fin (n + 1) → Bool} {x : Fin (n + 1) → V}
    (hx : IsHom (R := K) c x) :
    dec (n + 1) (EndGr.sv (∑ S ∈ nonempties (Fin (n + 1)),
        ((Equiv.Perm.sign (unsh S) : ℤ) : K) • GrOperad.map (R := K) (unsh S)
          (NOrd.plTN γ γ (n + 1) (n + 1 - S.card, 0)))) x
      = LInf.jac (lfam K V (barFam γ)) (fun a => !c a) x := by
  rw [sv_sum, map_sum, MultilinearMap.sum_apply, LInf.jac]
  exact Finset.sum_congr (by ext S; simp) fun S hS =>
    dec_sv_term γ hγ n S (NOrd.mem_nonempties.1 hS) hx

end PInfLie

end Operad
