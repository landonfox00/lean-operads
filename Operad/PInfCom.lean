/-
# `Com∞`-algebras are `C∞`-algebras

Over a field `K` of characteristic zero, for a dg super module `V`: **the homotopy algebras over
the Koszul dual cooperad of `Com` on `V` are the `C∞`-structures on `V`**
(`PInfCom.pinfEquiv`), where

* `Koszul.PInfAlgebra K E r V` is the type of the `Com∞`-algebra structures, the algebras over
  `ΩCom^¡` for the presentation of `Com` of `Operad/SymPresComLie.lean`, on `V` with its
  differential;
* `PInfCom.CInfOver K V` is the type of the `C∞`-structures `b` in the bar convention
  (`CInf.IsCInf`, `Operad/CInfinity.lean`) for the sign involution `-eps K V`, the sign
  involution of the parity shift of `V`, whose first operation `b 0` is the differential of `V`.

The equivalence composes `HoAlgebra.equivTwisting`, the description of the twisting morphisms out
of `Com^¡` as the twisting morphisms out of the signed linear orders vanishing on the kernel of
`ComDual.rho` (`Twisting.equivOfSurjective`), and `PInfAss.twistingEquiv`: a `Com∞`-structure is
an `Ass∞`-structure vanishing on the shuffles, with the signs of `Operad/PInfAssEquiv.lean`.

* **A standard shuffle element is the signed sum of the orders of the inverses of the
  unshuffles** (`PInfCom.shStd_eq`, `PInfCom.exists_unsh`).
* **The value of an invariant family at a standard shuffle element, in the bar convention**
  (`PInfCom.dec_sv_shStd`), by `PInfLie.dec_sv_map` and the Koszul sign of the inverse of a
  permutation (`PInfCom.ks_inv`); the interleaving `CInf.merge` of two words is their
  concatenation moved by the inverse of the unshuffle (`PInfCom.merge_eq`).
* **An invariant family vanishes on a standard shuffle element** iff its operation in the bar
  convention vanishes on the signed shuffles of homogeneous words (`PInfCom.shStd_eq_zero_iff`),
  and it vanishes on the kernel of `ComDual.rho` iff it vanishes on the standard shuffle elements
  (`PInfCom.kills_iff`, `PInfCom.kills_iff_shuffle`).
-/
import Operad.ComKernel
import Operad.TwistingQuot
import Operad.PInfLieEquiv
import Operad.CInfinity

universe u v

namespace Operad

open Sym GerBV GrEnd
open scoped TensorProduct

namespace PInfCom

open OrdCo PInfAss PInfLie ComDual LieDual

variable {K : Type u} [Field K]

/-! ## The standard shuffles and the unshuffles -/

/-- The order of the inverse of an unshuffle is a shuffle. -/
lemma unsh_mem_consSet {n : ℕ} (S : Finset (Fin (n + 1))) :
    SetOperad.map (unsh S)⁻¹ (sd n) ∈ consSet (stdCons n S.card) := by
  intro x y v h
  show unsh S x < unsh S y ↔ v = true
  rw [h.2]
  have hside : ∀ u w : Fin (n + 1), ((u : ℕ) < S.card ↔ (w : ℕ) < S.card) → u < w →
      unsh S u < unsh S w := fun u w hs huw => by
    refine unshFun_lt_of_lt S huw ?_
    by_cases hw : (w : ℕ) < S.card
    · exact Or.inl hw
    · exact Or.inr (not_lt.1 fun hu => hw (hs.1 hu))
  constructor
  · intro hlt
    by_contra hxy
    rcases eq_or_lt_of_le (not_lt.1 hxy) with e | e
    · rw [e] at hlt
      exact lt_irrefl _ hlt
    · exact lt_asymm hlt (hside y x h.1.symm e)
  · exact hside x y h.1

/-- **A shuffle is the order of the inverse of an unshuffle.** -/
lemma exists_unsh {n k : ℕ} (hk : k ≤ n + 1) (τ : Equiv.Perm (Fin (n + 1)))
    (h : SetOperad.map τ⁻¹ (sd n) ∈ consSet (stdCons n k)) :
    ∃ S : Finset (Fin (n + 1)), S.card = k ∧ unsh S = τ := by
  have hmono : ∀ x y : Fin (n + 1), ((x : ℕ) < k ↔ (y : ℕ) < k) → x < y → τ x < τ y :=
    fun x y hs hxy => (h x y true ⟨hs, by simpa using hxy⟩).2 rfl
  obtain ⟨S, hS⟩ : ∃ S, S = (AltGen.ini (n + 1) k).map τ.toEmbedding := ⟨_, rfl⟩
  have hcard : S.card = k := by rw [hS, Finset.card_map, AltGen.card_ini hk]
  have hmem : ∀ t : Fin (n + 1), τ t ∈ S ↔ (t : ℕ) < k := fun t => by
    rw [hS]
    exact (Finset.mem_map' τ.toEmbedding).trans AltGen.mem_ini
  have hcc : Sᶜ.card = n + 1 - S.card := card_compl_fin S
  refine ⟨S, hcard, Equiv.ext fun t => ?_⟩
  rw [unsh_apply]
  by_cases ht : (t : ℕ) < S.card
  · rw [unshFun_of_lt S t ht]
    have hu := Finset.orderEmbOfFin_unique (s := S) rfl
      (f := fun j : Fin S.card => τ ⟨j, by have := j.2; omega⟩)
      (fun j => (hmem _).2 (by have := j.2; show (j : ℕ) < k; omega))
      (fun j j' hjj => hmono _ _ ⟨fun _ => by have := j'.2; show (j' : ℕ) < k; omega,
        fun _ => by have := j.2; show (j : ℕ) < k; omega⟩ (Fin.mk_lt_mk.2 hjj))
    exact (congrFun hu ⟨t, ht⟩).symm
  · have ht' : S.card ≤ (t : ℕ) := not_lt.1 ht
    rw [unshFun_of_ge S t ht']
    have hu := Finset.orderEmbOfFin_unique (s := Sᶜ) rfl
      (f := fun j : Fin Sᶜ.card => τ ⟨j + S.card, by have := j.2; omega⟩)
      (fun j => Finset.mem_compl.2 fun hin => by
        have := (hmem _).1 hin
        have h1 : (j : ℕ) + S.card < k := this
        omega)
      (fun j j' hjj => hmono _ _ ⟨fun h1 => by
          have h2 : (j : ℕ) + S.card < k := h1
          omega, fun h1 => by
          have h2 : (j' : ℕ) + S.card < k := h1
          omega⟩ (Fin.mk_lt_mk.2 (by
            have : (j : ℕ) < j' := hjj
            omega)))
    exact (congrFun hu ⟨t - S.card, by have := t.2; omega⟩).symm.trans
      (congrArg τ (Fin.ext (by show (t : ℕ) - S.card + S.card = t; omega)))

lemma unsh_inj {N : ℕ} {S S' : Finset (Fin N)} (hc : S.card = S'.card)
    (h : unsh S = unsh S') : S = S' :=
  (map_ini_unsh S).symm.trans ((by rw [hc, h] : (AltGen.ini N S.card).map (unsh S).toEmbedding
    = (AltGen.ini N S'.card).map (unsh S').toEmbedding).trans (map_ini_unsh S'))

/-- **A standard shuffle element is the signed sum of the orders of the inverses of the
unshuffles.** -/
theorem shStd_eq (n k : ℕ) (hk : k ≤ n + 1) :
    shStd K n k = ∑ S : {S : Finset (Fin (n + 1)) // S.card = k},
      ((Equiv.Perm.sign (unsh S.1) : ℤ) : K) •
        Finsupp.single (SetOperad.map (unsh S.1)⁻¹ (sd n)) (1 : K) := by
  classical
  refine Finsupp.ext fun M => ?_
  obtain ⟨π, rfl⟩ := exists_perm M
  have halt : (show NOrd (Fin (n + 1)) →₀ K from alt K n) (SetOperad.map π (sd n))
      = ((Equiv.Perm.sign π : ℤ) : K) := alt_apply n π
  rw [shStd, restr_apply, halt, Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  by_cases hM : SetOperad.map π (sd n) ∈ consSet (stdCons n k)
  · rw [if_pos hM]
    obtain ⟨S₀, hc, hu⟩ := exists_unsh hk π⁻¹ (by rwa [inv_inv])
    rw [Finset.sum_eq_single ⟨S₀, hc⟩]
    · rw [hu, inv_inv, Finsupp.single_eq_same, mul_one, Equiv.Perm.sign_inv]
    · intro S _ hS
      rw [Finsupp.single_eq_of_ne, mul_zero]
      intro heq
      have h1 : π = (unsh S.1)⁻¹ := LinOrd.eq_of_map_eq (congrArg Subtype.val heq)
      exact hS (Subtype.ext (unsh_inj (S.2.trans hc.symm) (by rw [hu, h1, inv_inv])))
    · exact fun h => absurd (Finset.mem_univ _) h
  · rw [if_neg hM]
    symm
    refine Finset.sum_eq_zero fun S _ => ?_
    rw [Finsupp.single_eq_of_ne, mul_zero]
    intro heq
    apply hM
    rw [heq]
    have h1 := unsh_mem_consSet S.1
    rw [S.2] at h1
    exact h1

/-! ## The Koszul sign of the inverse of a permutation -/

omit [Field K] in
lemma rsg_mul_self [Field K] {A : Type} [Fintype A] (L L' : LinOrd A) (c : A → Bool) :
    rsg K L L' c * rsg K L L' c = 1 := by
  classical
  unfold rsg
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun a _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun b _ => ?_
  split_ifs
  · exact LInf.σ_mul_self _
  · exact one_mul 1

/-- The Koszul sign of the inverse of a permutation. -/
lemma ks_inv (N : ℕ) (τ : Equiv.Perm (Fin N)) (q : Fin N → Bool) :
    ks K N τ⁻¹ q = ks K N τ fun a => q (τ⁻¹ a) := by
  have h := ks_mul (K := K) N τ⁻¹ τ q
  rw [inv_mul_cancel, ks_one] at h
  have hsq : ks K N τ (fun a => q (τ⁻¹ a)) * ks K N τ (fun a => q (τ⁻¹ a)) = 1 :=
    rsg_mul_self _ _ _
  linear_combination (-(ks K N τ⁻¹ q)) * hsq - (ks K N τ fun a => q (τ⁻¹ a)) * h

/-! ## The operations on the shuffles -/

variable {V : Type v} [AddCommGroup V] [Module K V] [SuperMod K V]

/-- **The value of an invariant family at a standard shuffle element, in the bar convention**: on
homogeneous inputs, the signed sum of the operation at the inputs moved by the inverses of the
unshuffles. -/
theorem dec_sv_shStd (γ : GrOperad.Inv K (ConvOp K (OrdCo K) (EndGr K V))) (n k : ℕ)
    (hk : k ≤ n + 1) {c : Fin (n + 1) → Bool} {z : Fin (n + 1) → V} (hz : IsHom (R := K) c z) :
    dec (n + 1) (EndGr.sv (ConvOp.toLin (γ.1 (Fin (n + 1))) (shStd K n k))) z
      = ∑ S : {S : Finset (Fin (n + 1)) // S.card = k},
          LInf.usgn (R := K) (fun t => !c ((unsh S.1)⁻¹ t)) S.1 •
            barFam γ n (fun t => z ((unsh S.1)⁻¹ t)) := by
  have h1 : ConvOp.toLin (γ.1 (Fin (n + 1))) (shStd K n k)
      = ∑ S : {S : Finset (Fin (n + 1)) // S.card = k},
          ((Equiv.Perm.sign (unsh S.1)⁻¹ : ℤ) : K) •
            GrOperad.map (R := K) (unsh S.1)⁻¹ (famOf γ n) := by
    refine (congrArg (ConvOp.toLin (γ.1 (Fin (n + 1)))) (shStd_eq n k hk)).trans ?_
    refine (map_sum (ConvOp.toLin (γ.1 (Fin (n + 1)))) _ _).trans ?_
    refine Finset.sum_congr rfl fun S _ => ?_
    refine (LinearMap.map_smul (ConvOp.toLin (γ.1 (Fin (n + 1)))) _ _).trans ?_
    rw [Equiv.Perm.sign_inv]
    exact congrArg _ (toLin_bs_map γ (unsh S.1)⁻¹)
  rw [h1, sv_sum, map_sum, MultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [dec_sv_map (unsh S.1)⁻¹ (famOf γ n) hz, ks_inv, ks_unsh]
  rfl

omit [Field K] in
/-- **The interleaving of two words is their concatenation moved by the inverse of the
unshuffle.** -/
lemma merge_eq {a c : ℕ} (S : Finset (Fin (a + 1 + (c + 1)))) (hS : S.card = a + 1) {X : Type*}
    (x : Fin (a + 1) → X) (y : Fin (c + 1) → X) (t : Fin (a + 1 + (c + 1))) :
    CInf.merge S hS x y t = Fin.append x y ((unsh S)⁻¹ t) := by
  obtain ⟨u, rfl⟩ := (unsh S).surjective t
  rw [show (unsh S)⁻¹ (unsh S u) = u from (unsh S).symm_apply_apply u]
  have hc : Sᶜ.card = c + 1 := by rw [card_compl_fin, hS]; omega
  by_cases hu : (u : ℕ) < S.card
  · have hmem : unsh S u ∈ S := (unshFun_mem_iff S u).2 hu
    have h1 : (S.orderIsoOfFin hS).symm ⟨unsh S u, hmem⟩ = ⟨u, by omega⟩ := by
      rw [OrderIso.symm_apply_eq]
      refine Subtype.ext ?_
      show unsh S u = S.orderEmbOfFin hS ⟨u, by omega⟩
      rw [unsh_apply, unshFun_of_lt S u hu, oe_cast hS]
      rfl
    rw [CInf.merge_of_mem hS x y hmem, h1]
    exact ((congrArg (Fin.append x y) (Fin.ext rfl : u = Fin.castAdd (c + 1) ⟨u, by omega⟩)).trans
      (Fin.append_left x y _)).symm
  · have hu' : S.card ≤ (u : ℕ) := not_lt.1 hu
    have hnm : unsh S u ∉ S := fun h => hu ((unshFun_mem_iff S u).1 h)
    have hub : (u : ℕ) - (a + 1) < c + 1 := by have := u.2; omega
    have h1 : (Sᶜ.orderIsoOfFin hc).symm ⟨unsh S u, Finset.mem_compl.2 hnm⟩
        = ⟨u - (a + 1), hub⟩ := by
      rw [OrderIso.symm_apply_eq]
      refine Subtype.ext ?_
      show unsh S u = Sᶜ.orderEmbOfFin hc ⟨u - (a + 1), hub⟩
      rw [unsh_apply, unshFun_of_ge S u hu', oe_cast hc]
      exact congrArg _ (Fin.ext (by show (u : ℕ) - S.card = u - (a + 1); rw [hS]))
    have h2 : CInf.merge S hS x y (unsh S u)
        = y ((Sᶜ.orderIsoOfFin hc).symm ⟨unsh S u, Finset.mem_compl.2 hnm⟩) := dif_neg hnm
    rw [h2, h1]
    exact ((congrArg (Fin.append x y) (Fin.ext (by
      show (u : ℕ) = a + 1 + (u - (a + 1))
      omega) : u = Fin.natAdd (a + 1) ⟨u - (a + 1), hub⟩)).trans
        (Fin.append_right x y _)).symm

/-- **An invariant family vanishes on a standard shuffle element** iff its operation in the bar
convention vanishes on the signed shuffles of homogeneous words. -/
theorem shStd_eq_zero_iff [CharZero K] (γ : GrOperad.Inv K (ConvOp K (OrdCo K) (EndGr K V)))
    (a c : ℕ) :
    ConvOp.toLin (γ.1 (Fin (a + 1 + c + 1))) (shStd K (a + 1 + c) (a + 1)) = 0
      ↔ ∀ (x : Fin (a + 1) → V) (y : Fin (c + 1) → V) (px : Fin (a + 1) → Bool)
          (py : Fin (c + 1) → Bool), (∀ i, IsPar (-eps K V) (px i) (x i)) →
          (∀ j, IsPar (-eps K V) (py j) (y j)) →
          ∑ S : {S : Finset (Fin (a + 1 + (c + 1))) // S.card = a + 1},
            (LInf.usgn (CInf.merge (a := a + 1) (c := c + 1) S.1 S.2 px py) S.1 : K) •
              barFam γ (a + 1 + c) (CInf.merge (a := a + 1) (c := c + 1) S.1 S.2 x y) = 0 := by
  have key : ∀ (cz : Fin (a + 1 + (c + 1)) → Bool) (z : Fin (a + 1 + (c + 1)) → V),
      IsHom (R := K) cz z →
      dec (a + 1 + c + 1) (EndGr.sv (ConvOp.toLin (γ.1 (Fin (a + 1 + c + 1)))
          (shStd K (a + 1 + c) (a + 1)))) z
        = ∑ S : {S : Finset (Fin (a + 1 + (c + 1))) // S.card = a + 1},
            (LInf.usgn (CInf.merge (a := a + 1) (c := c + 1) S.1 S.2
              (fun i => !cz (Fin.castAdd (c + 1) i))
              (fun j => !cz (Fin.natAdd (a + 1) j))) S.1 : K) •
              barFam γ (a + 1 + c) (CInf.merge (a := a + 1) (c := c + 1) S.1 S.2
                (fun i => z (Fin.castAdd (c + 1) i))
                (fun j => z (Fin.natAdd (a + 1) j))) := fun cz z hz => by
    rw [dec_sv_shStd γ (a + 1 + c) (a + 1) (by omega) hz]
    refine Finset.sum_congr rfl fun S _ => ?_
    have h1 : (fun t => z ((unsh S.1)⁻¹ t))
        = CInf.merge (a := a + 1) (c := c + 1) S.1 S.2 (fun i => z (Fin.castAdd (c + 1) i))
          (fun j => z (Fin.natAdd (a + 1) j)) := funext fun t => by
      rw [merge_eq, Fin.append_castAdd_natAdd]
    have h2 : (fun t => !cz ((unsh S.1)⁻¹ t))
        = CInf.merge (a := a + 1) (c := c + 1) S.1 S.2 (fun i => !cz (Fin.castAdd (c + 1) i))
          (fun j => !cz (Fin.natAdd (a + 1) j)) := funext fun t => by
      rw [merge_eq, Fin.append_castAdd_natAdd (f := fun s => !cz s)]
    rw [h1, h2]
  constructor
  · intro h x y px py hx hy
    have hz : IsHom (R := K) (fun t => !(Fin.append px py t)) (Fin.append x y) := fun t => by
      refine Fin.addCases (fun i => ?_) (fun j => ?_) t
      · show SuperMod.pr (R := K) (!(Fin.append px py (Fin.castAdd (c + 1) i)))
          (Fin.append x y (Fin.castAdd (c + 1) i)) = Fin.append x y (Fin.castAdd (c + 1) i)
        rw [Fin.append_left, Fin.append_left]
        exact isHom_of_isPar (hx i)
      · show SuperMod.pr (R := K) (!(Fin.append px py (Fin.natAdd (a + 1) j)))
          (Fin.append x y (Fin.natAdd (a + 1) j)) = Fin.append x y (Fin.natAdd (a + 1) j)
        rw [Fin.append_right, Fin.append_right]
        exact isHom_of_isPar (hy j)
    have hk := key _ _ hz
    rw [h] at hk
    simp only [Fin.append_left, Fin.append_right, Bool.not_not] at hk
    have h0 : dec (a + 1 + c + 1) (EndGr.sv (0 : EndGr K V (Fin (a + 1 + c + 1))))
        (Fin.append x y : Fin (a + 1 + (c + 1)) → V) = 0 := by
      rw [show EndGr.sv (0 : EndGr K V (Fin (a + 1 + c + 1))) = 0 from rfl, LinearMap.map_zero]
      rfl
    exact hk.symm.trans h0
  · intro h
    refine (EndGr.eq_zero_iff_sv _).2 (dec_eq_zero (ext_hom fun cz z hz => ?_))
    rw [key cz z hz]
    exact h _ _ _ _ (fun i => isPar_of_isHom (hz _)) (fun j => isPar_of_isHom (hz _))

/-! ## The equivalence -/

variable [DGSuperMod K V] [CharZero K]

omit [SuperMod K V] [DGSuperMod K V] [CharZero K] in
/-- An operation of a family, at an equal index. -/
lemma fam_cast (b : AInf.Fam K V) {m m' : ℕ} (h : m = m') (w : Fin (m' + 1) → V) :
    b m (w ∘ Fin.cast (by rw [h])) = b m' w := by
  subst h
  rfl

omit [DGSuperMod K V] in
/-- **An invariant family vanishes on the kernel of the signed linear orders onto `Com^¡`** iff
it vanishes on the standard shuffle elements. -/
theorem kills_iff (α : GrOperad.Inv K (ConvOp K (OrdCo K) (EndGr K V))) :
    (∀ (A : Type) [Fintype A] [DecidableEq A] (x : OrdCo K A),
        (rho K).app A x = 0 → ConvOp.toLin (α.1 A) x = 0)
      ↔ ∀ a c : ℕ,
        ConvOp.toLin (α.1 (Fin (a + 1 + c + 1))) (shStd K (a + 1 + c) (a + 1)) = 0 := by
  constructor
  · intro h a c
    exact h _ _ (rho_eq_zero (shStd_mem (by omega) (by omega)))
  · intro h A _ _ x hx
    rcases isEmpty_or_nonempty A with hA | hA
    · have hx0 : x = 0 := (Finsupp.ext fun L => (IsEmpty.false (Classical.choice L.2)).elim :
        (show NOrd A →₀ K from x) = 0)
      rw [hx0, LinearMap.map_zero]
    · obtain ⟨n, hn⟩ : ∃ n, Fintype.card A = n + 1 :=
        ⟨Fintype.card A - 1, by have := Fintype.card_pos (α := A); omega⟩
      obtain ⟨e, -⟩ : ∃ e : Fin (n + 1) ≃ A, True :=
        ⟨(Fintype.equivFinOfCardEq hn).symm, trivial⟩
      have hx' : (rho K).app (Fin (n + 1)) (SymSpecies.map (R := K) e.symm x) = 0 := by
        rw [(rho K).app_map, hx, map_zero]
      have hmem := (rho_eq_zero_iff _).1 hx'
      have hker : stdSub K n ≤ LinearMap.ker (ConvOp.toLin (α.1 (Fin (n + 1)))) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨k, hk, hkn, e', rfl⟩
        obtain ⟨a, rfl⟩ : ∃ a, k = a + 1 := ⟨k - 1, by omega⟩
        obtain ⟨c, rfl⟩ : ∃ c, n = a + 1 + c := ⟨n - (a + 1), by omega⟩
        show ConvOp.toLin (α.1 (Fin (a + 1 + c + 1)))
          (GrOperad.map (R := K) e' (show OrdCo K _ from shStd K (a + 1 + c) (a + 1))) = 0
        rw [SgnLin.inv_toLin_map, h a c, map_zero]
      have h0 : ConvOp.toLin (α.1 (Fin (n + 1))) (SymSpecies.map (R := K) e.symm x) = 0 :=
        hker hmem
      have hxe : x = GrOperad.map (R := K) e (SymSpecies.map (R := K) e.symm x) :=
        (SymSpecies.map_map_symm (R := K) e x).symm
      rw [hxe, SgnLin.inv_toLin_map, h0, map_zero]

omit [CharZero K] in
/-- The family of the differential vanishes on the standard shuffle elements. -/
lemma toLin_dInv_shStd (a c : ℕ) :
    ConvOp.toLin ((dInv K V).1 (Fin (a + 1 + c + 1))) (shStd K (a + 1 + c) (a + 1)) = 0 := by
  refine (EndGr.eq_zero_iff_sv _).2 (dec_eq_zero (ext_hom fun cz z hz => ?_))
  rw [dec_sv_shStd (dInv K V) (a + 1 + c) (a + 1) (by omega) hz]
  refine (Finset.sum_eq_zero fun S _ => ?_).trans rfl
  have hb : barFam (dInv K V) (a + 1 + c) = 0 := by
    show dec (a + 1 + c + 1) (EndGr.sv (famOf (dInv K V) (a + 1 + c))) = 0
    rw [famOf_dInv_ne (by omega)]
    exact LinearMap.map_zero _
  rw [hb]
  exact smul_zero _

variable (K V) in
/-- **The `C∞`-structures of a dg super module**: the `C∞`-structures in the bar convention, for
the opposite sign involution, whose first operation is the differential. -/
def CInfOver : Type v :=
  {b : AInf.Fam K V // CInf.IsCInf (-eps K V) b ∧
    ∀ v : Fin 1 → V, b 0 v = DGSuperMod.d (R := K) (v 0)}

omit [DGSuperMod K V] [CharZero K] in
/-- The shuffle condition of `CInf.IsCInf`, for the opposite sign involution. -/
def IsShuf (b : AInf.Fam K V) : Prop :=
  ∀ (a c : ℕ) (x : Fin (a + 1) → V) (y : Fin (c + 1) → V) (px : Fin (a + 1) → Bool)
    (py : Fin (c + 1) → Bool), (∀ i, IsPar (-eps K V) (px i) (x i)) →
    (∀ j, IsPar (-eps K V) (py j) (y j)) →
    ∑ S : {S : Finset (Fin (a + 1 + (c + 1))) // S.card = a + 1},
      (LInf.usgn (CInf.merge S.1 S.2 px py) S.1 : K) •
        b (a + c + 1) (CInf.merge S.1 S.2 x y ∘ Fin.cast (by omega)) = 0

/-- **A twisting morphism from the signed linear orders vanishes on the kernel onto `Com^¡`** iff
its `A∞`-structure vanishes on the signed shuffles. -/
theorem kills_iff_shuffle (α : Twisting K (OrdCo K) (EndGr K V)) :
    (∀ (A : Type) [Fintype A] [DecidableEq A] (x : OrdCo K A),
        (rho K).app A x = 0 → ConvOp.toLin (α.1.1 A) x = 0)
      ↔ IsShuf (PInfAss.twistingEquiv α).1 := by
  unfold IsShuf
  rw [kills_iff]
  refine forall_congr' fun a => forall_congr' fun c => ?_
  have h1 : ConvOp.toLin (α.1.1 (Fin (a + 1 + c + 1))) (shStd K (a + 1 + c) (a + 1)) = 0
      ↔ ConvOp.toLin ((α.1 + dInv K V).1 (Fin (a + 1 + c + 1)))
        (shStd K (a + 1 + c) (a + 1)) = 0 := by
    have h2 : ConvOp.toLin ((α.1 + dInv K V).1 (Fin (a + 1 + c + 1)))
          (shStd K (a + 1 + c) (a + 1))
        = ConvOp.toLin (α.1.1 (Fin (a + 1 + c + 1))) (shStd K (a + 1 + c) (a + 1))
          + ConvOp.toLin ((dInv K V).1 (Fin (a + 1 + c + 1))) (shStd K (a + 1 + c) (a + 1)) := rfl
    rw [h2, toLin_dInv_shStd, add_zero]
  rw [h1, shStd_eq_zero_iff]
  refine forall_congr' fun x => forall_congr' fun y => forall_congr' fun px =>
    forall_congr' fun py => forall_congr' fun _ => forall_congr' fun _ => ?_
  have hterm : ∀ S : {S : Finset (Fin (a + 1 + (c + 1))) // S.card = a + 1},
      (PInfAss.twistingEquiv α).1 (a + c + 1) (CInf.merge S.1 S.2 x y ∘ Fin.cast (by omega))
        = barFam (α.1 + dInv K V) (a + 1 + c)
          (CInf.merge (a := a + 1) (c := c + 1) S.1 S.2 x y) := fun S =>
    fam_cast (barFam (α.1 + dInv K V)) (by omega : a + c + 1 = a + 1 + c) _
  simp only [hterm]

/-- **Twisting morphisms from the Koszul dual cooperad of `Com` to the endomorphism operad of a
dg super module are its `C∞`-structures.** -/
noncomputable def twistingEquiv :
    Twisting K (Koszul.Dual K (SymPresComLie.ECom K) (SymPresComLie.rCom K)) (EndGr K V)
      ≃ CInfOver K V :=
  (Twisting.equivOfSurjective (rho K) (fun A _ _ => rho_surjective A) rho_one).trans
    ((Equiv.subtypeEquiv PInfAss.twistingEquiv fun α => kills_iff_shuffle α).trans
      (show {b : AInfOver K V // IsShuf b.1} ≃ CInfOver K V from
        { toFun := fun b => ⟨b.1.1, ⟨b.1.2.1, b.2⟩, b.1.2.2⟩
          invFun := fun b => ⟨⟨b.1, b.2.1.toIsAInf, b.2.2⟩, b.2.1.shuffle⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }))

/-- **`Com∞`-algebras are `C∞`-algebras**: over a field of characteristic zero, the homotopy
algebras over the Koszul dual cooperad of the presentation of `Com`, on a dg super module `V`,
are the `C∞`-structures on `V` in the bar convention, for the opposite sign involution, whose
first operation is the differential. -/
noncomputable def pinfEquiv :
    Koszul.PInfAlgebra K (SymPresComLie.ECom K) (SymPresComLie.rCom K) V ≃ CInfOver K V :=
  HoAlgebra.equivTwisting.trans twistingEquiv

end PInfCom

end Operad
