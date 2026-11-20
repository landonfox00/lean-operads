/-
# The convolution product in the endomorphism operad and the `A∞` product

`V` is a super module over a field `K`, `EndGr K V` its graded endomorphism operad, and
`eps K V` its sign involution, `1` on the even part and `-1` on the odd part. The `A∞`-structures
of `Operad/AInfinity.lean` are in the bar convention, where every operation is odd; the
operations of a twisting morphism have the parity of their arity. The two are related by **the
décalage** (`PInfAss.dec`): the input `k` of `N` is twisted by the sign involution `N + k + 1`
times, and the sign involution is replaced by its opposite.

* **Planar composites on homogeneous inputs** (`PInfAss.sv_map_comp`), from
  `GrEnd.kcomp_apply_hom`.
* **The sign identity** (`PInfAss.sign_core`): the Koszul sign of a planar composite in the
  endomorphism operad, the signs of the cooperad of signed linear orders and the décalage sign of
  the inputs make up the sign of the composite in the bar convention after the décalages. The
  products are compared input by input, along the three zones of the inputs.
* Hence a composite in the bar convention of two décalages (`PInfAss.term_eq`), each planar term
  of the convolution product (`PInfAss.sv_plT`), and **the convolution product at a standard
  order is the product of `A∞`-structures** (`PInfAss.sv_star`):
  `(f ⋆ g)(1 < ⋯ < n + 1) = dec (tstar (-eps) 1 (barFam f) (barFam g) n)`, where `barFam f` is
  the family of the décalages of the operations of `f`.
* **The differential.** Composing with an operation of arity one, in planar terms
  (`PInfAss.lcomp_eq_planar`, `PInfAss.rcomp_eq_planar`). For a dg super module, the family of
  the differential `PInfAss.dInv` is the differential at the standard order on one input; the
  differential of an operation of an odd family is its convolution commutator with `dInv`
  (`PInfAss.d_famOf`), and `dInv ⋆ dInv = 0` (`PInfAss.star_dInv_dInv`).
* **The Maurer–Cartan equation is the `A∞` relation** (`PInfAss.mc_iff_tstar`): the planar
  Maurer–Cartan equations of an odd family `α` hold iff `barFam (α + dInv)` squares to zero for
  the Koszul product, for the opposite sign involution.

The equivalence of `Ass∞`-algebras with `A∞`-algebras is in `Operad/PInfAssEquiv.lean`.
-/
import Operad.OrdDual
import Operad.OrdTwisting
import Operad.AInfinity
import Operad.GerOperad
import Operad.PInfinity

universe u v

namespace Operad

open Sym GerBV GrEnd
open scoped TensorProduct

namespace PInfAss

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V] [SuperMod K V]

/-! ## The sign involution of a super module -/

variable (K V) in
/-- **The sign involution** of a super module: `1` on the even part and `-1` on the odd part. -/
def eps : V →ₗ[K] V := SuperMod.pr (R := K) false - SuperMod.pr (R := K) true

lemma eps_apply_hom {c : Bool} {x : V} (hx : SuperMod.pr (R := K) c x = x) :
    eps K V x = σ K c • x := by
  rw [eps, LinearMap.sub_apply]
  cases c
  · rw [hx, ← hx, SuperMod.pr_pr]
    simp
  · rw [hx, ← hx, SuperMod.pr_pr]
    simp

/-! ## Planar composites in the endomorphism operad, on homogeneous inputs -/

/-- **A planar composite at standard orders, on homogeneous inputs**: the inner operation, of
parity `q`, crosses the inputs before its slot. -/
lemma sv_map_comp {n l N : ℕ} (i : Fin n) (h : N + 1 = n + l) (F : EndGr K V (Fin n))
    (G : EndGr K V (Fin l)) {q : Bool} (hG : parML K V q (EndGr.sv G) = EndGr.sv G)
    {c : Fin N → Bool} {x : Fin N → V} (hx : IsHom (R := K) c x) :
    EndGr.sv (GrOperad.map (R := K) (posEquivF i l N h) (GrOperad.comp (R := K) i F G)) x
      = bsg K (LinOrd.std n) i q (slot i q fun u => c (posEquivF i l N h u)) •
          EndGr.sv F (feed i (fun u => x (posEquivF i l N h u))
            (EndGr.sv G fun b => x (posEquivF i l N h (Sum.inr b)))) := by
  have hL : LinOrd.map (posEquivF i l N h).symm (LinOrd.std N)
      = LinOrd.comp i (LinOrd.std n) (LinOrd.std l) := by
    rw [← map_posEquivF i h]
    exact LinOrd.ext fun a b => by simp
  show EndOp.mapL K V (posEquivF i l N h)
    ((EndGr.compE i F G).fam (LinOrd.map (posEquivF i l N h).symm (LinOrd.std N))) x = _
  rw [hL, EndGr.compE_fam, EndGr.compFam_comp, EndOp.mapL_apply]
  exact kcomp_apply_hom (LinOrd.std n) i (EndGr.sv F) hG fun u => hx (posEquivF i l N h u)

/-! ## Signs -/

section Signs

variable (K)

omit [Field K] in
/-- Two numbers differing by an even number have the same parity. -/
lemma bodd_congr {x y a b : ℕ} (h : x + 2 * a = y + 2 * b) : x.bodd = y.bodd := by
  have h' := congrArg Nat.bodd h
  simpa [Nat.bodd_add, Nat.bodd_mul] using h'

lemma σ_bodd (m : ℕ) : σ K m.bodd = (-1 : K) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.bodd_succ, pow_succ, ← ih]
    cases m.bodd <;> simp

lemma σ_and_tot {X : Type} [Fintype X] (m : Bool) (f : X → Bool) :
    σ K (m && tot f) = ∏ t, σ K (m && f t) := by
  cases m
  · simp
  · simp only [Bool.true_and]
    rw [tot, σ_bodd, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun t _ => ?_
    cases f t <;> simp

/-- The product over `Fin n` splits off the factor at `i`. -/
lemma prod_fin_split {n : ℕ} (i : Fin n) (f : Fin n → K) :
    ∏ s, f s = f i * ∏ a : Without (Fin n) i, f a.1 := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)]
  congr 1
  exact Finset.prod_subtype (Finset.univ.erase i) (fun a => by simp) f

/-- There are `i` inputs before the input `i`. -/
lemma prod_neg_one_lt {n : ℕ} (i : Fin n) :
    ∏ a : Without (Fin n) i, (if a.1 < i then (-1 : K) else 1) = σ K (i : ℕ).bodd := by
  have h := prod_fin_split K i fun a => if a < i then (-1 : K) else 1
  rw [if_neg (lt_irrefl i), one_mul] at h
  rw [← h, Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, σ_bodd]
  congr 1
  rw [show (Finset.univ.filter fun a : Fin n => a < i) = Finset.Iio i from by
    ext a
    simp]
  exact Fin.card_Iio i

/-- **The décalage sign**: the input `k` of `N` contributes its parity `N + k + 1` times. -/
noncomputable def decφ (N : ℕ) (c : Fin N → Bool) : K := ∏ k : Fin N, σ K ((N + k + 1).bodd && c k)

lemma decφ_mul_self (N : ℕ) (c : Fin N → Bool) : decφ K N c * decφ K N c = 1 := by
  rw [decφ, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun k _ => σ_mul_self K _

/-- **The sign identity of the décalage**: the Koszul sign of the planar composite of the
endomorphism operad, with the signs of the cooperad of signed linear orders, is the sign of the
composite in the bar convention after the décalages. -/
theorem sign_core {n l : ℕ} (i : Fin n) (h : (n - 1 + l) + 1 = n + l)
    (e : Without (Fin n) i ⊕ Fin l → Bool) :
    decφ K (n - 1 + l) (fun k => e ((posEquivF i l (n - 1 + l) h).symm k))
        * (σ K ((l + 1).bodd && (n + i + 1).bodd) * σ K (n + 1).bodd)
        * bsg K (LinOrd.std n) i l.bodd (slot i l.bodd e)
      = decφ K n (slot i l.bodd e)
        * (∏ t : Fin n, if t < i then -σ K (slot i l.bodd e t) else 1)
        * decφ K l (fun t => e (Sum.inr t)) := by
  have hi := i.isLt
  -- the three products over the inputs of the composite
  have h1 : decφ K (n - 1 + l) (fun k => e ((posEquivF i l (n - 1 + l) h).symm k))
      = (∏ a : Without (Fin n) i, σ K ((n - 1 + l + (posEquivF i l (n - 1 + l) h (Sum.inl a) : ℕ)
          + 1).bodd && e (Sum.inl a)))
        * ∏ t : Fin l, σ K ((n - 1 + l + (posEquivF i l (n - 1 + l) h (Sum.inr t) : ℕ)
          + 1).bodd && e (Sum.inr t)) := by
    rw [decφ, ← Equiv.prod_comp (posEquivF i l (n - 1 + l) h), Fintype.prod_sum_type]
    simp only [Equiv.symm_apply_apply]
  have h2 : bsg K (LinOrd.std n) i l.bodd (slot i l.bodd e)
      = ∏ a : Without (Fin n) i, if a.1 < i then σ K (l.bodd && e (Sum.inl a)) else 1 := by
    rw [bsg, prod_fin_split K i, if_neg ((LinOrd.std n).irrefl i), one_mul]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [slot, feed_of_ne a.2]
    by_cases hlt : a.1 < i
    · rw [if_pos hlt, if_pos (show (LinOrd.std n).lt a.1 i from hlt)]
    · rw [if_neg hlt, if_neg (show ¬ (LinOrd.std n).lt a.1 i from hlt)]
  have h3 : decφ K n (slot i l.bodd e)
      = (σ K ((n + i + 1).bodd && l.bodd) * ∏ t : Fin l, σ K ((n + i + 1).bodd && e (Sum.inr t)))
        * ∏ a : Without (Fin n) i, σ K ((n + a.1 + 1).bodd && e (Sum.inl a)) := by
    rw [decφ, prod_fin_split K i]
    congr 1
    · rw [slot, feed_self, σ_and_xor, σ_and_tot]
    · refine Finset.prod_congr rfl fun a _ => ?_
      rw [slot, feed_of_ne a.2]
  have h4 : (∏ t : Fin n, if t < i then -σ K (slot i l.bodd e t) else 1)
      = σ K (i : ℕ).bodd * ∏ a : Without (Fin n) i, if a.1 < i then σ K (e (Sum.inl a)) else 1 := by
    rw [prod_fin_split K i, if_neg (lt_irrefl i), one_mul, ← prod_neg_one_lt K i,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [slot, feed_of_ne a.2]
    split_ifs <;> simp
  rw [h1, h2, h3, h4, decφ]
  -- compare the factors
  have ha : ∀ a : Without (Fin n) i,
      σ K ((n - 1 + l + (posEquivF i l (n - 1 + l) h (Sum.inl a) : ℕ) + 1).bodd && e (Sum.inl a))
        * (if a.1 < i then σ K (l.bodd && e (Sum.inl a)) else 1)
      = σ K ((n + a.1 + 1).bodd && e (Sum.inl a))
        * (if a.1 < i then σ K (e (Sum.inl a)) else 1) := fun a => by
    have han := a.1.isLt
    by_cases hlt : a.1 < i
    · have hE : (posEquivF i l (n - 1 + l) h (Sum.inl a) : ℕ) = a.1 := posEquivF_inl_of_lt i h a hlt
      rw [if_pos hlt, if_pos hlt, hE]
      have hb : (n - 1 + l + (a.1 : ℕ) + 1).bodd = xor (xor (n + a.1 + 1).bodd l.bodd) true := by
        rw [bodd_congr (x := n - 1 + l + (a.1 : ℕ) + 1) (y := n + a.1 + 1 + l + 1) (a := 1)
          (b := 0) (by omega), Nat.bodd_add, Nat.bodd_add, Nat.bodd_one]
      rw [hb]
      cases (n + (a.1 : ℕ) + 1).bodd <;> cases l.bodd <;> cases e (Sum.inl a) <;> simp
    · have hgt : i < a.1 := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm a.2)
      have hE := posEquivF_inl_of_gt i h a hgt
      have hgt' : (i : ℕ) < a.1 := hgt
      rw [if_neg hlt, if_neg hlt, mul_one, mul_one]
      have hb : (n - 1 + l + (posEquivF i l (n - 1 + l) h (Sum.inl a) : ℕ) + 1).bodd
          = (n + a.1 + 1).bodd := by
        exact bodd_congr (a := 1) (b := l) (by omega)
      rw [hb]
  have ht : ∀ t : Fin l,
      σ K ((n - 1 + l + (posEquivF i l (n - 1 + l) h (Sum.inr t) : ℕ) + 1).bodd && e (Sum.inr t))
      = σ K ((n + i + 1).bodd && e (Sum.inr t)) * σ K ((l + t + 1).bodd && e (Sum.inr t)) :=
    fun t => by
      have hE : (posEquivF i l (n - 1 + l) h (Sum.inr t) : ℕ) = i + t := posEquivF_inr i h t
      rw [hE, ← σ_xor_and]
      have hb : (n - 1 + l + ((i : ℕ) + t) + 1).bodd = xor (n + i + 1).bodd (l + t + 1).bodd := by
        rw [← Nat.bodd_add]
        exact bodd_congr (a := 1) (b := 0) (by omega)
      rw [hb]
  have hconst : σ K ((l + 1).bodd && (n + i + 1).bodd) * σ K (n + 1).bodd
      = σ K ((n + i + 1).bodd && l.bodd) * σ K (i : ℕ).bodd := by
    simp only [Nat.bodd_add, Nat.bodd_one]
    cases n.bodd <;> cases l.bodd <;> cases (i : ℕ).bodd <;> simp
  calc (∏ a : Without (Fin n) i, σ K ((n - 1 + l + (posEquivF i l (n - 1 + l) h (Sum.inl a) : ℕ)
            + 1).bodd && e (Sum.inl a)))
          * (∏ t : Fin l, σ K ((n - 1 + l + (posEquivF i l (n - 1 + l) h (Sum.inr t) : ℕ)
            + 1).bodd && e (Sum.inr t)))
          * (σ K ((l + 1).bodd && (n + i + 1).bodd) * σ K (n + 1).bodd)
          * (∏ a : Without (Fin n) i, if a.1 < i then σ K (l.bodd && e (Sum.inl a)) else 1)
      = (∏ a : Without (Fin n) i,
            σ K ((n - 1 + l + (posEquivF i l (n - 1 + l) h (Sum.inl a) : ℕ) + 1).bodd
              && e (Sum.inl a)) * (if a.1 < i then σ K (l.bodd && e (Sum.inl a)) else 1))
          * (∏ t : Fin l, σ K ((n - 1 + l + (posEquivF i l (n - 1 + l) h (Sum.inr t) : ℕ)
            + 1).bodd && e (Sum.inr t)))
          * (σ K ((l + 1).bodd && (n + i + 1).bodd) * σ K (n + 1).bodd) := by
        rw [Finset.prod_mul_distrib]
        ring
    _ = (∏ a : Without (Fin n) i, σ K ((n + a.1 + 1).bodd && e (Sum.inl a))
            * (if a.1 < i then σ K (e (Sum.inl a)) else 1))
          * (∏ t : Fin l, σ K ((n + i + 1).bodd && e (Sum.inr t))
            * σ K ((l + t + 1).bodd && e (Sum.inr t)))
          * (σ K ((n + i + 1).bodd && l.bodd) * σ K (i : ℕ).bodd) := by
        rw [Finset.prod_congr rfl fun a _ => ha a, Finset.prod_congr rfl fun t _ => ht t, hconst]
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
        ring

end Signs

/-! ## The décalage -/

section Dec

/-- **The décalage** of a multilinear operation: the input `k` of `N` is twisted by the sign
involution `N + k + 1` times. -/
noncomputable def dec (N : ℕ) : EndOp K V (Fin N) →ₗ[K] EndOp K V (Fin N) :=
  GrEnd.twist K V (decφ K N)

lemma dec_apply_hom {N : ℕ} {c : Fin N → Bool} {x : Fin N → V} (hx : IsHom (R := K) c x)
    (f : EndOp K V (Fin N)) : dec N f x = decφ K N c • f x :=
  twist_apply_hom hx _ f

omit [SuperMod K V] in
/-- The inputs of a planar composite, in the two indexings. -/
lemma feed_eq_cfTuple {n l : ℕ} (i : Fin n) (h : (n - 1 + l) + 1 = n + l)
    (G : EndOp K V (Fin l)) (x : Fin (n - 1 + l) → V) :
    feed i (fun u => x (posEquivF i l (n - 1 + l) h u))
        (G fun b => x (posEquivF i l (n - 1 + l) h (Sum.inr b)))
      = End.cfTuple i G x := by
  funext s
  by_cases hs : s = i
  · subst hs
    rw [feed_self, End.cfTuple_of_eq s G x s rfl]
    exact congrArg G (funext fun t => congrArg x (Fin.ext (posEquivF_inr s h t)))
  · rw [feed_of_ne hs]
    rcases lt_or_gt_of_ne hs with hlt | hgt
    · rw [End.cfTuple_of_lt i G x s hlt]
      exact congrArg x (Fin.ext (posEquivF_inl_of_lt i h ⟨s, hs⟩ hlt))
    · rw [End.cfTuple_of_gt i G x s hgt]
      refine congrArg x (Fin.ext ?_)
      have hE : (posEquivF i l (n - 1 + l) h (Sum.inl ⟨s, hs⟩) : ℕ) + 1 = (s : ℕ) + l :=
        posEquivF_inl_of_gt i h ⟨s, hs⟩ hgt
      have hgt' : (i : ℕ) < s := hgt
      show (posEquivF i l (n - 1 + l) h (Sum.inl ⟨s, hs⟩) : ℕ) = s + l - 1
      omega

/-- **A composite in the bar convention after the décalages, on homogeneous inputs**: the
Koszul composite of the décalages of `F` and of `G`, for the opposite sign involution, is the
planar composite of `F` and `G` with the Koszul sign of the endomorphism operad, the signs of the
signed linear orders, and the décalage sign of the inputs. -/
theorem term_eq {n l : ℕ} (i : Fin n) (h : (n - 1 + l) + 1 = n + l) (F : EndOp K V (Fin n))
    (G : EndOp K V (Fin l)) (hG : parML K V l.bodd G = G) {c : Fin (n - 1 + l) → Bool}
    {x : Fin (n - 1 + l) → V} (hx : IsHom (R := K) c x) :
    End.kcompFin (-eps K V) 1 i (dec n F) (dec l G) x
      = (decφ K (n - 1 + l) c * (σ K ((l + 1).bodd && (n + i + 1).bodd) * σ K (n + 1).bodd)
          * bsg K (LinOrd.std n) i l.bodd
              (slot i l.bodd fun u => c (posEquivF i l (n - 1 + l) h u))) •
        F (feed i (fun u => x (posEquivF i l (n - 1 + l) h u))
          (G fun b => x (posEquivF i l (n - 1 + l) h (Sum.inr b)))) := by
  obtain ⟨e, he⟩ : ∃ e : Without (Fin n) i ⊕ Fin l → Bool,
      e = fun u => c (posEquivF i l (n - 1 + l) h u) := ⟨_, rfl⟩
  have hxE : IsHom (R := K) e fun u => x (posEquivF i l (n - 1 + l) h u) := fun u => by
    rw [he]
    exact hx _
  have hy₀ : IsHom (R := K) (slot i l.bodd e) (End.cfTuple i G x) := by
    rw [← feed_eq_cfTuple i h G x]
    exact isHom_feed i hxE hG
  have hin : IsHom (R := K) (fun t => e (Sum.inr t))
      fun b => x (posEquivF i l (n - 1 + l) h (Sum.inr b)) := fun b => hxE (Sum.inr b)
  -- the inputs of the outer operation
  have hy : (fun t => End.twistFn (-eps K V) 1 i t (End.cfTuple i (dec l G) x t))
      = fun t => ((if t < i then -σ K (slot i l.bodd e t) else 1)
          * (if t = i then decφ K l (fun t => e (Sum.inr t)) else 1)) • End.cfTuple i G x t := by
    funext t
    rcases lt_trichotomy t i with hlt | heq | hgt
    · rw [End.twistFn_of_lt _ 1 i t hlt, if_pos hlt, if_neg (ne_of_lt hlt), mul_one,
        End.cfTuple_of_lt i _ x t hlt, pow_one, LinearMap.neg_apply]
      have h1 := eps_apply_hom (K := K) (hy₀ t)
      rw [End.cfTuple_of_lt i G x t hlt] at h1
      rw [h1, neg_smul, End.cfTuple_of_lt i G x t hlt]
    · subst heq
      rw [End.twistFn_of_ge _ 1 (t : ℕ) t le_rfl, if_neg (lt_irrefl t), if_pos rfl, one_mul,
        End.cfTuple_of_eq t _ x t rfl, End.cfTuple_of_eq t G x t rfl, LinearMap.id_apply]
      have h2 : (fun s : Fin l => x ⟨(t : ℕ) + s, by have := s.isLt; have := t.isLt; omega⟩)
          = fun b => x (posEquivF t l (n - 1 + l) h (Sum.inr b)) :=
        funext fun s => congrArg x (Fin.ext (posEquivF_inr t h s).symm)
      rw [h2]
      exact dec_apply_hom hin G
    · rw [End.twistFn_of_ge _ 1 i t (le_of_lt hgt), if_neg (not_lt.2 (le_of_lt hgt)),
        if_neg (ne_of_gt hgt), one_mul, one_smul, End.cfTuple_of_gt i _ x t hgt,
        End.cfTuple_of_gt i G x t hgt, LinearMap.id_apply]
  have hprod : ∏ t : Fin n, ((if t < i then -σ K (slot i l.bodd e t) else 1)
      * (if t = i then decφ K l (fun t => e (Sum.inr t)) else 1))
      = (∏ t : Fin n, if t < i then -σ K (slot i l.bodd e t) else 1)
        * decφ K l (fun t => e (Sum.inr t)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i, if_pos (Finset.mem_univ i)]
  have hsign := sign_core K i h e
  have hce : (fun k => e ((posEquivF i l (n - 1 + l) h).symm k)) = c := by
    rw [he]
    funext k
    show c (posEquivF i l (n - 1 + l) h ((posEquivF i l (n - 1 + l) h).symm k)) = c k
    rw [Equiv.apply_symm_apply]
  rw [hce] at hsign
  rw [End.kcompFin, End.compFin_apply, End.twist_apply, hy, MultilinearMap.map_smul_univ,
    dec_apply_hom hy₀, hprod, smul_smul, feed_eq_cfTuple i h G x, ← he, hsign]
  congr 1
  ring

end Dec

/-! ## The planar terms of the convolution product in the endomorphism operad -/

section Terms

open OrdCo

omit [Field K] in
/-- There are `n - 1 - i` inputs after the input `i` of `n`. -/
lemma aftN_std {n : ℕ} (i : Fin n) : NOrd.aftN (LinOrd.std n) i + i + 1 = n := by
  classical
  have h1 : NOrd.aftN (LinOrd.std n) i = (Finset.Ioi i).card := by
    rw [NOrd.aftN, ← Finset.card_filter]
    exact congrArg Finset.card (by
      ext b
      simp [LinOrd.std_lt])
  have h2 := Fin.card_Ioi i
  have h3 := i.isLt
  omega

/-- **A planar term of the convolution product in the endomorphism operad, on homogeneous
inputs**: up to the décalage sign of the inputs, the Koszul composite in the bar convention of the
décalages of the two operations. -/
theorem sv_plT (f g : GrOperad.Inv K (ConvOp K (OrdCo K) (EndGr K V))) (j m : ℕ)
    (i : Fin (j + 1))
    (hg : parML K V (m + 1).bodd (EndGr.sv (famOf g m)) = EndGr.sv (famOf g m))
    {l N : ℕ} (hl : l = m + 1) (h : N + 1 = (j + 1) + l) (hlpos : 0 < l)
    {c : Fin N → Bool} {x : Fin N → V} (hx : IsHom (R := K) c x) :
    EndGr.sv (NOrd.plT f g i l N h hlpos) x
      = decφ K N c • (AInf.acast (End.kcompFin (-eps K V) 1 i
          (dec (j + 1) (EndGr.sv (famOf f j))) (dec (m + 1) (EndGr.sv (famOf g m)))) :
            End K V N) x := by
  subst hl
  obtain rfl : N = j + 1 - 1 + (m + 1) := by omega
  rw [AInf.acast_self, term_eq i h _ _ hg hx]
  have htw : GrSpecies.tw (R := K) true (SgnLin.bas NOrd.sgnD K (NOrd.std (j + 1) (Fin.pos i)))
      = σ K (j + 1 + 1).bodd • SgnLin.bas NOrd.sgnD K (NOrd.std (j + 1) (Fin.pos i)) := by
    refine (GrSpecies.tw_hom true (SgnLin.par_bas (R := K) (δ := NOrd.sgnD)
      (NOrd.std (j + 1) (Fin.pos i)))).trans ?_
    show σ K (true && (Fintype.card (Fin (j + 1)) + 1).bodd) • _ = _
    rw [Fintype.card_fin, Bool.true_and]
  have hsgn : SgnData.sgn i (NOrd.sgnD.app (Fin (j + 1)) (NOrd.std (j + 1) (Fin.pos i)))
      (NOrd.sgnD.app (Fin (m + 1)) (NOrd.std (m + 1) hlpos))
      = ((m + 1 + 1).bodd && (j + 1 + i + 1).bodd) := by
    show ((Fintype.card (Fin (m + 1)) + 1).bodd && (NOrd.aftN (LinOrd.std (j + 1)) i).bodd) = _
    rw [Fintype.card_fin, bodd_congr (x := NOrd.aftN (LinOrd.std (j + 1)) i) (y := j + 1 + i + 1)
      (a := (i : ℕ) + 1) (b := 0) (by have := aftN_std i; omega)]
  have hpl : NOrd.plT f g i (m + 1) (j + 1 - 1 + (m + 1)) h hlpos
      = (σ K ((m + 1 + 1).bodd && (j + 1 + i + 1).bodd) * σ K (j + 1 + 1).bodd) •
        GrOperad.map (R := K) (posEquivF i (m + 1) (j + 1 - 1 + (m + 1)) h)
          (GrOperad.comp (R := K) i (famOf f j) (famOf g m)) := by
    rw [NOrd.plT, SgnLin.repW, htw, hsgn]
    simp only [map_smul, LinearMap.smul_apply, smul_smul]
    rfl
  rw [hpl]
  show (σ K ((m + 1 + 1).bodd && (j + 1 + i + 1).bodd) * σ K (j + 1 + 1).bodd) •
    EndGr.sv (GrOperad.map (R := K) (posEquivF i (m + 1) (j + 1 - 1 + (m + 1)) h)
      (GrOperad.comp (R := K) i (famOf f j) (famOf g m))) x = _
  rw [sv_map_comp i h (famOf f j) (famOf g m) hg hx, smul_smul, smul_smul]
  congr 1
  have hd := decφ_mul_self K (j + 1 - 1 + (m + 1)) c
  linear_combination (σ K ((m + 1 + 1).bodd && (j + 1 + i + 1).bodd) * σ K (j + 1 + 1).bodd
    * bsg K (LinOrd.std (j + 1)) i (m + 1).bodd
      (slot i (m + 1).bodd fun u => c (posEquivF i (m + 1) (j + 1 - 1 + (m + 1)) h u))) * (-hd)

end Terms

/-! ## The convolution product in the endomorphism operad is the `A∞` product -/

section Star

open OrdCo

/-- **The family in the bar convention** of an invariant family on the signed linear orders with
values in the endomorphism operad: the décalages of its operations at the standard orders. -/
noncomputable def barFam (f : GrOperad.Inv K (ConvOp K (OrdCo K) (EndGr K V))) : AInf.Fam K V :=
  fun j => dec (j + 1) (EndGr.sv (famOf f j))

lemma sv_sum {N : ℕ} {ι : Type*} (s : Finset ι) (F : ι → EndGr K V (Fin N)) :
    EndGr.sv (∑ x ∈ s, F x) = ∑ x ∈ s, EndGr.sv (F x) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EndGr.sv_add, ih]

/-- The operations of an odd invariant family have the parity of their arity. -/
lemma parML_famOf {g : GrOperad.Inv K (ConvOp K (OrdCo K) (EndGr K V))}
    (hg : GrOperad.Inv.IsPar true g) (m : ℕ) :
    parML K V (m + 1).bodd (EndGr.sv (famOf g m)) = EndGr.sv (famOf g m) := by
  rw [← EndGr.sv_par]
  exact congrArg EndGr.sv ((isPar_iff g).1 hg m)

/-- **The convolution product at a standard order is the product of `A∞`-structures**: for
invariant families `f`, `g` on the signed linear orders with values in the endomorphism operad,
`g` odd, the value of `f ⋆ g` at the standard order on `n + 1` inputs is the décalage of the
`n`-th component of the Koszul product of the families in the bar convention, for the opposite
sign involution. -/
theorem sv_star (f g : GrOperad.Inv K (ConvOp K (OrdCo K) (EndGr K V)))
    (hg : GrOperad.Inv.IsPar true g) (n : ℕ) :
    EndGr.sv (ConvOp.toLin ((GrOperad.Inv.star K _ f g).1 (Fin (n + 1)))
        (SgnLin.bas NOrd.sgnD K (sd n)))
      = dec (n + 1) (AInf.tstar (-eps K V) 1 (barFam f) (barFam g) n) := by
  have hodd : ∀ (B : Type) [Fintype B] [DecidableEq B], ConvOp.IsParC true (g.1 B) :=
    fun B _ _ => ConvOp.parC_eq_self_iff.1 (hg B)
  refine ext_hom fun c x hx => ?_
  rw [NOrd.star_std f g hodd (n + 1) n.succ_pos, sv_sum, MultilinearMap.sum_apply,
    dec_apply_hom hx, AInf.tstar_apply, MultilinearMap.sum_apply, Finset.smul_sum, NOrd.idx,
    Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [End.kstar, AInf.acast_sum, MultilinearMap.sum_apply, Finset.smul_sum,
    ← Finset.sum_filter,
    show (Finset.range (n + 1)).filter (fun i => i ≤ j) = Finset.range (j + 1) from by
      ext i
      rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range]
      omega,
    Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (i : ℕ) ≤ j ∧ j < n + 1 := ⟨Nat.lt_succ_iff.1 i.isLt, by omega⟩
  rw [NOrd.plTN, dif_pos hi]
  exact sv_plT f g j (n - j) i (parML_famOf hg _) (by omega) _ _ hx

end Star

/-! ## The inner differential, in planar terms -/

section Inner

variable {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (P A)] [GrOperad K P]

omit [SuperMod K V] in
/-- **Composing an operation of arity one on the left, in planar terms.** -/
lemma lcomp_eq_planar (D : P Unit) {N : ℕ} (h : N + 1 = 1 + N) (F : P (Fin N)) :
    GrOperad.lcomp K D F = GrOperad.map (R := K) (posEquivF (0 : Fin 1) N N h)
      (GrOperad.comp (R := K) (0 : Fin 1) (GrOperad.map (R := K) unitFinOne D) F) := by
  have h1 := GrOperad.map_comp (R := K) unitFinOne (Equiv.refl (Fin N)) () D F
  rw [GrOperad.map_refl] at h1
  have h2 : (GrOperad.comp (R := K) (0 : Fin 1) (GrOperad.map (R := K) unitFinOne D) F)
      = GrOperad.map (R := K) (compEquiv unitFinOne (Equiv.refl (Fin N)) ())
        (GrOperad.comp (R := K) () D F) := h1.symm
  have h3 : GrOperad.map (R := K) (posEquivF (0 : Fin 1) N N h)
      (GrOperad.map (R := K) (compEquiv unitFinOne (Equiv.refl (Fin N)) ())
        (GrOperad.comp (R := K) () D F))
      = GrOperad.map (R := K) ((compEquiv unitFinOne (Equiv.refl (Fin N)) ()).trans
          (posEquivF (0 : Fin 1) N N h)) (GrOperad.comp (R := K) () D F) :=
    (GrOperad.map_trans (R := K) _ _ _).symm
  rw [h2, h3, GrOperad.lcomp_apply]
  refine congrArg (fun E => GrOperad.map (R := K) E (GrOperad.comp (R := K) () D F))
    (Equiv.ext ?_)
  rintro (⟨u, hu⟩ | b)
  · exact absurd rfl hu
  · refine Fin.ext ?_
    show (b : ℕ) = (posEquivF (0 : Fin 1) N N h (Sum.inr b) : ℕ)
    rw [posEquivF_inr]
    simp

omit [SuperMod K V] in
/-- **Composing an operation of arity one at an input, in planar terms.** -/
lemma rcomp_eq_planar (D : P Unit) {N : ℕ} (a : Fin N) (h : N + 1 = N + 1) (F : P (Fin N)) :
    GrOperad.rcomp K D a F = GrOperad.map (R := K) (posEquivF a 1 N h)
      (GrOperad.comp (R := K) a F (GrOperad.map (R := K) unitFinOne D)) := by
  have h1 := GrOperad.map_comp (R := K) (Equiv.refl (Fin N)) unitFinOne a F D
  rw [GrOperad.map_refl] at h1
  have h2 : GrOperad.comp (R := K) a F (GrOperad.map (R := K) unitFinOne D)
      = GrOperad.map (R := K) (compEquiv (Equiv.refl (Fin N)) unitFinOne a)
        (GrOperad.comp (R := K) a F D) := h1.symm
  have h3 : GrOperad.map (R := K) (posEquivF a 1 N h)
      (GrOperad.map (R := K) (compEquiv (Equiv.refl (Fin N)) unitFinOne a)
        (GrOperad.comp (R := K) a F D))
      = GrOperad.map (R := K) ((compEquiv (Equiv.refl (Fin N)) unitFinOne a).trans
          (posEquivF a 1 N h)) (GrOperad.comp (R := K) a F D) :=
    (GrOperad.map_trans (R := K) _ _ _).symm
  rw [h2, h3, GrOperad.rcomp_apply]
  refine congrArg (fun E => GrOperad.map (R := K) E (GrOperad.comp (R := K) a F D))
    (Equiv.ext ?_)
  rintro (x | u)
  · refine Fin.ext ?_
    show (x.1 : ℕ) = (posEquivF a 1 N h (Sum.inl ⟨x.1, x.2⟩) : ℕ)
    rcases lt_or_gt_of_ne x.2 with hlt | hgt
    · exact (posEquivF_inl_of_lt a h ⟨x.1, x.2⟩ hlt).symm
    · have hE : (posEquivF a 1 N h (Sum.inl ⟨x.1, x.2⟩) : ℕ) + 1 = (x.1 : ℕ) + 1 :=
        posEquivF_inl_of_gt a h ⟨x.1, x.2⟩ hgt
      omega
  · refine Fin.ext ?_
    show (a : ℕ) = (posEquivF a 1 N h (Sum.inr (unitFinOne u)) : ℕ)
    rw [posEquivF_inr]
    rfl

omit [SuperMod K V] in
/-- **A planar term of the convolution product**, in terms of the operations of the two
families. -/
lemma plT_eq (f g : GrOperad.Inv K (ConvOp K (OrdCo K) P)) (j m : ℕ) (i : Fin (j + 1))
    {l N : ℕ} (hl : l = m + 1) (h : N + 1 = (j + 1) + l) (hlpos : 0 < l) :
    NOrd.plT f g i l N h hlpos
      = (σ K ((m + 1 + 1).bodd && (j + 1 + i + 1).bodd) * σ K (j + 1 + 1).bodd) •
        GrOperad.map (R := K) (posEquivF i (m + 1) N (hl ▸ h))
          (GrOperad.comp (R := K) i (OrdCo.famOf f j) (OrdCo.famOf g m)) := by
  subst hl
  have htw : GrSpecies.tw (R := K) true (SgnLin.bas NOrd.sgnD K (NOrd.std (j + 1) (Fin.pos i)))
      = σ K (j + 1 + 1).bodd • SgnLin.bas NOrd.sgnD K (NOrd.std (j + 1) (Fin.pos i)) := by
    refine (GrSpecies.tw_hom true (SgnLin.par_bas (R := K) (δ := NOrd.sgnD)
      (NOrd.std (j + 1) (Fin.pos i)))).trans ?_
    show σ K (true && (Fintype.card (Fin (j + 1)) + 1).bodd) • _ = _
    rw [Fintype.card_fin, Bool.true_and]
  have hsgn : SgnData.sgn i (NOrd.sgnD.app (Fin (j + 1)) (NOrd.std (j + 1) (Fin.pos i)))
      (NOrd.sgnD.app (Fin (m + 1)) (NOrd.std (m + 1) hlpos))
      = ((m + 1 + 1).bodd && (j + 1 + i + 1).bodd) := by
    show ((Fintype.card (Fin (m + 1)) + 1).bodd && (NOrd.aftN (LinOrd.std (j + 1)) i).bodd) = _
    rw [Fintype.card_fin, bodd_congr (x := NOrd.aftN (LinOrd.std (j + 1)) i) (y := j + 1 + i + 1)
      (a := (i : ℕ) + 1) (b := 0) (by have := aftN_std i; omega)]
  rw [NOrd.plT, SgnLin.repW, htw, hsgn]
  simp only [map_smul, LinearMap.smul_apply, smul_smul]
  rfl

end Inner

/-! ## The differential as a convolution with the family of the differential -/

section Diff

open OrdCo

variable [DGSuperMod K V]

variable (K V) in
/-- **The differential of `V`**, as an operation of the endomorphism operad on one input. -/
noncomputable def D1 : EndGr K V (Fin 1) := GrOperad.map (R := K) unitFinOne (EndGr.dE K V)

variable (K V) in
/-- **The invariant family of the differential**: the differential at the standard order on one
input, and zero at the other standard orders. -/
noncomputable def dInv : GrOperad.Inv K (ConvOp K (OrdCo K) (EndGr K V)) :=
  ofFam (K := K) (Pi.single (M := fun n : ℕ => EndGr K V (Fin (n + 1))) 0 (D1 K V))

lemma famOf_dInv_zero : famOf (dInv K V) 0 = D1 K V := by
  have h := congrFun ((invEquiv (K := K) (Q := EndGr K V)).right_inv
    (Pi.single (M := fun n : ℕ => EndGr K V (Fin (n + 1))) 0 (D1 K V))) 0
  rw [Pi.single_eq_same] at h
  exact h

lemma famOf_dInv_ne {n : ℕ} (hn : n ≠ 0) : famOf (dInv K V) n = 0 := by
  have h := congrFun ((invEquiv (K := K) (Q := EndGr K V)).right_inv
    (Pi.single (M := fun n : ℕ => EndGr K V (Fin (n + 1))) 0 (D1 K V))) n
  rw [Pi.single_eq_of_ne hn] at h
  exact h

lemma isPar_dInv : GrOperad.Inv.IsPar true (dInv K V) := by
  refine (isPar_iff _).2 fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [famOf_dInv_zero, D1, ← GrOperad.map_par]
    show GrOperad.map (R := K) unitFinOne (GrOperad.par (R := K) true (EndGr.dE K V)) = _
    rw [EndGr.dE_odd]
  · rw [famOf_dInv_ne (by omega), map_zero]

/-- **The convolution with the family of the differential on the left** is the composite with
the differential. -/
theorem star_dInv_left (g : GrOperad.Inv K (ConvOp K (OrdCo K) (EndGr K V)))
    (hg : GrOperad.Inv.IsPar true g) (n : ℕ) :
    ConvOp.toLin ((GrOperad.Inv.star K _ (dInv K V) g).1 (Fin (n + 1)))
        (SgnLin.bas NOrd.sgnD K (sd n))
      = GrOperad.lcomp K (EndGr.dE K V) (famOf g n) := by
  have hodd : ∀ (B : Type) [Fintype B] [DecidableEq B], ConvOp.IsParC true (g.1 B) :=
    fun B _ _ => ConvOp.parC_eq_self_iff.1 (hg B)
  rw [NOrd.star_std (dInv K V) g hodd (n + 1) n.succ_pos, Finset.sum_eq_single (0, 0)]
  · rw [NOrd.plTN, dif_pos ⟨le_rfl, n.succ_pos⟩,
      plT_eq (dInv K V) g 0 n _ (show n + 1 - 0 = n + 1 from rfl), famOf_dInv_zero,
      lcomp_eq_planar (EndGr.dE K V) (by omega) (famOf g n)]
    have hs : σ K ((n + 1 + 1).bodd && (0 + 1 + ((⟨0, Nat.lt_succ_of_le le_rfl⟩ : Fin (0 + 1)) : ℕ)
        + 1).bodd) * σ K (0 + 1 + 1).bodd = 1 := by
      rw [show ((0 : ℕ) + 1 + ((⟨0, Nat.lt_succ_of_le le_rfl⟩ : Fin (0 + 1)) : ℕ) + 1).bodd
        = false from rfl, show ((0 : ℕ) + 1 + 1).bodd = false from rfl, Bool.and_false, σ_false,
        one_mul]
    rw [hs, one_smul]
    rfl
  · rintro ⟨j, i⟩ hb hne
    obtain ⟨hij, hjn⟩ := NOrd.mem_idx.1 hb
    have hj : j ≠ 0 := fun h0 => hne (by
      simp only at hij h0
      subst h0
      rw [Nat.le_zero.1 hij])
    rw [NOrd.plTN, dif_pos ⟨hij, hjn⟩,
      plT_eq (dInv K V) g j (n - j) _ (show n + 1 - j = n - j + 1 by simp only at hjn; omega),
      famOf_dInv_ne hj, LinearMap.map_zero₂, map_zero, smul_zero]
  · intro h
    exact absurd (NOrd.mem_idx.2 ⟨le_rfl, n.succ_pos⟩) h

/-- **The convolution with the family of the differential on the right** is the sum of the
composites with the differential at the inputs. -/
theorem star_dInv_right (f : GrOperad.Inv K (ConvOp K (OrdCo K) (EndGr K V))) (n : ℕ) :
    ConvOp.toLin ((GrOperad.Inv.star K _ f (dInv K V)).1 (Fin (n + 1)))
        (SgnLin.bas NOrd.sgnD K (sd n))
      = σ K (n + 1 + 1).bodd • ∑ a : Fin (n + 1), GrOperad.rcomp K (EndGr.dE K V) a (famOf f n)
    := by
  have hodd : ∀ (B : Type) [Fintype B] [DecidableEq B],
      ConvOp.IsParC true ((dInv K V).1 B) :=
    fun B _ _ => ConvOp.parC_eq_self_iff.1 (isPar_dInv B)
  rw [NOrd.star_std f (dInv K V) hodd (n + 1) n.succ_pos, NOrd.idx, Finset.sum_filter,
    Finset.sum_product, Finset.sum_eq_single n]
  · rw [← Finset.sum_filter,
      show (Finset.range (n + 1)).filter (fun i => i ≤ n) = Finset.range (n + 1) from by
        ext i
        rw [Finset.mem_filter, Finset.mem_range]
        omega,
      Finset.sum_range, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : (i : ℕ) ≤ n ∧ n < n + 1 := ⟨Nat.lt_succ_iff.1 i.isLt, Nat.lt_succ_self n⟩
    rw [NOrd.plTN, dif_pos hi,
      plT_eq f (dInv K V) n 0 _ (show n + 1 - n = 0 + 1 by omega), famOf_dInv_zero,
      show ((0 : ℕ) + 1 + 1).bodd = false from rfl, Bool.false_and, σ_false, one_mul,
      rcomp_eq_planar (EndGr.dE K V) i rfl (famOf f n)]
    rfl
  · intro j hj hjn
    have hjn' : j < n := lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) hjn
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with hij
    · rw [NOrd.plTN, dif_pos ⟨hij, by omega⟩,
        plT_eq f (dInv K V) j (n - j) _ (show n + 1 - j = n - j + 1 by omega),
        famOf_dInv_ne (by omega), map_zero, map_zero, smul_zero]
    · rfl
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h

end Diff

/-! ## The Maurer–Cartan equation is the `A∞` relation -/

section MC

open OrdCo

/-- The décalage is an involution. -/
lemma dec_dec (N : ℕ) (f : EndOp K V (Fin N)) : dec N (dec N f) = f :=
  ext_hom fun c x hx => by
    rw [dec_apply_hom hx, dec_apply_hom hx, smul_smul, decφ_mul_self, one_smul]

lemma dec_eq_zero {N : ℕ} {f : EndOp K V (Fin N)} (h : dec N f = 0) : f = 0 := by
  rw [← dec_dec N f, h, map_zero]

variable [DGSuperMod K V]

/-- **The differential of an operation of an odd family is its convolution commutator with the
family of the differential.** -/
theorem d_famOf (α : GrOperad.Inv K (ConvOp K (OrdCo K) (EndGr K V)))
    (hα : GrOperad.Inv.IsPar true α) (n : ℕ) :
    DGOperad.d (R := K) (famOf α n)
      = ConvOp.toLin ((GrOperad.Inv.star K _ (dInv K V) α).1 (Fin (n + 1)))
          (SgnLin.bas NOrd.sgnD K (sd n))
        + ConvOp.toLin ((GrOperad.Inv.star K _ α (dInv K V)).1 (Fin (n + 1)))
          (SgnLin.bas NOrd.sgnD K (sd n)) := by
  have hpar := (isPar_iff α).1 hα n
  rw [star_dInv_left α hα n, star_dInv_right α n, EndGr.d_eq, GrOperad.innerL_apply,
    GrOperad.tw_hom true hpar, sub_eq_add_neg]
  congr 1
  rw [← Finset.sum_neg_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, ← neg_smul]
  congr 1
  rw [Nat.bodd_succ (n + 1)]
  cases (n + 1).bodd <;> simp

/-- The family of the differential squares to zero. -/
theorem star_dInv_dInv (n : ℕ) :
    ConvOp.toLin ((GrOperad.Inv.star K _ (dInv K V) (dInv K V)).1 (Fin (n + 1)))
      (SgnLin.bas NOrd.sgnD K (sd n)) = 0 := by
  rw [star_dInv_left (dInv K V) isPar_dInv n]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [famOf_dInv_zero, D1, GrOperad.lcomp_apply]
    have h1 := GrOperad.map_comp (R := K) (Equiv.refl Unit) unitFinOne ()
      (EndGr.dE K V) (EndGr.dE K V)
    rw [GrOperad.map_refl, EndGr.dE_comp_dE] at h1
    have h2 : GrOperad.comp (R := K) () (EndGr.dE K V)
        (GrOperad.map (R := K) unitFinOne (EndGr.dE K V)) = 0 :=
      h1.symm.trans (LinearMap.map_zero _)
    rw [h2]
    exact LinearMap.map_zero _
  · rw [famOf_dInv_ne (by omega), map_zero]

/-- **The Maurer–Cartan expression at a standard order is a convolution square**: that of the
family with the family of the differential added. -/
theorem mc_eq_star (α : GrOperad.Inv K (ConvOp K (OrdCo K) (EndGr K V)))
    (hα : GrOperad.Inv.IsPar true α) (n : ℕ) :
    DGOperad.d (R := K) (famOf α n)
        + ConvOp.toLin ((GrOperad.Inv.star K _ α α).1 (Fin (n + 1)))
          (SgnLin.bas NOrd.sgnD K (sd n))
      = ConvOp.toLin ((GrOperad.Inv.star K _ (α + dInv K V) (α + dInv K V)).1 (Fin (n + 1)))
          (SgnLin.bas NOrd.sgnD K (sd n)) := by
  have h : GrOperad.Inv.star K _ (α + dInv K V) (α + dInv K V)
      = (GrOperad.Inv.star K _ α α + GrOperad.Inv.star K _ α (dInv K V))
        + (GrOperad.Inv.star K _ (dInv K V) α
          + GrOperad.Inv.star K _ (dInv K V) (dInv K V)) := by
    simp only [map_add, LinearMap.add_apply]
    abel
  have hadd : ∀ q q' : GrOperad.Inv K (ConvOp K (OrdCo K) (EndGr K V)),
      ConvOp.toLin ((q + q').1 (Fin (n + 1))) (SgnLin.bas NOrd.sgnD K (sd n))
        = ConvOp.toLin (q.1 (Fin (n + 1))) (SgnLin.bas NOrd.sgnD K (sd n))
          + ConvOp.toLin (q'.1 (Fin (n + 1))) (SgnLin.bas NOrd.sgnD K (sd n)) :=
    fun _ _ => rfl
  rw [h, hadd, hadd, hadd, star_dInv_dInv, add_zero, d_famOf α hα n]
  abel

/-- **The Maurer–Cartan equation in the endomorphism operad is the `A∞` relation**: for an odd
invariant family `α` on the signed linear orders with values in the endomorphism operad of a dg
super module, the planar Maurer–Cartan equations hold iff the family in the bar convention of
`α` with the differential added squares to zero for the Koszul product, for the opposite sign
involution. -/
theorem mc_iff_tstar (α : GrOperad.Inv K (ConvOp K (OrdCo K) (EndGr K V)))
    (hα : GrOperad.Inv.IsPar true α) :
    (∀ n, DGOperad.d (R := K) (famOf α n)
        + ∑ x ∈ NOrd.idx (n + 1), NOrd.plTN α α (n + 1) x = 0)
      ↔ AInf.tstar (-eps K V) 1 (barFam (α + dInv K V)) (barFam (α + dInv K V)) = 0 := by
  have hodd : ∀ (B : Type) [Fintype B] [DecidableEq B], ConvOp.IsParC true (α.1 B) :=
    fun B _ _ => ConvOp.parC_eq_self_iff.1 (hα B)
  have hα' : GrOperad.Inv.IsPar true (α + dInv K V) := fun A _ _ => by
    show GrOperad.par (R := K) true (α.1 A + (dInv K V).1 A) = α.1 A + (dInv K V).1 A
    rw [map_add, hα A, isPar_dInv A]
  have key : ∀ n, (DGOperad.d (R := K) (famOf α n)
        + ∑ x ∈ NOrd.idx (n + 1), NOrd.plTN α α (n + 1) x = 0)
      ↔ AInf.tstar (-eps K V) 1 (barFam (α + dInv K V)) (barFam (α + dInv K V)) n = 0 :=
    fun n => by
      rw [← NOrd.star_std α α hodd (n + 1) n.succ_pos, mc_eq_star α hα n, EndGr.eq_zero_iff_sv,
        sv_star _ _ hα' n]
      exact ⟨dec_eq_zero, fun h => by rw [h, map_zero]⟩
  exact ⟨fun h => funext fun n => (key n).1 (h n), fun h n => (key n).2 (congrFun h n)⟩

end MC

end PInfAss

end Operad
