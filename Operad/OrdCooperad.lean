/-
# The set operad of nonempty linear orders and its sign data

The nonempty linear orders on finite sets are a set operad (`NOrd`, a suboperad of the linear
orders), with finite factorizations and whose units only factor into units. A linear order
carries the sign data of the planar binary trees with that order of leaves (`NOrd.sgnD`): the
parity after an input is that of the number of inputs after it (`NOrd.aftN`), and the total
parity is that of the number of inputs minus one. The data are compatible with relabelling and
with composition, so they are a morphism of set operads to `SgnD`.

The twisted linearization `SgnLin K NOrd.sgnD` is then a graded operad and a coaugmented graded
cooperad (`SgnLin.instGrOperad`, `SgnLin.instGrCooperad`, `SgnLin.instCoaug`): the cooperad of
signed linear orders, `OrdCo K` in `Operad/OrdCut.lean`. Its decomposition sums over the
factorizations of an order, an interval and the order with the interval contracted, with the
sign `(-1)^((|interval| - 1) (number of inputs after it))`.
-/
import Operad.GrDecCooperad

universe u

namespace Operad

open Sym GerBV
open scoped TensorProduct

/-! ## The set operad of nonempty linear orders -/

/-- **A linear order on a nonempty set of inputs.** -/
@[nolint unusedArguments]
def NOrd (A : Type) [Fintype A] [DecidableEq A] : Type := {_L : LinOrd A // Nonempty A}

namespace NOrd

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

local notation "𝕃" => (fun (A : Type) [Fintype A] [DecidableEq A] => LinOrd A)

/-- **The set operad of nonempty linear orders**: a suboperad of the linear orders. -/
instance instSetOperad : SetOperad NOrd where
  map e x := ⟨SetOperad.map (S := 𝕃) e x.1, x.2.map e⟩
  map_refl x := Subtype.ext (SetOperad.map_refl (S := 𝕃) x.1)
  map_trans e f x := Subtype.ext (SetOperad.map_trans (S := 𝕃) e f x.1)
  one := ⟨LinOrd.one, ⟨()⟩⟩
  comp i x y := ⟨LinOrd.comp i x.1 y.1, y.2.map Sum.inr⟩
  map_comp σ τ i x y := Subtype.ext (SetOperad.map_comp (S := 𝕃) σ τ i x.1 y.1)
  comp_one i x := Subtype.ext (SetOperad.comp_one (S := 𝕃) i x.1)
  one_comp y := Subtype.ext (SetOperad.one_comp (S := 𝕃) y.1)
  comp_assoc_seq i j x y z := Subtype.ext (SetOperad.comp_assoc_seq (S := 𝕃) i j x.1 y.1 z.1)
  comp_assoc_par hik x y z := Subtype.ext (SetOperad.comp_assoc_par (S := 𝕃) hik x.1 y.1 z.1)

@[simp] lemma map_val (e : A ≃ B) (x : NOrd A) : (SetOperad.map e x).1 = LinOrd.map e x.1 := rfl

@[simp] lemma one_val : (SetOperad.one : NOrd Unit).1 = LinOrd.one := rfl

@[simp] lemma comp_val (i : A) (x : NOrd A) (y : NOrd B) :
    (SetOperad.comp i x y).1 = LinOrd.comp i x.1 y.1 := rfl

instance instFinite : Finite (NOrd A) :=
  haveI : Finite (LinOrd A) := Finite.of_injective (fun L : LinOrd A => L.lt) fun _ _ h =>
    LinOrd.ext fun a b => Iff.of_eq (congrFun (congrFun h a) b)
  inferInstanceAs (Finite {_L : LinOrd A // Nonempty A})

instance instFiniteFact : SetOperad.FiniteFact NOrd where
  finite _ _ := Set.toFinite _

instance instUnitFact : SetOperad.UnitFact NOrd where
  fact {A B} _ _ _ _ i e p q _ := by
    haveI : Subsingleton (Without A i ⊕ B) := e.symm.subsingleton
    obtain ⟨b₀⟩ := q.2
    have hA : ∀ a : A, a = i := fun a => by
      by_contra ha
      exact Sum.inl_ne_inr (Subsingleton.elim (Sum.inl ⟨a, ha⟩ : Without A i ⊕ B) (Sum.inr b₀))
    have hB : ∀ b b' : B, b = b' := fun b b' =>
      Sum.inr_injective (Subsingleton.elim (Sum.inr b : Without A i ⊕ B) (Sum.inr b'))
    refine ⟨⟨⟨fun _ => i, fun _ => (), fun _ => rfl, fun a => (hA a).symm⟩,
        Subtype.ext (LinOrd.ext fun a a' => ?_)⟩,
      ⟨⟨fun _ => b₀, fun _ => (), fun _ => rfl, fun b => hB _ _⟩,
        Subtype.ext (LinOrd.ext fun b b' => ?_)⟩⟩
    · rw [hA a, hA a']
      exact ⟨fun h => (p.1.irrefl _ h).elim, fun h => h.elim⟩
    · rw [hB b b']
      exact ⟨fun h => (q.1.irrefl _ h).elim, fun h => h.elim⟩

/-! ## The sign data of a linear order -/

open Classical in
/-- The number of inputs after an input. -/
noncomputable def aftN (L : LinOrd A) (a : A) : ℕ := ∑ b, if L.lt a b then 1 else 0

lemma sum_without (i : A) (f : A → ℕ) : ∑ a : Without A i, f a.1 + f i = ∑ a, f a := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  congr 1
  exact (Finset.sum_subtype (Finset.univ.erase i) (fun a => by simp) f).symm

omit [DecidableEq A] [DecidableEq B] in
lemma aftN_map (e : A ≃ B) (L : LinOrd A) (b : B) :
    aftN (LinOrd.map e L) b = aftN L (e.symm b) := by
  classical
  unfold aftN
  exact Equiv.sum_comp e.symm fun a => if L.lt (e.symm b) a then 1 else 0

lemma aftN_one (u : Unit) : aftN LinOrd.one u = 0 := by
  classical
  unfold aftN
  exact Finset.sum_eq_zero fun _ _ => if_neg id

omit [DecidableEq B] in
open Classical in
lemma aftN_comp_inl (i : A) (L : LinOrd A) (M : LinOrd B) (a : Without A i) :
    aftN (LinOrd.comp i L M) (.inl a) + (if L.lt a.1 i then 1 else 0)
      = aftN L a.1 + if L.lt a.1 i then Fintype.card B else 0 := by
  classical
  unfold aftN
  rw [Fintype.sum_sum_type, ← sum_without i]
  simp only [LinOrd.comp_lt, LinOrd.compLt_inl_inl, LinOrd.compLt_inl_inr]
  by_cases h : L.lt a.1 i
  · simp only [if_pos h, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
    omega
  · simp only [if_neg h, Finset.sum_const_zero, add_zero]

omit [DecidableEq B] in
lemma aftN_comp_inr (i : A) (L : LinOrd A) (M : LinOrd B) (b : B) :
    aftN (LinOrd.comp i L M) (.inr b) = aftN L i + aftN M b := by
  classical
  unfold aftN
  rw [Fintype.sum_sum_type, ← sum_without i (fun a => if L.lt i a then 1 else 0),
    if_neg (L.irrefl i), add_zero]
  simp only [LinOrd.comp_lt, LinOrd.compLt_inr_inl, LinOrd.compLt_inr_inr]

/-- **The sign data of a linear order**: the parity after an input is that of the number of
inputs after it, and the total parity is that of the number of inputs minus one. They are the
sign data of the planar binary trees with that order of leaves. -/
noncomputable def sgnD : SetOperadHom NOrd SgnD where
  app A _ _ L := ⟨L.1, fun a => (aftN L.1 a).bodd, (Fintype.card A + 1).bodd⟩
  app_map {A B} _ _ _ _ e x := by
    refine SgnData.ext rfl (funext fun b => ?_) ?_
    · show (aftN (LinOrd.map e x.1) b).bodd = (aftN x.1 (e.symm b)).bodd
      rw [aftN_map]
    · show (Fintype.card B + 1).bodd = (Fintype.card A + 1).bodd
      rw [Fintype.card_congr e]
  app_one := by
    refine SgnData.ext rfl (funext fun u => ?_) rfl
    show (aftN LinOrd.one u).bodd = false
    rw [aftN_one]
    rfl
  app_comp {A B} _ _ _ _ i x y := by
    obtain ⟨m, hm⟩ : ∃ m, Fintype.card A = m + 1 :=
      Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.1 (Fintype.card_pos_iff.2 ⟨i⟩))
    refine SgnData.ext rfl (funext fun u => ?_) ?_
    · rcases u with a | b
      · have h := aftN_comp_inl i x.1 y.1 a
        show (aftN (LinOrd.comp i x.1 y.1) (.inl a)).bodd = _
        by_cases hlt : x.1.lt a.1 i
        · rw [if_pos hlt, if_pos hlt] at h
          rw [SgnData.comp_def, SgnData.comp_aft_inl_of_lt _ _ _ _ hlt]
          show _ = xor (aftN x.1 a.1).bodd (Fintype.card B + 1).bodd
          have h2 := congrArg Nat.bodd h
          simp only [Nat.bodd_add, Nat.bodd_one] at h2 ⊢
          revert h2
          cases (aftN (LinOrd.comp i x.1 y.1) (Sum.inl a)).bodd <;> cases (aftN x.1 a.1).bodd <;>
            cases (Fintype.card B).bodd <;> simp
        · rw [if_neg hlt, if_neg hlt, add_zero, add_zero] at h
          rw [SgnData.comp_def, SgnData.comp_aft_inl_of_not_lt _ _ _ _ hlt, h]
      · show (aftN (LinOrd.comp i x.1 y.1) (.inr b)).bodd = xor (aftN y.1 b).bodd (aftN x.1 i).bodd
        rw [aftN_comp_inr, Nat.bodd_add, Bool.xor_comm]
    · show (Fintype.card (Without A i ⊕ B) + 1).bodd
        = xor (Fintype.card A + 1).bodd (Fintype.card B + 1).bodd
      rw [Fintype.card_sum, Reg.card_without, hm]
      simp only [Nat.add_sub_cancel, Nat.bodd_add, Nat.bodd_one]
      cases m.bodd <;> cases (Fintype.card B).bodd <;> rfl

end NOrd

end Operad
