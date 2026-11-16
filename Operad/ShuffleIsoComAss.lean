/-
# The shuffle operads of `Com` and `Ass` are presented by their rules

`Operad.ShuffleAnyCom` and `Operad.ShuffleAnyAss` give rules for the commutative and the
associative operad and compute the operads they present in each arity. This file identifies those
presented shuffle operads, over a field `K`, with the underlying shuffle operads
(`SymOperad.toShuffle`) of the commutative operad `Lin K ComSet` and of the associative operad
`Lin K AssSet`, the operads of algebras without unit.

* **`Com`** (`ComGen.presIso`): the lift of the generator to the binary operation of `ComSet` is
  an isomorphism of shuffle operads `(ComGen.rules K).Presented ≅ Shuf (Lin K ComSet)`. The
  relations hold because `ComSet` has one operation on each nonempty set of inputs
  (`ComGen.holds`); the lift is onto because `ComSet` is presented by that operation
  (`ComGen.presLift_surjective`); both sides have dimension one on a nonempty set.
* **`Ass`** (`AssShGen.presIso`): the lift of `x₁x₂` to the order `0 < 1` and of `x₂x₁` to
  `1 < 0` is an isomorphism `(AssShGen.rules K).Presented ≅ Shuf (Lin K AssSet)`. A leading
  monomial and its tail have the same linear order of the three inputs
  (`AssShGen.value_lead_eq_tail`), a linear order on three inputs being determined by three
  comparisons (`Sym.LinOrd.ext3`); the two operations of `AssSet` on two inputs are the values of
  the generators (`AssShGen.exists_eq_sv`); both sides have dimension `n!`.
* **Arity zero.** A presented shuffle operad has no operation without inputs, and neither have
  `Lin K ComSet` and `Lin K AssSet`. The operads `Sym.Com K` and `Sym.Ass K` have the component
  `K` on the empty set, so their shuffle operads are not presented by these rules; the comparison
  morphisms (`ComGen.toSymCom`, `AssShGen.toSymAss`) are bijective on every nonempty finite
  linear order (`ComGen.toSymCom_bijective`, `AssShGen.toSymAss_bijective`).
-/
import Operad.ShufflePresIso
import Operad.ShuffleAnyCom
import Operad.ShuffleAnyAss
import Operad.AssPres

universe u

namespace Operad

open STree

namespace ComGen

variable (K : Type u) [Field K]

instance isEmpty_zero : IsEmpty (ComGen 0) := ⟨fun x => nomatch x⟩

/-- **The values of the generator**: the product goes to the binary operation of `ComSet`. -/
noncomputable def val : ∀ k, ComGen k → Shuf (Lin K ComSet) (Fin k)
  | _, .mu => Finsupp.single ComSet.mu 1

lemma lift_gen₂ :
    (FreeSh.lift K (Shuf (Lin K ComSet)) (val K)).app (Fin 2) (FreeSh.gen₂ K ComGen.mu) =
      Finsupp.single ComSet.mu 1 :=
  FreeSh.lift_gen _ _ _

/-- **The relations of the rules hold in `ComSet`**, where any two operations with the same
inputs are equal. -/
theorem holds : (rules K).Holds (val K) := by
  refine Rules.holds_of_lift fun r => ⟨3, three_eq_range, ?_⟩
  rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, map_sub, sub_eq_zero]
  show _ = (FreeSh.lift K _ (val K)).app (Fin 3)
    (Finsupp.mapDomain (SMono.cast three_eq_range) (Finsupp.single rcomb 1))
  rw [Finsupp.mapDomain_single,
    FreeSh.app_right (g := mu) (h := mu) (m := SMono.cast three_eq_range rcomb) _ rfl, lift_gen₂,
    Lin.shuffle_comp_single]
  cases r
  · refine (FreeSh.app_twist (g := mu) (h := mu) (m := SMono.cast three_eq_range tcomb) _
      rfl).trans ?_
    rw [lift_gen₂, Lin.shuffle_comp_single]
    exact congrArg (Finsupp.single · 1) (Subsingleton.elim _ _)
  · refine (FreeSh.app_left (g := mu) (h := mu) (m := SMono.cast three_eq_range lcomb) _
      rfl).trans ?_
    rw [lift_gen₂, Lin.shuffle_comp_single]
    exact congrArg (Finsupp.single · 1) (Subsingleton.elim _ _)

/-- **The free operad on the product maps onto the linearization of `ComSet`.** -/
noncomputable def freeHom : SymOperadHom K (Lin K (FreeSet ComGen)) (Lin K ComSet) :=
  (ComSet.comPresIso.hom.comp Pres.ofFree).lin K

lemma freeHom_surjective (A : Type) [Fintype A] [DecidableEq A] :
    Function.Surjective ((freeHom K).app A) :=
  SetOperadHom.lin_surjective K _
    ((ComSet.comPresIso.equiv A).surjective.comp (Pres.ofFree_surjective A))

/-- **The lift of the rules is onto `ComSet`.** -/
theorem presLift_surjective (A : Type) [Fintype A] [LinearOrder A] :
    Function.Surjective (((rules K).presLift (holds K)).app A) := by
  refine Rules.presLift_surjective (holds K) (freeHom K) (freeHom_surjective K) (fun k s => ?_) A
  obtain ⟨g, σ⟩ := s
  cases g
  refine ⟨(rules K).shuffleIdeal.proj _ (Finsupp.single (FreeSh.genM (by norm_num) mu) 1), ?_⟩
  rw [Rules.presLift_gen, freeHom, SetOperadHom.lin_single]
  exact congrArg (Finsupp.single · 1) (Subsingleton.elim _ _)

lemma finrank_presented (A : Type) [Fintype A] [LinearOrder A] [Nonempty A] :
    Module.finrank K ((rules K).Presented A) = 1 :=
  finrank_eq_one (K := K) (Finset.nonempty_range_iff.2 Fintype.card_ne_zero)

lemma finrank_comSet (A : Type) [Fintype A] [DecidableEq A] [Nonempty A] :
    Module.finrank K (Lin K ComSet A) = 1 := by
  have e : Lin K ComSet A ≃ₗ[K] K := Finsupp.uniqueLinearEquiv K K (⟨‹Nonempty A›⟩ : ComSet A)
  rw [e.finrank_eq, Module.finrank_self]

/-- **The lift of the rules is bijective** in every arity. -/
theorem presLift_bijective (A : Type) [Fintype A] [LinearOrder A] :
    Function.Bijective (((rules K).presLift (holds K)).app A) :=
  Rules.presLift_bijective (holds K) (presLift_surjective K) (fun A _ _ _ => by
    rw [finrank_presented, finrank_comSet]
    exact ⟨rfl, Nat.one_pos⟩) A

/-- **The shuffle operad presented by the rules of `Com` is the underlying shuffle operad of the
commutative operad** `Lin K ComSet`, the operad of commutative associative algebras without
unit. -/
noncomputable def presIso : ShuffleOperadIso K (rules K).Presented (Shuf (Lin K ComSet)) :=
  ShuffleOperadIso.ofBijective _ (presLift_bijective K)

/-- **The isomorphism sends the generator to the binary operation of `ComSet`.** -/
theorem presIso_gen :
    (presIso K).hom.app (Fin 2) ((rules K).shuffleIdeal.proj _
      (Finsupp.single (FreeSh.genM (by norm_num) mu) 1)) = Finsupp.single ComSet.mu 1 :=
  Rules.presLift_gen (holds K) _ mu

end ComGen

namespace ComSet

variable (K : Type u) [Field K]

/-- Every operation of `ComSet` goes to `1`. -/
def unitHom : SetOperadHom ComSet (Und K (Sym.Com K)) where
  app _ _ _ _ := Und.of K (Sym.Com K) (1 : K)
  app_map _ _ := rfl
  app_one := rfl
  app_comp _ _ _ := by
    show (1 : K) = 1 * 1
    rw [mul_one]

/-- **The comparison with the unital commutative operad** `Sym.Com K`, whose component on the
empty set is `K`: the sum of the coefficients. -/
noncomputable def toCom : SymOperadHom K (Lin K ComSet) (Sym.Com K) := (unitHom K).linExtend

lemma toCom_single {A : Type} [Fintype A] [DecidableEq A] (x : ComSet A) (c : K) :
    (toCom K).app A (Finsupp.single x c) = c := by
  simp [toCom, SetOperadHom.linExtend, unitHom, Und.of]

/-- **The comparison is bijective on every nonempty set of inputs.** -/
theorem toCom_bijective (A : Type) [Fintype A] [DecidableEq A] [Nonempty A] :
    Function.Bijective ((toCom K).app A) := by
  refine bijective_of_surjective_of_finrank_eq _ (fun c => ⟨Finsupp.single ⟨‹Nonempty A›⟩ c,
    toCom_single K _ c⟩) ?_ ?_
  · rw [ComGen.finrank_comSet]
    exact (Module.finrank_self K).symm
  · rw [ComGen.finrank_comSet]
    exact Nat.one_pos

end ComSet

namespace ComGen

variable (K : Type u) [Field K]

/-- **The morphism from the presented shuffle operad to the shuffle operad of `Sym.Com`.** -/
noncomputable def toSymCom : ShuffleOperadHom K (rules K).Presented (Shuf (Sym.Com K)) :=
  (ComSet.toCom K).toShuffle.comp (presIso K).hom

/-- **The shuffle operad presented by the rules of `Com` is the shuffle operad of `Sym.Com` on
every nonempty finite linear order.** On the empty one the first is zero and the second is
`K`. -/
theorem toSymCom_bijective (A : Type) [Fintype A] [LinearOrder A] [Nonempty A] :
    Function.Bijective ((toSymCom K).app A) :=
  (ComSet.toCom_bijective K A).comp (presLift_bijective K A)

end ComGen

/-! ## The associative operad -/

namespace Sym.LinOrd

/-- In a linear order, of two distinct elements one is smaller. -/
lemma lt_swap_iff {A : Type} (x : LinOrd A) {a b : A} (h : a ≠ b) : x.lt b a ↔ ¬ x.lt a b :=
  ⟨fun h₁ h₂ => x.irrefl a (x.trans a b a h₂ h₁), fun h₁ => (x.total a b h).resolve_left h₁⟩

/-- **A linear order on three inputs is determined by three comparisons.** -/
lemma ext3 {x y : LinOrd (Fin 3)} (h01 : x.lt 0 1 ↔ y.lt 0 1) (h02 : x.lt 0 2 ↔ y.lt 0 2)
    (h12 : x.lt 1 2 ↔ y.lt 1 2) : x = y := by
  have sw : ∀ {a b : Fin 3}, a ≠ b → (x.lt a b ↔ y.lt a b) → (x.lt b a ↔ y.lt b a) :=
    fun h hab => (x.lt_swap_iff h).trans ((not_congr hab).trans (y.lt_swap_iff h).symm)
  have ir : ∀ a : Fin 3, x.lt a a ↔ y.lt a a :=
    fun a => ⟨fun h => absurd h (x.irrefl _), fun h => absurd h (y.irrefl _)⟩
  refine LinOrd.ext fun a b => ?_
  fin_cases a <;> fin_cases b
  · exact ir _
  · exact h01
  · exact h02
  · exact sw (by decide) h01
  · exact ir _
  · exact h12
  · exact sw (by decide) h02
  · exact sw (by decide) h12
  · exact ir _

/-- **A linear order on two inputs is determined by one comparison.** -/
lemma ext2 {x y : LinOrd (Fin 2)} (h01 : x.lt 0 1 ↔ y.lt 0 1) : x = y := by
  refine LinOrd.ext fun a b => ?_
  fin_cases a <;> fin_cases b
  · exact ⟨fun h => absurd h (x.irrefl _), fun h => absurd h (y.irrefl _)⟩
  · exact h01
  · exact (x.lt_swap_iff (by decide)).trans ((not_congr h01).trans (y.lt_swap_iff (by decide)).symm)
  · exact ⟨fun h => absurd h (x.irrefl _), fun h => absurd h (y.irrefl _)⟩

/-- **The order `0 < 1`** on two inputs. -/
def ord2 : LinOrd (Fin 2) where
  lt a b := a < b
  irrefl a := lt_irrefl a
  trans _ _ _ := lt_trans
  total _ _ h := lt_or_gt_of_ne h

end Sym.LinOrd

namespace AssShGen

open Sym FreeBin PoisDim

variable (K : Type u) [Field K]

instance isEmpty_assGen_zero : IsEmpty (AssGen 0) := ⟨fun x => nomatch x⟩

/-- **The orders of the two generators**: `0 < 1` for `x₁x₂`, `1 < 0` for `x₂x₁`. -/
def sv : AssShGen 2 → AssSet (Fin 2)
  | mu => (LinOrd.ord2, ⟨⟨0⟩⟩)
  | op => SetOperad.map (Equiv.swap 0 1) (LinOrd.ord2, ⟨⟨0⟩⟩)

/-- **The values of the generators** in the linearization of `AssSet`. -/
noncomputable def val : ∀ k, AssShGen k → Shuf (Lin K AssSet) (Fin k)
  | _, mu => Finsupp.single (sv mu) 1
  | _, op => Finsupp.single (sv op) 1

lemma lift_gen₂ (e : AssShGen 2) :
    (FreeSh.lift K (Shuf (Lin K AssSet)) (val K)).app (Fin 2) (FreeSh.gen₂ K e) =
      Finsupp.single (sv e) 1 := by
  refine (FreeSh.lift_gen _ _ _).trans ?_
  cases e <;> rfl

/-- The order of `e (f (0, 1), 2)`. -/
noncomputable def vL (e f : AssShGen 2) : AssSet (Fin 3) :=
  SetOperad.map e0 (SetOperad.comp 0 (sv e) (sv f))

/-- The order of `e (f (0, 2), 1)`. -/
noncomputable def vT (e f : AssShGen 2) : AssSet (Fin 3) :=
  SetOperad.map (e0.trans τ₁₂) (SetOperad.comp 0 (sv e) (sv f))

/-- The order of `e (0, f (1, 2))`. -/
noncomputable def vR (e f : AssShGen 2) : AssSet (Fin 3) :=
  SetOperad.map e1 (SetOperad.comp 1 (sv e) (sv f))

lemma lift_lcomb (e f : AssShGen 2) :
    (FreeSh.lift K (Shuf (Lin K AssSet)) (val K)).app (Fin 3)
      (Finsupp.single (SMono.cast three_eq_range (lcomb e f)) 1) = Finsupp.single (vL e f) 1 := by
  refine (FreeSh.app_left (g := e) (h := f) _ rfl).trans ?_
  rw [lift_gen₂, lift_gen₂, Lin.shuffle_comp_single]
  rfl

lemma lift_tcomb (e f : AssShGen 2) :
    (FreeSh.lift K (Shuf (Lin K AssSet)) (val K)).app (Fin 3)
      (Finsupp.single (SMono.cast three_eq_range (tcomb e f)) 1) = Finsupp.single (vT e f) 1 := by
  refine (FreeSh.app_twist (g := e) (h := f) _ rfl).trans ?_
  rw [lift_gen₂, lift_gen₂, Lin.shuffle_comp_single]
  rfl

lemma lift_rcomb (e f : AssShGen 2) :
    (FreeSh.lift K (Shuf (Lin K AssSet)) (val K)).app (Fin 3)
      (Finsupp.single (SMono.cast three_eq_range (rcomb e f)) 1) = Finsupp.single (vR e f) 1 := by
  refine (FreeSh.app_right (g := e) (h := f) _ rfl).trans ?_
  rw [lift_gen₂, lift_gen₂, Lin.shuffle_comp_single]
  rfl

lemma e0_symm_zero : e0.symm 0 = Sum.inr 0 := e0.symm_apply_eq.2 rfl

lemma e0_symm_one : e0.symm 1 = Sum.inr 1 := e0.symm_apply_eq.2 rfl

lemma e0_symm_two : e0.symm 2 = Sum.inl ⟨1, by decide⟩ := e0.symm_apply_eq.2 rfl

lemma e0t_symm_zero : (e0.trans τ₁₂).symm 0 = Sum.inr 0 := (e0.trans τ₁₂).symm_apply_eq.2 rfl

lemma e0t_symm_one : (e0.trans τ₁₂).symm 1 = Sum.inl ⟨1, by decide⟩ :=
  (e0.trans τ₁₂).symm_apply_eq.2 rfl

lemma e0t_symm_two : (e0.trans τ₁₂).symm 2 = Sum.inr 1 := (e0.trans τ₁₂).symm_apply_eq.2 rfl

lemma e1_symm_zero : e1.symm 0 = Sum.inl ⟨0, by decide⟩ := e1.symm_apply_eq.2 rfl

lemma e1_symm_one : e1.symm 1 = Sum.inr 0 := e1.symm_apply_eq.2 rfl

lemma e1_symm_two : e1.symm 2 = Sum.inr 1 := e1.symm_apply_eq.2 rfl

lemma sv_mu_lt (a b : Fin 2) : (sv mu).1.lt a b ↔ a < b := Iff.rfl

lemma sv_op_lt (a b : Fin 2) : (sv op).1.lt a b ↔ b < a := by
  show Equiv.swap (0 : Fin 2) 1 a < Equiv.swap (0 : Fin 2) 1 b ↔ b < a
  fin_cases a <;> fin_cases b <;> decide

lemma vL_lt (e f : AssShGen 2) :
    ((vL e f).1.lt 0 1 ↔ (sv f).1.lt 0 1) ∧ ((vL e f).1.lt 0 2 ↔ (sv e).1.lt 0 1) ∧
      ((vL e f).1.lt 1 2 ↔ (sv e).1.lt 0 1) := by
  refine ⟨?_, ?_, ?_⟩
  · show LinOrd.compLt (sv e).1.lt (sv f).1.lt 0 (e0.symm 0) (e0.symm 1) ↔ _
    rw [e0_symm_zero, e0_symm_one]
    rfl
  · show LinOrd.compLt (sv e).1.lt (sv f).1.lt 0 (e0.symm 0) (e0.symm 2) ↔ _
    rw [e0_symm_zero, e0_symm_two]
    rfl
  · show LinOrd.compLt (sv e).1.lt (sv f).1.lt 0 (e0.symm 1) (e0.symm 2) ↔ _
    rw [e0_symm_one, e0_symm_two]
    rfl

lemma vT_lt (e f : AssShGen 2) :
    ((vT e f).1.lt 0 1 ↔ (sv e).1.lt 0 1) ∧ ((vT e f).1.lt 0 2 ↔ (sv f).1.lt 0 1) ∧
      ((vT e f).1.lt 1 2 ↔ (sv e).1.lt 1 0) := by
  refine ⟨?_, ?_, ?_⟩
  · show LinOrd.compLt (sv e).1.lt (sv f).1.lt 0 ((e0.trans τ₁₂).symm 0)
      ((e0.trans τ₁₂).symm 1) ↔ _
    rw [e0t_symm_zero, e0t_symm_one]
    rfl
  · show LinOrd.compLt (sv e).1.lt (sv f).1.lt 0 ((e0.trans τ₁₂).symm 0)
      ((e0.trans τ₁₂).symm 2) ↔ _
    rw [e0t_symm_zero, e0t_symm_two]
    rfl
  · show LinOrd.compLt (sv e).1.lt (sv f).1.lt 0 ((e0.trans τ₁₂).symm 1)
      ((e0.trans τ₁₂).symm 2) ↔ _
    rw [e0t_symm_one, e0t_symm_two]
    rfl

lemma vR_lt (e f : AssShGen 2) :
    ((vR e f).1.lt 0 1 ↔ (sv e).1.lt 0 1) ∧ ((vR e f).1.lt 0 2 ↔ (sv e).1.lt 0 1) ∧
      ((vR e f).1.lt 1 2 ↔ (sv f).1.lt 0 1) := by
  refine ⟨?_, ?_, ?_⟩
  · show LinOrd.compLt (sv e).1.lt (sv f).1.lt 1 (e1.symm 0) (e1.symm 1) ↔ _
    rw [e1_symm_zero, e1_symm_one]
    rfl
  · show LinOrd.compLt (sv e).1.lt (sv f).1.lt 1 (e1.symm 0) (e1.symm 2) ↔ _
    rw [e1_symm_zero, e1_symm_two]
    rfl
  · show LinOrd.compLt (sv e).1.lt (sv f).1.lt 1 (e1.symm 1) (e1.symm 2) ↔ _
    rw [e1_symm_one, e1_symm_two]
    rfl

/-- **Two operations of `AssSet` on three inputs with the same three comparisons are equal.** -/
lemma ext3 {u v : AssSet (Fin 3)} (h01 : u.1.lt 0 1 ↔ v.1.lt 0 1) (h02 : u.1.lt 0 2 ↔ v.1.lt 0 2)
    (h12 : u.1.lt 1 2 ↔ v.1.lt 1 2) : u = v :=
  Prod.ext (LinOrd.ext3 h01 h02 h12) (Subsingleton.elim _ _)

/-- **A leading monomial and its tail have the same order**, as they have the same word. -/
theorem value_lead_eq_tail {e f : AssShGen 2} (hef : (e, f) ≠ (mu, op)) (s : Bool) :
    ∃ u : AssSet (Fin 3),
      (FreeSh.lift K (Shuf (Lin K AssSet)) (val K)).app (Fin 3)
        (Finsupp.single (SMono.cast three_eq_range (leadOf e f s)) 1) = Finsupp.single u 1 ∧
      (FreeSh.lift K (Shuf (Lin K AssSet)) (val K)).app (Fin 3)
        (Finsupp.single (SMono.cast three_eq_range (tailOf e f s)) 1) = Finsupp.single u 1 := by
  have key : ∀ {u v : AssSet (Fin 3)}, u = v → ∀ {x y : Lin K AssSet (Fin 3)},
      x = Finsupp.single u 1 → y = Finsupp.single v 1 →
      ∃ w : AssSet (Fin 3), x = Finsupp.single w 1 ∧ y = Finsupp.single w 1 :=
    fun h _ _ hx hy => ⟨_, hx, h ▸ hy⟩
  cases e <;> cases f <;> cases s
  · exact key (u := vT mu mu) (v := vR mu op) (ext3
      (by simp [(vT_lt mu mu).1, (vR_lt mu op).1])
      (by simp [(vT_lt mu mu).2.1, (vR_lt mu op).2.1])
      (by simp [(vT_lt mu mu).2.2, (vR_lt mu op).2.2, sv_mu_lt, sv_op_lt]))
      (lift_tcomb K mu mu) (lift_rcomb K mu op)
  · exact key (u := vL mu mu) (v := vR mu mu) (ext3
      (by simp [(vL_lt mu mu).1, (vR_lt mu mu).1, sv_mu_lt])
      (by simp [(vL_lt mu mu).2.1, (vR_lt mu mu).2.1])
      (by simp [(vL_lt mu mu).2.2, (vR_lt mu mu).2.2, sv_mu_lt]))
      (lift_lcomb K mu mu) (lift_rcomb K mu mu)
  · exact absurd rfl hef
  · exact absurd rfl hef
  · exact key (u := vT op mu) (v := vL mu op) (ext3
      (by simp [(vT_lt op mu).1, (vL_lt mu op).1])
      (by simp [(vT_lt op mu).2.1, (vL_lt mu op).2.1, sv_mu_lt])
      (by simp [(vT_lt op mu).2.2, (vL_lt mu op).2.2, sv_mu_lt, sv_op_lt]))
      (lift_tcomb K op mu) (lift_lcomb K mu op)
  · exact key (u := vL op mu) (v := vT mu op) (ext3
      (by simp [(vL_lt op mu).1, (vT_lt mu op).1, sv_mu_lt])
      (by simp [(vL_lt op mu).2.1, (vT_lt mu op).2.1])
      (by simp [(vL_lt op mu).2.2, (vT_lt mu op).2.2, sv_mu_lt, sv_op_lt]))
      (lift_lcomb K op mu) (lift_tcomb K mu op)
  · exact key (u := vT op op) (v := vR op mu) (ext3
      (by simp [(vT_lt op op).1, (vR_lt op mu).1])
      (by simp [(vT_lt op op).2.1, (vR_lt op mu).2.1])
      (by simp [(vT_lt op op).2.2, (vR_lt op mu).2.2, sv_mu_lt, sv_op_lt]))
      (lift_tcomb K op op) (lift_rcomb K op mu)
  · exact key (u := vL op op) (v := vR op op) (ext3
      (by simp [(vL_lt op op).1, (vR_lt op op).1, sv_op_lt])
      (by simp [(vL_lt op op).2.1, (vR_lt op op).2.1])
      (by simp [(vL_lt op op).2.2, (vR_lt op op).2.2, sv_op_lt]))
      (lift_lcomb K op op) (lift_rcomb K op op)

/-- **The relations of the rules hold in `AssSet`.** -/
theorem holds : (rules K).Holds (val K) := by
  refine Rules.holds_of_lift fun r => ⟨3, three_eq_range, ?_⟩
  obtain ⟨⟨⟨e, f⟩, hef⟩, s⟩ := r
  obtain ⟨u, h₁, h₂⟩ := value_lead_eq_tail K hef s
  rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, map_sub, sub_eq_zero]
  refine h₁.trans (Eq.trans ?_ h₂).symm
  show (FreeSh.lift K _ (val K)).app (Fin 3) (Finsupp.mapDomain (SMono.cast three_eq_range)
    (Finsupp.single (tailOf e f s) 1)) = _
  rw [Finsupp.mapDomain_single]

/-- **The free operad on one binary operation maps onto the linearization of `AssSet`.** -/
noncomputable def freeHom : SymOperadHom K (Lin K (FreeSet AssGen)) (Lin K AssSet) :=
  (AssSet.presIso.hom.comp Pres.ofFree).lin K

lemma freeHom_surjective (A : Type) [Fintype A] [DecidableEq A] :
    Function.Surjective ((freeHom K).app A) :=
  SetOperadHom.lin_surjective K _
    ((AssSet.presIso.equiv A).surjective.comp (Pres.ofFree_surjective A))

/-- **The two operations of `AssSet` on two inputs** are the orders of the two generators. -/
lemma exists_eq_sv (y : AssSet (Fin 2)) : ∃ e, y = sv e := by
  by_cases h : y.1.lt 0 1
  · exact ⟨mu, Prod.ext (LinOrd.ext2 (iff_of_true h (by rw [sv_mu_lt]; decide)))
      (Subsingleton.elim _ _)⟩
  · exact ⟨op, Prod.ext (LinOrd.ext2 (iff_of_false h (by rw [sv_op_lt]; decide)))
      (Subsingleton.elim _ _)⟩

/-- **The lift of the rules is onto `AssSet`.** -/
theorem presLift_surjective (A : Type) [Fintype A] [LinearOrder A] :
    Function.Surjective (((rules K).presLift (holds K)).app A) := by
  refine Rules.presLift_surjective (holds K) (freeHom K) (freeHom_surjective K) (fun k s => ?_) A
  obtain ⟨g, σ⟩ := s
  cases g
  obtain ⟨e, he⟩ := exists_eq_sv ((AssSet.presIso.hom.comp Pres.ofFree).app (Fin 2)
    (SetOperad.map σ.symm (Pres.gen AssGen.m)))
  refine ⟨(rules K).shuffleIdeal.proj _ (Finsupp.single (FreeSh.genM (by norm_num) e) 1), ?_⟩
  rw [Rules.presLift_gen, freeHom, SetOperadHom.lin_single, he]
  cases e <;> rfl

lemma finrank_presented (A : Type) [Fintype A] [LinearOrder A] [Nonempty A] :
    Module.finrank K ((rules K).Presented A) = (Fintype.card A).factorial :=
  (finrank_eq_factorial (K := K) (Finset.nonempty_range_iff.2 Fintype.card_ne_zero)).trans
    (by rw [Finset.card_range])

/-- On a nonempty set of inputs an operation of `AssSet` is a linear order. -/
def AssSet.equivLinOrd (A : Type) [Fintype A] [DecidableEq A] [Nonempty A] :
    AssSet A ≃ LinOrd A where
  toFun x := x.1
  invFun x := (x, ⟨‹Nonempty A›⟩)
  left_inv _ := Prod.ext rfl (Subsingleton.elim _ _)
  right_inv _ := rfl

lemma finrank_assSet (A : Type) [Fintype A] [DecidableEq A] [Nonempty A] :
    Module.finrank K (Lin K AssSet A) = (Fintype.card A).factorial := by
  have e : Lin K AssSet A ≃ₗ[K] Sym.Ass K A := Finsupp.domLCongr (AssSet.equivLinOrd A)
  rw [e.finrank_eq, Sym.Ass.finrank]

/-- **The lift of the rules is bijective** in every arity. -/
theorem presLift_bijective (A : Type) [Fintype A] [LinearOrder A] :
    Function.Bijective (((rules K).presLift (holds K)).app A) :=
  Rules.presLift_bijective (holds K) (presLift_surjective K) (fun A _ _ _ => by
    rw [finrank_presented, finrank_assSet]
    exact ⟨rfl, Nat.factorial_pos _⟩) A

/-- **The shuffle operad presented by the rules of `Ass` is the underlying shuffle operad of the
associative operad** `Lin K AssSet`, the operad of associative algebras without unit. -/
noncomputable def presIso : ShuffleOperadIso K (rules K).Presented (Shuf (Lin K AssSet)) :=
  ShuffleOperadIso.ofBijective _ (presLift_bijective K)

/-- **The isomorphism sends the generators to their orders**: `x₁x₂` to `0 < 1` and `x₂x₁` to
`1 < 0`. -/
theorem presIso_gen (e : AssShGen 2) :
    (presIso K).hom.app (Fin 2) ((rules K).shuffleIdeal.proj _
      (Finsupp.single (FreeSh.genM (by norm_num) e) 1)) = Finsupp.single (sv e) 1 := by
  refine (Rules.presLift_gen (holds K) _ e).trans ?_
  cases e <;> rfl

/-- **The comparison with `Sym.Ass K`**, which also has the empty order in arity zero: forget
that the set of inputs is nonempty. -/
noncomputable def toAss : SymOperadHom K (Lin K AssSet) (Sym.Ass K) :=
  (Hadamard.fst (S := fun A _ _ => LinOrd A) (T := ComSet)).lin K

/-- **The comparison is bijective on every nonempty set of inputs.** -/
theorem toAss_bijective (A : Type) [Fintype A] [DecidableEq A] [Nonempty A] :
    Function.Bijective ((toAss K).app A) :=
  ⟨Finsupp.mapDomain_injective (AssSet.equivLinOrd A).injective,
    Finsupp.mapDomain_surjective (AssSet.equivLinOrd A).surjective⟩

/-- **The morphism from the presented shuffle operad to the shuffle operad of `Sym.Ass`.** -/
noncomputable def toSymAss : ShuffleOperadHom K (rules K).Presented (Shuf (Sym.Ass K)) :=
  (toAss K).toShuffle.comp (presIso K).hom

/-- **The shuffle operad presented by the rules of `Ass` is the shuffle operad of `Sym.Ass` on
every nonempty finite linear order.** On the empty one the first is zero and the second is
`K`. -/
theorem toSymAss_bijective (A : Type) [Fintype A] [LinearOrder A] [Nonempty A] :
    Function.Bijective ((toSymAss K).app A) :=
  (toAss_bijective K A).comp (presLift_bijective K A)

end AssShGen

end Operad
