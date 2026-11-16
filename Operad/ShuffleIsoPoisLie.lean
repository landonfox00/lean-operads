/-
# The shuffle operads of `Pois` and `Lie` are presented by their rules

Over a field `K`, the shuffle operads presented by rules are identified with the underlying
shuffle operads (`SymOperad.toShuffle`) of `Operad.Pois` and `Operad.Lie`.

* **`Pois`** (`PoisShGen.presIso`): the lift of the product and the bracket is an isomorphism of
  shuffle operads from the operad presented by the six rules of `Operad.ShuffleAnyPois` to
  `Shuf (Pois K)`. The relations are the six relations of arity three of `Operad.PoisPBW`
  (`PoisShGen.holds`); the lift is onto because a transposed generator is the generator up to
  sign (`PoisShGen.presLift_surjective`); both sides have dimension `n!`
  (`PoisShGen.finrank_eq_factorial`, `PoisDim.finrank_pois_eq`).
* **The rule of `Lie`** (`LieSh.rules`): the shuffle operad of `Lie` has one generator of arity
  two, and the rule is the Jacobi identity
  `[[x₀, x₁], x₂] = [[x₀, x₂], x₁] + [x₀, [x₁, x₂]]`, led by the left comb for the
  path-lexicographic order of `Operad.ComGen` (`ComGen.tcomb_lt_lcomb`).
* **`Lie`** (`LieSh.presIso`): the lift of the bracket is an isomorphism from the operad
  presented by the Jacobi rule to `Shuf (Lie K)`. The rule holds by
  `Operad.FreeBin.jacobi_rule_mem`, and the lift is onto as for `Pois`. The library has no
  dimension of `Lie` to compare, so injectivity goes through `Pois`: the presented operad of
  `Lie` maps to that of `Pois` (`LieSh.ι`) with a retraction sending the product to zero
  (`LieSh.ϱ`, `LieSh.ϱ_comp_ι`), and the square with the morphism `Lie.toPois` commutes
  (`LieSh.toPois_comp_presLift`).
* Hence **`Lie` is a suboperad of `Pois`** (`Lie.toPois_injective`): the morphism sending the
  bracket to the bracket is injective on every finite set of inputs.

Not proved here: that the Jacobi rule is a Gröbner basis, and the dimension `(n - 1)!` of `Lie`.
-/
import Operad.ShufflePresIso
import Operad.ShuffleAnyPois
import Operad.ShuffleAnyCom
import Operad.PostLie

universe u

namespace Operad

open STree FreeBin

/-! ## The Poisson operad -/

namespace PoisShGen

variable (K : Type u) [Field K]

/-- **The quotient map** from the free operad on the product and the bracket to `Pois`. -/
noncomputable abbrev projP : SymOperadHom K (FreeBin K PoisOp) (Pois K) :=
  (SymOperadIdeal.span K (rel23 (PoisDim.r₂P K) (PoisDim.r₃P K))).projHom

/-- **The values of the generators**: the classes of the product and of the bracket. -/
noncomputable def val : ∀ k, PoisShGen k → Shuf (Pois K) (Fin k)
  | _, mul => (projP K).app (Fin 2) (bin2 PoisOp.mul 1)
  | _, br => (projP K).app (Fin 2) (bin2 PoisOp.bracket 1)

lemma lift_gen₂ (e : PoisShGen 2) :
    (FreeSh.lift K (Shuf (Pois K)) (val K)).app (Fin 2) (FreeSh.gen₂ K e) =
      (projP K).app (Fin 2) (bin2 (op e) 1) := by
  refine (FreeSh.lift_gen _ _ _).trans ?_
  cases e <;> rfl

lemma lift_lcomb (e f : PoisShGen 2) :
    (FreeSh.lift K (Shuf (Pois K)) (val K)).app (Fin 3)
      (Finsupp.single (SMono.cast three_eq_range (lcomb e f)) 1) =
      (projP K).app (Fin 3) (binL (op e) (op f) 1) :=
  FreeSh.app_left_bin (projP K) _ (lift_gen₂ K e) (lift_gen₂ K f) rfl

lemma lift_tcomb (e f : PoisShGen 2) :
    (FreeSh.lift K (Shuf (Pois K)) (val K)).app (Fin 3)
      (Finsupp.single (SMono.cast three_eq_range (tcomb e f)) 1) =
      (projP K).app (Fin 3) (binL (op e) (op f) PoisDim.τ₁₂) :=
  FreeSh.app_twist_bin (projP K) _ (lift_gen₂ K e) (lift_gen₂ K f) rfl

lemma lift_rcomb (e f : PoisShGen 2) :
    (FreeSh.lift K (Shuf (Pois K)) (val K)).app (Fin 3)
      (Finsupp.single (SMono.cast three_eq_range (rcomb e f)) 1) =
      (projP K).app (Fin 3) (binR (op e) (op f) 1) :=
  FreeSh.app_right_bin (projP K) _ (lift_gen₂ K e) (lift_gen₂ K f) rfl

lemma projP_eq_zero {x : FreeBin K PoisOp (Fin 3)} (hx : x ∈ PoisDim.I3 K) :
    (projP K).app (Fin 3) x = 0 :=
  ((SymOperadIdeal.span K (rel23 (PoisDim.r₂P K) (PoisDim.r₃P K))).proj_eq_zero_iff x).2
    (PoisDim.I3_eq (K := K) ▸ hx)

/-- **The relations of the rules hold in `Pois`**: each is one of the six relations of arity
three of `Operad.PoisDim`. -/
theorem holds : (rules K).Holds (val K) := by
  refine Rules.holds_of_lift fun r => ⟨3, three_eq_range, ?_⟩
  rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, map_sub, sub_eq_zero]
  cases r
  · have h := projP_eq_zero K (PoisDim.y₁_mem (K := K))
    rw [map_sub, map_sub, sub_sub, sub_eq_zero] at h
    show (FreeSh.lift K _ (val K)).app (Fin 3)
        (Finsupp.single (SMono.cast three_eq_range (lcomb br br)) 1) =
      (FreeSh.lift K _ (val K)).app (Fin 3) (Finsupp.mapDomain (SMono.cast three_eq_range)
        (Finsupp.single (tcomb br br) 1 + Finsupp.single (rcomb br br) 1))
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single, map_add]
    simp only [lift_lcomb, lift_tcomb, lift_rcomb]
    exact h
  · have h := projP_eq_zero K (PoisDim.y₂_mem (K := K))
    rw [map_sub, map_sub, sub_sub, sub_eq_zero] at h
    show (FreeSh.lift K _ (val K)).app (Fin 3)
        (Finsupp.single (SMono.cast three_eq_range (rcomb br mul)) 1) =
      (FreeSh.lift K _ (val K)).app (Fin 3) (Finsupp.mapDomain (SMono.cast three_eq_range)
        (Finsupp.single (lcomb mul br) 1 + Finsupp.single (tcomb mul br) 1))
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single, map_add]
    simp only [lift_lcomb, lift_tcomb, lift_rcomb]
    exact h
  · have h := projP_eq_zero K (PoisDim.y₃_mem (K := K))
    rw [map_add, map_sub, sub_add, sub_eq_zero] at h
    show (FreeSh.lift K _ (val K)).app (Fin 3)
        (Finsupp.single (SMono.cast three_eq_range (tcomb br mul)) 1) =
      (FreeSh.lift K _ (val K)).app (Fin 3) (Finsupp.mapDomain (SMono.cast three_eq_range)
        (Finsupp.single (lcomb mul br) 1 - Finsupp.single (rcomb mul br) 1))
    rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, Finsupp.mapDomain_single, map_sub]
    simp only [lift_lcomb, lift_tcomb, lift_rcomb]
    exact h
  · have h := projP_eq_zero K (PoisDim.y₄_mem (K := K))
    rw [map_sub, map_sub, sub_sub, sub_eq_zero] at h
    show (FreeSh.lift K _ (val K)).app (Fin 3)
        (Finsupp.single (SMono.cast three_eq_range (lcomb br mul)) 1) =
      (FreeSh.lift K _ (val K)).app (Fin 3) (Finsupp.mapDomain (SMono.cast three_eq_range)
        (Finsupp.single (tcomb mul br) 1 + Finsupp.single (rcomb mul br) 1))
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single, map_add]
    simp only [lift_lcomb, lift_tcomb, lift_rcomb]
    exact h
  · have h := projP_eq_zero K (PoisDim.y₅_mem (K := K))
    rw [map_sub, sub_eq_zero] at h
    show (FreeSh.lift K _ (val K)).app (Fin 3)
        (Finsupp.single (SMono.cast three_eq_range (rcomb mul mul)) 1) =
      (FreeSh.lift K _ (val K)).app (Fin 3) (Finsupp.mapDomain (SMono.cast three_eq_range)
        (Finsupp.single (lcomb mul mul) 1))
    rw [Finsupp.mapDomain_single]
    simp only [lift_lcomb, lift_rcomb]
    exact h
  · have h := projP_eq_zero K (PoisDim.y₆_mem (K := K))
    rw [map_sub, sub_eq_zero] at h
    show (FreeSh.lift K _ (val K)).app (Fin 3)
        (Finsupp.single (SMono.cast three_eq_range (tcomb mul mul)) 1) =
      (FreeSh.lift K _ (val K)).app (Fin 3) (Finsupp.mapDomain (SMono.cast three_eq_range)
        (Finsupp.single (lcomb mul mul) 1))
    rw [Finsupp.mapDomain_single]
    simp only [lift_lcomb, lift_tcomb]
    exact h

/-- **The lift of the rules is onto `Pois`.** -/
theorem presLift_surjective (A : Type) [Fintype A] [LinearOrder A] :
    Function.Surjective (((rules K).presLift (holds K)).app A) := by
  refine Rules.presLift_surjective (T := BinGen PoisOp) (holds K) (projP K)
    (fun A _ _ => (SymOperadIdeal.span K _).proj_surjective A) (fun k s => ?_) A
  obtain ⟨⟨g⟩, σ⟩ := s
  have hmul : (projP K).app (Fin 2) (bin2 PoisOp.mul 1) ∈
      LinearMap.range (((rules K).presLift (holds K)).app (Fin 2)) :=
    ⟨_, Rules.presLift_gen (holds K) (by norm_num) mul⟩
  have hbr : (projP K).app (Fin 2) (bin2 PoisOp.bracket 1) ∈
      LinearMap.range (((rules K).presLift (holds K)).app (Fin 2)) :=
    ⟨_, Rules.presLift_gen (holds K) (by norm_num) br⟩
  show (projP K).app (Fin 2) (bin2 g σ.symm) ∈ _
  rcases perm2_cases σ.symm with h | h <;> rw [h] <;> cases g
  · exact hmul
  · exact hbr
  · have := proj_bin2_swap_comm (K := K) (r₂ := PoisDim.r₂P K) (r₃ := PoisDim.r₃P K)
      (b := PoisOp.mul) (Or.inl rfl)
    exact (show (projP K).app (Fin 2) (bin2 PoisOp.mul (Equiv.swap 0 1)) = _ from this) ▸ hmul
  · have := proj_bin2_swap_anti (K := K) (r₂ := PoisDim.r₂P K) (r₃ := PoisDim.r₃P K)
      (b := PoisOp.bracket) (Or.inr rfl)
    exact (show (projP K).app (Fin 2) (bin2 PoisOp.bracket (Equiv.swap 0 1)) = _ from this) ▸
      Submodule.neg_mem _ hbr

lemma finrank_presented (A : Type) [Fintype A] [LinearOrder A] [Nonempty A] :
    Module.finrank K ((rules K).Presented A) = (Fintype.card A).factorial :=
  (finrank_eq_factorial (K := K) (Finset.nonempty_range_iff.2 Fintype.card_ne_zero)).trans
    (by rw [Finset.card_range])

/-- **The lift of the rules is bijective** in every arity. -/
theorem presLift_bijective (A : Type) [Fintype A] [LinearOrder A] :
    Function.Bijective (((rules K).presLift (holds K)).app A) :=
  Rules.presLift_bijective (holds K) (presLift_surjective K) (fun A _ _ _ => by
    rw [finrank_presented, PoisDim.finrank_pois_eq K A]
    exact ⟨rfl, Nat.factorial_pos _⟩) A

/-- **The shuffle operad presented by the rules of `Pois` is the underlying shuffle operad of
the Poisson operad.** -/
noncomputable def presIso : ShuffleOperadIso K (rules K).Presented (Shuf (Pois K)) :=
  ShuffleOperadIso.ofBijective _ (presLift_bijective K)

/-- **The isomorphism sends the generators to the product and the bracket.** -/
theorem presIso_gen (e : PoisShGen 2) :
    (presIso K).hom.app (Fin 2) ((rules K).shuffleIdeal.proj _
      (Finsupp.single (FreeSh.genM (by norm_num) e) 1)) =
      (projP K).app (Fin 2) (bin2 (op e) 1) := by
  refine (Rules.presLift_gen (holds K) _ e).trans ?_
  cases e <;> rfl

end PoisShGen

/-! ## The Lie operad -/

namespace ComGen

/-- The twisted left comb is smaller than the left comb: the words of the leaf `0` agree, and the
word of the leaf `1` is shorter. -/
lemma tcomb_lt_lcomb : pathLex letter tcomb lcomb := by
  refine ⟨⟨1, by simp⟩, fun j hj => ?_, ?_⟩
  · have hj0 : j.1 = 0 := by
      have : j.1 < 1 := hj
      omega
    show STree.word letter tcomb.1 j.1 = STree.word letter lcomb.1 j.1
    rw [hj0, STree.word, STree.word, pos_eq tcomb.nodup (q := [0, 0]) rfl,
      pos_eq lcomb.nodup (q := [0, 0]) rfl]
    rfl
  · show DegLex (STree.word letter tcomb.1 1) (STree.word letter lcomb.1 1)
    rw [STree.word, STree.word, pos_eq tcomb.nodup (q := [1]) rfl,
      pos_eq lcomb.nodup (q := [0, 1]) rfl]
    exact Or.inl (by decide)

end ComGen

namespace LieSh

open ComGen

section Rules

variable (K : Type u) [CommRing K]

/-- **The rule of the Lie operad**, on the one generator of arity two of its shuffle operad, the
bracket, with the monomials and the order of `Operad.ComGen`: the Jacobi identity
`[[x₀, x₁], x₂] = [[x₀, x₂], x₁] + [x₀, [x₁, x₂]]`, led by the left comb. -/
noncomputable def rules : Rules K Unit ComGen.order.toCtxOrder where
  src _ := three
  lead _ := lcomb
  tail _ := Finsupp.single tcomb 1 + Finsupp.single rcomb 1
  tail_lt _ m hm := by
    classical
    rcases Finset.mem_union.1 (Finsupp.support_add hm) with h | h
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset h)]
      exact tcomb_lt_lcomb
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset h)]
      exact rcomb_lt_lcomb

end Rules

variable (K : Type u) [Field K]

/-- **The quotient map** from the free operad on the bracket to `Lie`. -/
noncomputable abbrev projL : SymOperadHom K (FreeBin K Unit) (Lie K) :=
  (SymOperadIdeal.span K (rel23 {BinRel.antisymm K ()} {BinRel.jacobi K ()})).projHom

/-- **The value of the generator**: the class of the bracket. -/
noncomputable def val : ∀ k, ComGen k → Shuf (Lie K) (Fin k)
  | _, .mu => (projL K).app (Fin 2) (bin2 () 1)

lemma lift_gen₂ :
    (FreeSh.lift K (Shuf (Lie K)) (val K)).app (Fin 2) (FreeSh.gen₂ K ComGen.mu) =
      (projL K).app (Fin 2) (bin2 () 1) :=
  FreeSh.lift_gen _ _ _

/-- **The Jacobi rule holds in `Lie`.** -/
theorem holds : (rules K).Holds (val K) := by
  refine Rules.holds_of_lift fun r => ⟨3, three_eq_range, ?_⟩
  have h := ((SymOperadIdeal.span K
    (rel23 {BinRel.antisymm K ()} {BinRel.jacobi K ()})).proj_eq_zero_iff _).2
    (jacobi_rule_mem (K := K) (b := ()) (Set.mem_singleton _) (Set.mem_singleton _))
  rw [map_sub, map_sub, sub_sub, sub_eq_zero] at h
  rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, map_sub, sub_eq_zero]
  show (FreeSh.lift K _ (val K)).app (Fin 3)
      (Finsupp.single (SMono.cast three_eq_range lcomb) 1) =
    (FreeSh.lift K _ (val K)).app (Fin 3) (Finsupp.mapDomain (SMono.cast three_eq_range)
      (Finsupp.single tcomb 1 + Finsupp.single rcomb 1))
  rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single, map_add,
    FreeSh.app_left_bin (projL K) _ (lift_gen₂ K) (lift_gen₂ K)
      (m := SMono.cast three_eq_range lcomb) rfl,
    FreeSh.app_twist_bin (projL K) _ (lift_gen₂ K) (lift_gen₂ K)
      (m := SMono.cast three_eq_range tcomb) rfl,
    FreeSh.app_right_bin (projL K) _ (lift_gen₂ K) (lift_gen₂ K)
      (m := SMono.cast three_eq_range rcomb) rfl]
  exact h

/-- **The lift of the rule is onto `Lie`.** -/
theorem presLift_surjective (A : Type) [Fintype A] [LinearOrder A] :
    Function.Surjective (((rules K).presLift (holds K)).app A) := by
  refine Rules.presLift_surjective (T := BinGen Unit) (holds K) (projL K)
    (fun A _ _ => (SymOperadIdeal.span K _).proj_surjective A) (fun k s => ?_) A
  obtain ⟨⟨g⟩, σ⟩ := s
  have hbr : (projL K).app (Fin 2) (bin2 () 1) ∈
      LinearMap.range (((rules K).presLift (holds K)).app (Fin 2)) :=
    ⟨_, Rules.presLift_gen (holds K) (by norm_num) ComGen.mu⟩
  show (projL K).app (Fin 2) (bin2 g σ.symm) ∈ _
  rcases perm2_cases σ.symm with h | h <;> rw [h]
  · exact hbr
  · have := proj_bin2_swap_anti (K := K) (r₂ := {BinRel.antisymm K ()})
      (r₃ := {BinRel.jacobi K ()}) (b := ()) (Set.mem_singleton _)
    exact (show (projL K).app (Fin 2) (bin2 () (Equiv.swap 0 1)) = _ from this) ▸
      Submodule.neg_mem _ hbr

/-! ### The Lie operad inside the Poisson operad -/

/-- The bracket of the presented shuffle Poisson operad. -/
noncomputable def valι : ∀ k, ComGen k → (PoisShGen.rules K).Presented (Fin k)
  | _, .mu => (PoisShGen.rules K).shuffleIdeal.projHom.app (Fin 2)
      (FreeSh.gen₂ K PoisShGen.br)

lemma liftι_gen₂ :
    (FreeSh.lift K (PoisShGen.rules K).Presented (valι K)).app (Fin 2)
      (FreeSh.gen₂ K ComGen.mu) =
      (PoisShGen.rules K).shuffleIdeal.projHom.app (Fin 2) (FreeSh.gen₂ K PoisShGen.br) :=
  FreeSh.lift_gen _ _ _

/-- **The Jacobi rule holds in the presented shuffle Poisson operad**, of which it is a rule. -/
theorem holdsι : (rules K).Holds (valι K) := by
  refine Rules.holds_of_lift fun r => ⟨3, three_eq_range, ?_⟩
  have h : (PoisShGen.rules K).shuffleIdeal.projHom.app (Fin 3)
      (Finsupp.single (SMono.cast three_eq_range (PoisShGen.lcomb .br .br)) 1) =
      (PoisShGen.rules K).shuffleIdeal.projHom.app (Fin 3)
        (Finsupp.mapDomain (SMono.cast three_eq_range)
          (Finsupp.single (PoisShGen.tcomb .br .br) 1 +
            Finsupp.single (PoisShGen.rcomb .br .br) 1)) :=
    Rules.proj_lead_eq (PoisShGen.rules K) PoisShGen.Rule.jac three_eq_range
  rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single, map_add] at h
  rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, map_sub, sub_eq_zero]
  show (FreeSh.lift K _ (valι K)).app (Fin 3)
      (Finsupp.single (SMono.cast three_eq_range lcomb) 1) =
    (FreeSh.lift K _ (valι K)).app (Fin 3) (Finsupp.mapDomain (SMono.cast three_eq_range)
      (Finsupp.single tcomb 1 + Finsupp.single rcomb 1))
  rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single, map_add,
    FreeSh.app_left _ (g := mu) (h := mu) (m := SMono.cast three_eq_range lcomb) rfl,
    FreeSh.app_twist _ (g := mu) (h := mu) (m := SMono.cast three_eq_range tcomb) rfl,
    FreeSh.app_right _ (g := mu) (h := mu) (m := SMono.cast three_eq_range rcomb) rfl,
    liftι_gen₂,
    ← FreeSh.app_left _ (m := SMono.cast three_eq_range (PoisShGen.lcomb .br .br)) rfl,
    ← FreeSh.app_twist _ (m := SMono.cast three_eq_range (PoisShGen.tcomb .br .br)) rfl,
    ← FreeSh.app_right _ (m := SMono.cast three_eq_range (PoisShGen.rcomb .br .br)) rfl]
  exact h

/-- **The presented shuffle operad of `Lie` maps to that of `Pois`**, the bracket to the
bracket. -/
noncomputable def ι : ShuffleOperadHom K (rules K).Presented (PoisShGen.rules K).Presented :=
  (rules K).presLift (holdsι K)

/-- The bracket to the bracket, the product to zero. -/
noncomputable def valϱ : ∀ k, PoisShGen k → (rules K).Presented (Fin k)
  | _, .mul => 0
  | _, .br => (rules K).shuffleIdeal.projHom.app (Fin 2) (FreeSh.gen₂ K ComGen.mu)

lemma liftϱ_mul :
    (FreeSh.lift K (rules K).Presented (valϱ K)).app (Fin 2) (FreeSh.gen₂ K PoisShGen.mul) = 0 :=
  FreeSh.lift_gen _ _ _

lemma liftϱ_br :
    (FreeSh.lift K (rules K).Presented (valϱ K)).app (Fin 2) (FreeSh.gen₂ K PoisShGen.br) =
      (rules K).shuffleIdeal.projHom.app (Fin 2) (FreeSh.gen₂ K ComGen.mu) :=
  FreeSh.lift_gen _ _ _

lemma liftϱ_gen₂_eq_zero {e f : PoisShGen 2} (h : e = .mul ∨ f = .mul) {C : Type} [Fintype C]
    [LinearOrder C] (i : Fin 2) (s : Without (Fin 2) i ⊕ Fin 2 ≃ C) (hs : IsShuffle i s) :
    ShuffleOperad.comp (R := K) i s hs
      ((FreeSh.lift K (rules K).Presented (valϱ K)).app (Fin 2) (FreeSh.gen₂ K e))
      ((FreeSh.lift K (rules K).Presented (valϱ K)).app (Fin 2) (FreeSh.gen₂ K f)) = 0 := by
  rcases h with rfl | rfl
  · rw [liftϱ_mul, map_zero, LinearMap.zero_apply]
  · rw [liftϱ_mul, map_zero]

lemma liftϱ_lcomb {e f : PoisShGen 2} (h : e = .mul ∨ f = .mul) :
    (FreeSh.lift K (rules K).Presented (valϱ K)).app (Fin 3)
      (Finsupp.single (SMono.cast three_eq_range (PoisShGen.lcomb e f)) 1) = 0 :=
  (FreeSh.app_left _ (g := e) (h := f) rfl).trans (liftϱ_gen₂_eq_zero K h _ _ _)

lemma liftϱ_tcomb {e f : PoisShGen 2} (h : e = .mul ∨ f = .mul) :
    (FreeSh.lift K (rules K).Presented (valϱ K)).app (Fin 3)
      (Finsupp.single (SMono.cast three_eq_range (PoisShGen.tcomb e f)) 1) = 0 :=
  (FreeSh.app_twist _ (g := e) (h := f) rfl).trans (liftϱ_gen₂_eq_zero K h _ _ _)

lemma liftϱ_rcomb {e f : PoisShGen 2} (h : e = .mul ∨ f = .mul) :
    (FreeSh.lift K (rules K).Presented (valϱ K)).app (Fin 3)
      (Finsupp.single (SMono.cast three_eq_range (PoisShGen.rcomb e f)) 1) = 0 :=
  (FreeSh.app_right _ (g := e) (h := f) rfl).trans (liftϱ_gen₂_eq_zero K h _ _ _)

/-- **The rules of `Pois` hold in the presented shuffle operad of `Lie`** when the product goes
to zero: the Jacobi rule is its rule, and every monomial of the other rules has a product. -/
theorem holdsϱ : (PoisShGen.rules K).Holds (valϱ K) := by
  refine Rules.holds_of_lift fun r => ⟨3, three_eq_range, ?_⟩
  rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, map_sub, sub_eq_zero]
  cases r
  · have h : (rules K).shuffleIdeal.projHom.app (Fin 3)
        (Finsupp.single (SMono.cast three_eq_range lcomb) 1) =
        (rules K).shuffleIdeal.projHom.app (Fin 3) (Finsupp.mapDomain (SMono.cast three_eq_range)
          (Finsupp.single tcomb 1 + Finsupp.single rcomb 1)) :=
      Rules.proj_lead_eq (rules K) () three_eq_range
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single, map_add] at h
    show (FreeSh.lift K _ (valϱ K)).app (Fin 3)
        (Finsupp.single (SMono.cast three_eq_range (PoisShGen.lcomb .br .br)) 1) =
      (FreeSh.lift K _ (valϱ K)).app (Fin 3) (Finsupp.mapDomain (SMono.cast three_eq_range)
        (Finsupp.single (PoisShGen.tcomb .br .br) 1 + Finsupp.single (PoisShGen.rcomb .br .br) 1))
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single, map_add,
      FreeSh.app_left _ (g := PoisShGen.br) (h := PoisShGen.br)
        (m := SMono.cast three_eq_range (PoisShGen.lcomb .br .br)) rfl,
      FreeSh.app_twist _ (g := PoisShGen.br) (h := PoisShGen.br)
        (m := SMono.cast three_eq_range (PoisShGen.tcomb .br .br)) rfl,
      FreeSh.app_right _ (g := PoisShGen.br) (h := PoisShGen.br)
        (m := SMono.cast three_eq_range (PoisShGen.rcomb .br .br)) rfl,
      liftϱ_br,
      ← FreeSh.app_left _ (m := SMono.cast three_eq_range lcomb) rfl,
      ← FreeSh.app_twist _ (m := SMono.cast three_eq_range tcomb) rfl,
      ← FreeSh.app_right _ (m := SMono.cast three_eq_range rcomb) rfl]
    exact h
  · show (FreeSh.lift K _ (valϱ K)).app (Fin 3)
        (Finsupp.single (SMono.cast three_eq_range (PoisShGen.rcomb .br .mul)) 1) =
      (FreeSh.lift K _ (valϱ K)).app (Fin 3) (Finsupp.mapDomain (SMono.cast three_eq_range)
        (Finsupp.single (PoisShGen.lcomb .mul .br) 1 + Finsupp.single (PoisShGen.tcomb .mul .br) 1))
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single, map_add,
      liftϱ_rcomb K (Or.inr rfl), liftϱ_lcomb K (Or.inl rfl), liftϱ_tcomb K (Or.inl rfl), add_zero]
  · show (FreeSh.lift K _ (valϱ K)).app (Fin 3)
        (Finsupp.single (SMono.cast three_eq_range (PoisShGen.tcomb .br .mul)) 1) =
      (FreeSh.lift K _ (valϱ K)).app (Fin 3) (Finsupp.mapDomain (SMono.cast three_eq_range)
        (Finsupp.single (PoisShGen.lcomb .mul .br) 1 - Finsupp.single (PoisShGen.rcomb .mul .br) 1))
    rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, Finsupp.mapDomain_single, map_sub,
      liftϱ_tcomb K (Or.inr rfl), liftϱ_lcomb K (Or.inl rfl), liftϱ_rcomb K (Or.inl rfl), sub_zero]
  · show (FreeSh.lift K _ (valϱ K)).app (Fin 3)
        (Finsupp.single (SMono.cast three_eq_range (PoisShGen.lcomb .br .mul)) 1) =
      (FreeSh.lift K _ (valϱ K)).app (Fin 3) (Finsupp.mapDomain (SMono.cast three_eq_range)
        (Finsupp.single (PoisShGen.tcomb .mul .br) 1 + Finsupp.single (PoisShGen.rcomb .mul .br) 1))
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single, map_add,
      liftϱ_lcomb K (Or.inr rfl), liftϱ_tcomb K (Or.inl rfl), liftϱ_rcomb K (Or.inl rfl), add_zero]
  · show (FreeSh.lift K _ (valϱ K)).app (Fin 3)
        (Finsupp.single (SMono.cast three_eq_range (PoisShGen.rcomb .mul .mul)) 1) =
      (FreeSh.lift K _ (valϱ K)).app (Fin 3) (Finsupp.mapDomain (SMono.cast three_eq_range)
        (Finsupp.single (PoisShGen.lcomb .mul .mul) 1))
    rw [Finsupp.mapDomain_single, liftϱ_rcomb K (Or.inl rfl), liftϱ_lcomb K (Or.inl rfl)]
  · show (FreeSh.lift K _ (valϱ K)).app (Fin 3)
        (Finsupp.single (SMono.cast three_eq_range (PoisShGen.tcomb .mul .mul)) 1) =
      (FreeSh.lift K _ (valϱ K)).app (Fin 3) (Finsupp.mapDomain (SMono.cast three_eq_range)
        (Finsupp.single (PoisShGen.lcomb .mul .mul) 1))
    rw [Finsupp.mapDomain_single, liftϱ_tcomb K (Or.inl rfl), liftϱ_lcomb K (Or.inl rfl)]

/-- **The retraction**: the presented shuffle operad of `Pois` maps to that of `Lie`, the bracket
to the bracket and the product to zero. -/
noncomputable def ϱ : ShuffleOperadHom K (PoisShGen.rules K).Presented (rules K).Presented :=
  (PoisShGen.rules K).presLift (holdsϱ K)

/-- **The retraction is a left inverse.** -/
theorem ϱ_comp_ι : (ϱ K).comp (ι K) = ShuffleOperadHom.id :=
  Rules.presented_hom_ext fun k hk g => by
    cases g
    exact (congrArg ((ϱ K).app (Fin 2)) (Rules.presLift_gen (holdsι K) hk ComGen.mu)).trans
      (Rules.presLift_gen (holdsϱ K) (by norm_num) PoisShGen.br)

lemma ι_injective (A : Type) [Fintype A] [LinearOrder A] : Function.Injective ((ι K).app A) :=
  Function.LeftInverse.injective (g := (ϱ K).app A) fun x =>
    congrArg (fun φ : ShuffleOperadHom K (rules K).Presented (rules K).Presented => φ.app A x)
      (ϱ_comp_ι K)

end LieSh

namespace Lie

variable (K : Type u) [Field K]

/-- **The morphism from `Lie` to `Pois`**: the bracket to the bracket. -/
noncomputable def toPois : SymOperadHom K (Lie K) (Pois K) :=
  BinPres.renameHom (r₂ := {BinRel.antisymm K ()}) (r₃ := {BinRel.jacobi K ()})
    (s₂ := PoisDim.r₂P K) (s₃ := PoisDim.r₃P K) (fun _ => PoisOp.bracket) (fun _ => 1)
    (fun x hx => by
      rw [Set.mem_singleton_iff.1 hx, BinRel.antisymm, map_add, rename_bin2, rename_bin2,
        one_smul, one_smul]
      exact SymOperadIdeal.subset_span (r := rel23 (PoisDim.r₂P K) (PoisDim.r₃P K)) 2
        (Or.inr rfl))
    (fun x hx => by
      rw [Set.mem_singleton_iff.1 hx, BinRel.jacobi, map_add, map_add, rename_binL, rename_binL,
        rename_binL, mul_one, one_smul, one_smul, one_smul]
      exact SymOperadIdeal.subset_span (r := rel23 (PoisDim.r₂P K) (PoisDim.r₃P K)) 3
        (Or.inr (Or.inl rfl)))

lemma toPois_bracket :
    (toPois K).app (Fin 2) ((LieSh.projL K).app (Fin 2) (bin2 () 1)) =
      (PoisShGen.projP K).app (Fin 2) (bin2 PoisOp.bracket 1) := by
  show (PoisShGen.projP K).app (Fin 2) ((rename K (fun _ => PoisOp.bracket) (fun _ => 1)).app _
    (bin2 () 1)) = _
  rw [rename_bin2, one_smul]

end Lie

namespace LieSh

open ComGen

variable (K : Type u) [Field K]

/-- **The two lifts commute with the morphisms to `Pois`.** -/
theorem toPois_comp_presLift :
    (Lie.toPois K).toShuffle.comp ((rules K).presLift (holds K)) =
      ((PoisShGen.rules K).presLift (PoisShGen.holds K)).comp (ι K) :=
  Rules.presented_hom_ext fun k hk g => by
    cases g
    show (Lie.toPois K).app (Fin 2) (((rules K).presLift (holds K)).app (Fin 2) _) =
      ((PoisShGen.rules K).presLift (PoisShGen.holds K)).app (Fin 2) ((ι K).app (Fin 2) _)
    rw [Rules.presLift_gen (holds K) hk ComGen.mu]
    refine (Lie.toPois_bracket K).trans ?_
    exact ((congrArg (((PoisShGen.rules K).presLift (PoisShGen.holds K)).app (Fin 2))
      (Rules.presLift_gen (holdsι K) hk ComGen.mu)).trans
      (Rules.presLift_gen (PoisShGen.holds K) (by norm_num) PoisShGen.br)).symm

/-- **The lift of the rule is bijective** in every arity: it is onto, and injective because its
composite with the morphism to `Pois` is the injection of the presented operads followed by the
isomorphism for `Pois`. -/
theorem presLift_bijective (A : Type) [Fintype A] [LinearOrder A] :
    Function.Bijective (((rules K).presLift (holds K)).app A) := by
  refine ⟨fun x y hxy => ι_injective K A ((PoisShGen.presLift_bijective K A).1 ?_),
    presLift_surjective K A⟩
  have h := fun z => congrArg (fun φ : ShuffleOperadHom K (rules K).Presented (Shuf (Pois K)) =>
    φ.app A z) (toPois_comp_presLift K)
  exact ((h x).symm.trans (congrArg ((Lie.toPois K).app A) hxy)).trans (h y)

/-- **The shuffle operad presented by the Jacobi rule is the underlying shuffle operad of the
Lie operad.** -/
noncomputable def presIso : ShuffleOperadIso K (rules K).Presented (Shuf (Lie K)) :=
  ShuffleOperadIso.ofBijective _ (presLift_bijective K)

/-- **The isomorphism sends the generator to the bracket.** -/
theorem presIso_gen :
    (presIso K).hom.app (Fin 2) ((rules K).shuffleIdeal.proj _
      (Finsupp.single (FreeSh.genM (by norm_num) ComGen.mu) 1)) =
      (projL K).app (Fin 2) (bin2 () 1) :=
  Rules.presLift_gen (holds K) _ ComGen.mu

end LieSh

namespace Lie

variable (K : Type u) [Field K]

/-- The morphism from `Lie` to `Pois` is injective on every finite linear order. -/
theorem toPois_injective_of_linearOrder (A : Type) [Fintype A] [LinearOrder A] :
    Function.Injective ((toPois K).app A) := by
  intro x y hxy
  obtain ⟨x', rfl⟩ := LieSh.presLift_surjective K A x
  obtain ⟨y', rfl⟩ := LieSh.presLift_surjective K A y
  have h := fun z => congrArg (fun φ : ShuffleOperadHom K (LieSh.rules K).Presented
    (Shuf (Pois K)) => φ.app A z) (LieSh.toPois_comp_presLift K)
  exact congrArg _ (LieSh.ι_injective K A ((PoisShGen.presLift_bijective K A).1
    (((h x').symm.trans hxy).trans (h y'))))

/-- **`Lie` is a suboperad of `Pois`**: the morphism sending the bracket to the bracket is
injective on every finite set of inputs. -/
theorem toPois_injective (A : Type) [Fintype A] [d : DecidableEq A] :
    Function.Injective ((toPois K).app A) := by
  let lo : LinearOrder A := LinearOrder.lift' (Fintype.equivFin A) (Fintype.equivFin A).injective
  have hd : d = lo.toDecidableEq := Subsingleton.elim _ _
  subst hd
  exact toPois_injective_of_linearOrder K A

end Lie

end Operad
