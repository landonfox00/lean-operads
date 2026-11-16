/-
# Gröbner bases make presented symmetric operads Koszul

Let `E` be a graded linear species over a field `K` of characteristic zero with an even basis
`c k` of each `E (Fin k)` indexed by `BinGen G k`, and `r` relators concentrated in arity three,
spanning a subspace of `T(E) (Fin 3)` stable under the permutations of `Fin 3`. The bridge
`ShuffleBarSym.isKoszul_iff_shuffle` identifies the Koszulness of the presented operad
`T(E)/(r)` (`Koszul.IsKoszul`) with that of the shuffle operad presented by the shuffle relators
`Rsh c hc r` (`ShuffleBar.IsKoszul`). This file composes it with the Gröbner criteria on the
shuffle side.

* **A quadratic Gröbner basis** (`ShuffleBarSym.isKoszul_of_isGroebner`): if the shuffle
  relators are a quadratic Gröbner basis (`LTree.IsGroebner`), then `T(E)/(r)` is Koszul. This is
  the criterion of Dotsenko and Khoroshkin (`ShuffleBar.isKoszul`) for a symmetric operad.
* **Rules** (`ShuffleBarSym.isKoszul_iff_rules`): for rewriting rules on the leaves `0, 1, 2`
  whose vectors span the shuffle relators, `T(E)/(r)` is Koszul iff the rules are
  (`STree.Rules.IsKoszul`, through `ShuffleBridge.isKoszul_iff`).
* **Resolvable critical ambiguities** (`ShuffleBarSym.isKoszul_of_critical`): if the critical
  ambiguities of such rules are resolvable, then `T(E)/(r)` is Koszul. This is the Buchberger
  criterion of `Operad/ShuffleAnyGroebner.lean` followed by "PBW implies Koszul"
  (`STree.Rules.isKoszul_of_critical`).
-/
import Operad.ShuffleBarJ
import Operad.ShuffleBridgeBar

universe u

namespace Operad

open Sym GerBV STree

namespace ShuffleBarSym

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]

section Groebner

variable {G : Type} [Fintype G] [DecidableEq G]
  (c : ∀ k, Module.Basis (BinGen G k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen G k), GrSpecies.par (R := K) false (c k β) = c k β)
  {r : ∀ n : ℕ, Set (FreeGrL K E (Fin n))}

/-- **A quadratic Gröbner basis makes the presented symmetric operad Koszul** (Dotsenko and
Khoroshkin): for an even binary graded linear species `E` over a field of characteristic zero and
relators concentrated in arity three, spanning a subspace stable under the permutations of
`Fin 3`, if the shuffle relators `Rsh` are a quadratic Gröbner basis then `T(E)/(r)` is
Koszul. -/
theorem isKoszul_of_isGroebner [CharZero K] (hr3 : ∀ n ≠ 3, r n = ∅)
    (hrS : ∀ σ : Equiv.Perm (Fin 3), ∀ x ∈ r 3,
      GrOperad.map (R := K) σ x ∈ Submodule.span K (r 3))
    (rk : G → ℕ) {L : Set (LTree G)} (hG : LTree.IsGroebner K rk L (Rsh c hc r)) :
    Koszul.IsKoszul K E r :=
  (isKoszul_iff_shuffle c hc hr3 hrS).2 (ShuffleBar.isKoszul K rk hG)

end Groebner

section Rules

open ShuffleBridge

variable {F : ℕ → Type} [BinaryGens F] [Fintype (F 2)] [DecidableEq (F 2)]
  (c : ∀ k, Module.Basis (BinGen (F 2) k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen (F 2) k), GrSpecies.par (R := K) false (c k β) = c k β)
  {r : ∀ n : ℕ, Set (FreeGrL K E (Fin n))}
  {ρ : Type*} {O : AdmOrder F} (Gr : Rules K ρ O.toCtxOrder)
  (hsrc : ∀ q, Gr.src q = Finset.range 3)
  (hR : (Rsh c hc r).map (vecEquiv F K 3).toLinearMap
    = Submodule.span K (Set.range (ruleVec Gr hsrc)))

include hR in
/-- **The presented symmetric operad is Koszul iff its rules are**: for rewriting rules on the
leaves `0, 1, 2` whose vectors span the shuffle relators, `Koszul.IsKoszul` is the Koszulness of
the shuffle operad with generators of any arity presented by the rules. -/
theorem isKoszul_iff_rules [CharZero K] (hr3 : ∀ n ≠ 3, r n = ∅)
    (hrS : ∀ σ : Equiv.Perm (Fin 3), ∀ x ∈ r 3,
      GrOperad.map (R := K) σ x ∈ Submodule.span K (r 3)) :
    Koszul.IsKoszul K E r ↔ Gr.IsKoszul :=
  (isKoszul_iff_shuffle c hc hr3 hrS).trans (ShuffleBridge.isKoszul_iff Gr hsrc hR)

include hR in
/-- **Resolvable critical ambiguities make the presented symmetric operad Koszul**: if the
critical ambiguities of rules on the leaves `0, 1, 2` whose vectors span the shuffle relators are
resolvable, so that the normal monomials are a basis of the shuffle operad, then `T(E)/(r)` is
Koszul. -/
theorem isKoszul_of_critical [CharZero K] (hr3 : ∀ n ≠ 3, r n = ∅)
    (hrS : ∀ σ : Equiv.Perm (Fin 3), ∀ x ∈ r 3,
      GrOperad.map (R := K) σ x ∈ Submodule.span K (r 3))
    (hcrit : ∀ {C : Finset ℕ} {r₁ r₂ : ρ} (B : Gr.Amb C r₁ r₂), Critical Gr B → B.Res) :
    Koszul.IsKoszul K E r :=
  (isKoszul_iff_rules c hc Gr hsrc hR hr3 hrS).2
    (Gr.isKoszul_of_critical (fun q => weight_eq_two (hsrc q) _)
      (fun q m _ => weight_eq_two (hsrc q) m) hcrit)

end Rules

end ShuffleBarSym

end Operad
