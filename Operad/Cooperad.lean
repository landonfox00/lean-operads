/-
# Non-symmetric cooperads

The dual of `Operad.NSOperad`, in the same positional convention. Where an operad has partial
composition `comp a b : P (a+1+b) → P n → P (a+n+b)`, a cooperad has *infinitesimal
decomposition*

`decomp a b n : C (a + n + b) →ₗ C (a + 1 + b) ⊗ C n`,

splitting off the sub-operation occupying the `n` slots after the first `a`. Every axiom below is
the corresponding operad axiom with the arrows reversed.

Unlike the operad axioms these cannot be stated elementwise: a tensor product has no description
by elements, so each axiom is an equality of linear maps. That is the only real difference — the
`reindex` machinery of `Operad.Basic` carries over unchanged, because it is generic in the family
`ℕ → Type v`.
-/
import Operad.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator

universe u v

namespace Operad

open scoped TensorProduct

/-- Swap the last two tensor factors. The parallel coassociativity axiom needs it, because the
two ways of decomposing at disjoint slots produce the same three pieces in opposite order. -/
noncomputable def swapLast (R : Type u) [CommRing R] (X Y Z : Type v)
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z] :
    (X ⊗[R] Y) ⊗[R] Z ≃ₗ[R] (X ⊗[R] Z) ⊗[R] Y :=
  (TensorProduct.assoc R X Y Z).trans
    ((TensorProduct.congr (LinearEquiv.refl R X) (TensorProduct.comm R Y Z)).trans
      (TensorProduct.assoc R X Z Y).symm)

/-- A non-symmetric cooperad in `R`-modules, in the positional convention. -/
class NSCooperad (R : Type u) [CommRing R] (C : ℕ → Type v)
    [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)] where
  /-- The counit, dual to the identity operation. -/
  counit : C 1 →ₗ[R] R
  /-- Infinitesimal decomposition: split off the `n` slots sitting after the first `a`. -/
  decomp (a b n : ℕ) : C (a + n + b) →ₗ[R] C (a + 1 + b) ⊗[R] C n
  /-- Dual to `comp_one_right`: splitting off a single slot and counting it changes nothing. -/
  rid_counit_decomp (a b : ℕ) :
    (TensorProduct.rid R (C (a + 1 + b))).toLinearMap ∘ₗ
        LinearMap.lTensor (C (a + 1 + b)) counit ∘ₗ decomp a b 1
      = LinearMap.id
  /-- Dual to `comp_one_left`: splitting off everything and counting the outer part changes
  nothing. -/
  lid_counit_decomp (n : ℕ) :
    (TensorProduct.lid R (C n)).toLinearMap ∘ₗ
        LinearMap.rTensor (C n) counit ∘ₗ decomp 0 0 n
      = (reindex R C (show 0 + n + 0 = n by omega)).toLinearMap
  /-- Dual to `comp_assoc_seq`: decomposing twice in sequence. -/
  decomp_assoc_seq (a b c d p : ℕ) :
    LinearMap.lTensor (C (a + 1 + b)) (decomp c d p) ∘ₗ decomp a b (c + p + d)
      = (TensorProduct.assoc R (C (a + 1 + b)) (C (c + 1 + d)) (C p)).toLinearMap ∘ₗ
          LinearMap.rTensor (C p)
            (decomp a b (c + 1 + d) ∘ₗ
              (reindex R C (show a + c + 1 + (d + b) = a + (c + 1 + d) + b by omega)).toLinearMap)
            ∘ₗ decomp (a + c) (d + b) p ∘ₗ
          (reindex R C (show a + (c + p + d) + b = a + c + p + (d + b) by omega)).toLinearMap
  /-- Dual to `comp_assoc_par`: decomposing at two disjoint slots, in either order. -/
  decomp_assoc_par (a b c n p : ℕ) :
    LinearMap.rTensor (C p)
        (decomp a (b + 1 + c) n ∘ₗ
          (reindex R C (show a + n + b + 1 + c = a + n + (b + 1 + c) by omega)).toLinearMap) ∘ₗ
      decomp (a + n + b) c p
      = (swapLast R (C (a + 1 + (b + 1 + c))) (C p) (C n)).toLinearMap ∘ₗ
          LinearMap.rTensor (C n)
            ((TensorProduct.congr
                (reindex R C (show a + 1 + b + 1 + c = a + 1 + (b + 1 + c) by omega))
                (LinearEquiv.refl R (C p))).toLinearMap ∘ₗ
              decomp (a + 1 + b) c p ∘ₗ
              (reindex R C
                (show a + 1 + (b + p + c) = a + 1 + b + p + c by omega)).toLinearMap) ∘ₗ
          decomp a (b + p + c) n ∘ₗ
          (reindex R C (show a + n + b + p + c = a + n + (b + p + c) by omega)).toLinearMap

/-! ### The associative cooperad

`Ass R` is `R` in every arity, so it carries a cooperad structure as well as an operad one: the
decomposition is the canonical `R ≃ R ⊗ R`. Beyond being the first example, this validates the
axioms above — a mis-stated coassociativity would show up here as an unprovable goal. -/

/-- **The associative cooperad.** -/
noncomputable instance instNSCooperadAss (R : Type u) [CommRing R] : NSCooperad R (Ass R) where
  counit := LinearMap.id
  decomp _ _ _ := (TensorProduct.rid R R).symm.toLinearMap
  rid_counit_decomp a b := by ext; simp
  lid_counit_decomp n := by ext; simp [reindex_ass]
  decomp_assoc_seq a b c d p := by ext; simp [reindex_ass]
  decomp_assoc_par a b c n p := by ext; simp [reindex_ass, swapLast]

end Operad
