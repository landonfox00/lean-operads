/-
# Morphisms preserve the signed circle product and the graded bracket

A morphism of non-symmetric operads commutes with the reindexings and the positional compositions
`compFin` (`NSOperadHom.app_reindex`, `NSOperadHom.app_compFin`), hence with the signed circle
product `⋆ₛ` (`NSOperadHom.app_sstar`) and the graded bracket `⁅-, -⁆ₛ`
(`NSOperadHom.app_gbracket`) of `Operad.DG`. Applied to the projection onto a quotient operad,
this transports Maurer–Cartan elements and twisted differentials to the quotient.
-/
import Operad.DG

universe u v w

namespace Operad

open NSOperad

namespace NSOperadHom

variable {R : Type u} [CommRing R] {P : ℕ → Type v}
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]
  {Q : ℕ → Type w} [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)] [NSOperad R Q]
  (φ : NSOperadHom R P Q)

/-- **Morphisms preserve the signed circle product.** -/
lemma app_sstar {j k : ℕ} (α : P (j + 1)) (β : P (k + 1)) :
    φ.app (j + k + 1) (sstar (R := R) α β)
      = sstar (R := R) (φ.app (j + 1) α) (φ.app (k + 1) β) := by
  rw [sstar_def, sstar_def]
  refine (map_sum (φ.app (j + k + 1)) _ _).trans (Finset.sum_congr rfl fun a _ => ?_)
  exact (LinearMap.map_smul (φ.app (j + k + 1)) _ _).trans
    (congrArg (fun z => ((-1 : R) ^ ((a : ℕ) * k)) • z) (φ.app_compFin a α β))

/-- **Morphisms preserve the graded bracket.** -/
lemma app_gbracket {j k : ℕ} (α : P (j + 1)) (β : P (k + 1)) :
    φ.app (j + k + 1) (gbracket (R := R) α β)
      = gbracket (R := R) (φ.app (j + 1) α) (φ.app (k + 1) β) := by
  rw [gbracket, gbracket, map_sub, map_smul, φ.app_sstar, φ.app_reindex, φ.app_sstar]

end NSOperadHom

end Operad
