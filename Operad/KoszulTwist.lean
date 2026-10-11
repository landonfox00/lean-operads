/-
# Twisting on a Koszul dual

For a slice-closed collection `C` of chains — the Koszul dual of a binary quadratic presentation
is one (`TConv.koszulDual_sliceClosed`) — a cochain matters only through its values on `C`: the
cochains vanishing on `C` form the operad ideal `TConv.ann`, and `HomOp C` is the quotient. The
projection is a morphism of operads, so it carries signed products and brackets along
(`NSOperadHom.app_sstar`, `NSOperadHom.app_gbracket`). Hence, at the level of cochains:

* `TConv.eval_gbracket_congr`: the bracket with a fixed cochain respects agreement on `C`;
* `TConv.eval_gbracket_gbracket_eq_zero`: **at a Koszul-dual Maurer–Cartan element** — a binary
  cochain `T` with `T ⋆ₛ T` vanishing on `C 3` — the twisted differential `⁅T, -⁆ₛ` squares to
  zero on `C`. This is `Operad.dLin_dLin` in `HomOp C`, read back on cochains; `T` itself need
  not be Maurer–Cartan in the convolution operad of all trees.
-/
import Operad.KoszulDual
import Operad.Cohomology
import Operad.DGHom

universe u v w

namespace Operad

open NSOperad

namespace TConv

variable {R : Type u} [CommRing R] {E : Type v} [Fintype E] [DecidableEq E]
  {Q : ℕ → Type w} [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)] [NSOperad R Q]
  {C : ∀ n, Submodule R (Chain R E n)} (hC : SliceClosed R E C)

include hC in
/-- Two cochains have the same image in `HomOp C` exactly when they agree on `C`. -/
lemma projHom_app_eq_iff {n : ℕ} (f g : TConv R E Q n) :
    (ann Q hC).projHom.app n f = (ann Q hC).projHom.app n g ↔
      ∀ x ∈ C n, eval f x = eval g x := by
  show Submodule.Quotient.mk f = Submodule.Quotient.mk g ↔ _
  rw [Submodule.Quotient.eq]
  constructor
  · intro h x hx
    have h' : eval (f - g) x = 0 := h x hx
    rwa [eval_sub, sub_eq_zero] at h'
  · intro h x hx
    show eval (f - g) x = 0
    rw [eval_sub, h x hx, sub_self]

include hC in
/-- **The bracket respects agreement on a slice-closed collection.** -/
theorem eval_gbracket_congr {j k : ℕ} (α : TConv R E Q (j + 1)) {θ θ' : TConv R E Q (k + 1)}
    (h : ∀ x ∈ C (k + 1), eval θ x = eval θ' x) :
    ∀ x ∈ C (j + k + 1), eval (gbracket (R := R) α θ) x = eval (gbracket (R := R) α θ') x := by
  rw [← projHom_app_eq_iff hC] at h ⊢
  rw [NSOperadHom.app_gbracket, NSOperadHom.app_gbracket, h]

include hC in
/-- **Twisting at a Koszul-dual Maurer–Cartan element squares to zero on the Koszul dual.** If
`T ⋆ₛ T` vanishes on `C 3`, then `⁅T, ⁅T, ψ⁆ₛ⁆ₛ` vanishes on `C` for every cochain `ψ`. -/
theorem eval_gbracket_gbracket_eq_zero [Invertible (2 : R)] (T : TConv R E Q 2)
    (hT : ∀ x ∈ C 3, eval (sstar (R := R) (j := 1) (k := 1) T T) x = 0) (m : ℕ)
    (ψ : TConv R E Q (m + 1)) :
    ∀ x ∈ C (1 + (1 + m) + 1), eval (gbracket (R := R) (j := 1) (k := 1 + m) T
      (gbracket (R := R) (j := 1) (k := m) T ψ)) x = 0 := by
  set π := (ann Q hC).projHom
  have hMC : sstar (R := R) (P := HomOp Q hC) (j := 1) (k := 1) (π.app 2 T) (π.app 2 T) = 0 := by
    rw [← NSOperadHom.app_sstar]
    show Submodule.Quotient.mk _ = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hT
  have key := dLin_dLin (R := R) (P := HomOp Q hC) (π.app 2 T) hMC m (π.app (m + 1) ψ)
  simp only [dLin_apply] at key
  rw [← NSOperadHom.app_gbracket, ← NSOperadHom.app_gbracket] at key
  intro x hx
  exact (Submodule.Quotient.mk_eq_zero _).1 key x hx

end TConv

end Operad
