/-
# The symmetric presentation of `Pois` is Koszul

Step 3 of the bridge between symmetric and shuffle operads (Dotsenko–Khoroshkin), for the Poisson
operad. Over a field `K` of characteristic zero:

* **The generators** (`SymPresPois.E`): the regular representation `Reg2 K` of `𝔖₂` in arity
  two, two-dimensional and even, which is the trivial representation plus the sign
  representation: the basis `SymPresPois.c` is the symmetric vector `(1 + τ)/2`, the commutative
  product `x₁x₂` (`PoisShGen.mul`), and the antisymmetric vector `(1 - τ)/2`, the bracket
  `[x₁, x₂]` (`PoisShGen.br`), `τ` the transposition (`SymPresPois.val_c`).
* **The relators** (`SymPresPois.rel`): the operations of arity three which vanish in the Poisson
  algebra of polynomials in words with its Kirillov–Kostant bracket `PoisDim.W K`
  (`SymPresPois.φ`, through `SymPresB.model` of the product plus the bracket), that is, all the
  relations of arity three among a commutative associative product and a Lie bracket satisfying
  the Leibniz rule: associativity, the Jacobi identity and the Leibniz rule span them. They are
  concentrated in arity three and stable under `𝔖₃`.
* **Their shuffle relators are those of `Pois`** (`SymPresPois.Rsh_eq`):
  `ShuffleBarSym.Rsh = PoisBin.rel K`. One inclusion evaluates at the one-letter words; for the
  other, `PoisBin.rel K` is spanned by the six relators `PoisBin.relB` of the rules, and each
  vanishes on every family of inputs by the identities of the Poisson algebra `PoisDim.W K`
  (`SymPresPois.relB_vanish`).
* Hence **the symmetric operad `Pois = T(E)/(rel)` is Koszul** (`SymPresPois.isKoszul`), by the
  bridge `ShuffleBarSym.isKoszul_iff_shuffle` and `PoisBin.isKoszul`.

The comparison of `T(E)/(rel)` with the library's presentation `Pois` of `BinaryQuadratic.lean`
is not made here.
-/
import Operad.SymPresBinB
import Operad.ShuffleBinPois

universe u

namespace Operad

namespace SymPresPois

open Sym SymPresB PoisShGen MvPolynomial KK

variable (K : Type u) [Field K] [CharZero K]

/-- The two numberings of `Fin 2`, as a case split. -/
lemma perm_two (τ : Fin 2 ≃ Fin 2) : τ = Equiv.refl _ ∨ τ = Equiv.swap 0 1 := by
  revert τ
  decide

lemma refl_ne_swap : (Equiv.refl (Fin 2)) ≠ Equiv.swap 0 1 := by decide

/-- **The coordinates of the trivial and the sign parts**: `f ↦ (f 1 + f τ, f 1 - f τ)`. -/
noncomputable def coordEquiv : Reg2 K (Fin 2) ≃ₗ[K] (PoisShGen 2 → K) where
  toFun f g := match g with
    | .mul => f.val (Equiv.refl _) + f.val (Equiv.swap 0 1)
    | .br => f.val (Equiv.refl _) - f.val (Equiv.swap 0 1)
  invFun h := show (Fin 2 ≃ Fin 2) → K from fun τ =>
    if τ = Equiv.refl _ then (h .mul + h .br) / 2 else (h .mul - h .br) / 2
  map_add' f g := by
    funext e
    cases e <;> simp only [Reg2.val_add, Pi.add_apply] <;> ring
  map_smul' a f := by
    funext e
    cases e <;> simp only [Reg2.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring
  left_inv f := by
    funext τ
    show (if τ = Equiv.refl _ then _ else _) = f.val τ
    rcases perm_two τ with rfl | rfl
    · rw [if_pos rfl]
      ring
    · rw [if_neg refl_ne_swap.symm]
      ring
  right_inv h := by
    funext e
    have h1 : (if Equiv.refl (Fin 2) = Equiv.refl _ then (h .mul + h .br) / 2
      else (h .mul - h .br) / 2) = (h .mul + h .br) / 2 := if_pos rfl
    have h2 : (if Equiv.swap (0 : Fin 2) 1 = Equiv.refl _ then (h .mul + h .br) / 2
      else (h .mul - h .br) / 2) = (h .mul - h .br) / 2 := if_neg refl_ne_swap.symm
    cases e
    · show (if Equiv.refl (Fin 2) = Equiv.refl _ then (h .mul + h .br) / 2
          else (h .mul - h .br) / 2) + (if Equiv.swap (0 : Fin 2) 1 = Equiv.refl _ then
          (h .mul + h .br) / 2 else (h .mul - h .br) / 2) = h .mul
      rw [h1, h2]
      ring
    · show (if Equiv.refl (Fin 2) = Equiv.refl _ then (h .mul + h .br) / 2
          else (h .mul - h .br) / 2) - (if Equiv.swap (0 : Fin 2) 1 = Equiv.refl _ then
          (h .mul + h .br) / 2 else (h .mul - h .br) / 2) = h .br
      rw [h1, h2]
      ring

lemma symm_refl (h : PoisShGen 2 → K) :
    (coordEquiv K).symm h (Equiv.refl _) = (h .mul + h .br) / 2 := by
  show (if Equiv.refl (Fin 2) = Equiv.refl _ then (h .mul + h .br) / 2
    else (h .mul - h .br) / 2) = _
  rw [if_pos rfl]

lemma symm_swap (h : PoisShGen 2 → K) :
    (coordEquiv K).symm h (Equiv.swap 0 1) = (h .mul - h .br) / 2 := by
  show (if Equiv.swap (0 : Fin 2) 1 = Equiv.refl _ then (h .mul + h .br) / 2
    else (h .mul - h .br) / 2) = _
  rw [if_neg refl_ne_swap.symm]

/-- **The generators of `Pois`**: the regular representation of `𝔖₂` in arity two, the trivial
plus the sign representation. -/
abbrev E := Reg2 K

/-- The basis of `E (Fin 2)`: the symmetric vector `(1 + τ)/2` and the antisymmetric `(1 - τ)/2`.
-/
noncomputable def basis2 : Module.Basis (PoisShGen 2) K (Reg2 K (Fin 2)) :=
  Module.Basis.ofEquivFun (coordEquiv K)

/-- **The basis of the generators**, indexed by `BinGen (PoisShGen 2)`. -/
noncomputable def c : ∀ k, Module.Basis (BinGen (PoisShGen 2) k) K (Reg2 K (Fin k)) :=
  FreeL.binBasisOf (basis2 K) fun _ hk => Reg2.subsingleton hk

/-- The basis vectors are even. -/
lemma hc : ∀ k (β : BinGen (PoisShGen 2) k), GrSpecies.par (R := K) false (c K k β) = c K k β :=
  fun _ _ => Reg2.par_false _

/-- The Kirillov–Kostant bracket of the polynomials in words. -/
local notation "𝔟" => bracket (wordBracket K)

/-- **The product plus the bracket**, the bilinear map of the model. -/
noncomputable def mb : PoisDim.W K →ₗ[K] PoisDim.W K →ₗ[K] PoisDim.W K :=
  LinearMap.mul K (PoisDim.W K) + bracketL (wordBracket K)

/-- **The evaluation in the Poisson algebra of polynomials in words.** -/
noncomputable def φ : GrOperadHom K (FreeGrL K (Reg2 K)) (SymGr (EndOp K (PoisDim.W K))) :=
  model (mb K)

/-- **The relators of `Pois`**: the operations of arity three vanishing in the Poisson algebra of
polynomials in words, and none in the other arities. -/
def rel : ∀ n : ℕ, Set (FreeGrL K (Reg2 K) (Fin n)) := kerRel (φ K)

variable {K}

lemma val_c (g : PoisShGen 2) (τ : Fin 2 ≃ Fin 2) :
    (c K 2 (BinGen.op g)).val τ = (coordEquiv K).symm (Pi.single g 1) τ := by
  rw [c, FreeL.binBasisOf_op, basis2, Module.Basis.coe_ofEquivFun]
  rfl

lemma μ_mul (x y : PoisDim.W K) : μ (c K) (φ K) mul x y = x * y := by
  rw [φ, μ_model, val_c, val_c, symm_refl, symm_swap]
  simp only [mb, LinearMap.add_apply, LinearMap.mul_apply', bracketL, LinearMap.mk₂_apply,
    Pi.single_apply, reduceCtorEq, if_true, if_false]
  rw [bracket_antisymm wordBracket_antisymm y x, mul_comm y x]
  module

lemma μ_br (x y : PoisDim.W K) : μ (c K) (φ K) br x y = 𝔟 x y := by
  rw [φ, μ_model, val_c, val_c, symm_refl, symm_swap]
  simp only [mb, LinearMap.add_apply, LinearMap.mul_apply', bracketL, LinearMap.mk₂_apply,
    Pi.single_apply, reduceCtorEq, if_true, if_false]
  rw [bracket_antisymm wordBracket_antisymm y x, mul_comm y x]
  module

/-- **A binary tree evaluates to its value in the Poisson algebra.** -/
theorem lev_eq : ∀ t : LTree (PoisShGen 2),
    lev (μ (c K) (φ K)) (fun a => X [a]) t = PoisBin.ev K t
  | .leaf _ => rfl
  | .node .mul l r => by
    rw [lev, μ_mul, lev_eq l, lev_eq r]
    rfl
  | .node .br l r => by
    rw [lev, μ_br, lev_eq l, lev_eq r]
    rfl

omit [CharZero K] in
/-- A coordinate vector of one monomial picks its value. -/
lemma sum_vecOf {W : Type*} [AddCommGroup W] [Module K W] (F : LTree (PoisShGen 2) → W)
    {t : LTree (PoisShGen 2)} (ht : t ∈ LTree.monomials 3) :
    ∑ σ : LTree.Mono (PoisShGen 2) 3, LTree.vecOf K 3 t σ • F σ.1 = F t := by
  rw [Finset.sum_eq_single ⟨t, ht⟩ (fun σ _ hσ => ?_) (by simp)]
  · simp [LTree.vecOf]
  · rw [show LTree.vecOf K 3 t σ = 0 from if_neg fun h => hσ (Subtype.ext h), zero_smul]

omit [CharZero K] in
/-- **A combination of monomials** picks the combination of their values. -/
lemma sum_combo {W : Type*} [AddCommGroup W] [Module K W] (F : LTree (PoisShGen 2) → W) :
    ∀ l : List (ℤ × LTree (PoisShGen 2)), (∀ x ∈ l, x.2 ∈ LTree.monomials 3) →
      ∑ σ : LTree.Mono (PoisShGen 2) 3, PoisBin.combo K l σ • F σ.1
        = (l.map fun x => (x.1 : K) • F x.2).sum
  | [], _ => by simp [PoisBin.combo]
  | x :: l, h => by
    have hc : PoisBin.combo K (x :: l) = (x.1 : K) • LTree.vecOf K 3 x.2 + PoisBin.combo K l := by
      simp [PoisBin.combo]
    rw [hc, List.map_cons, List.sum_cons,
      ← sum_combo F l fun y hy => h y (List.mem_cons_of_mem _ hy),
      ← sum_vecOf (K := K) F (h x List.mem_cons_self), Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Pi.add_apply, Pi.smul_apply, add_smul, smul_eq_mul, mul_smul]

omit [CharZero K] in
lemma bracket_neg_right (f g : PoisDim.W K) : 𝔟 f (-g) = -𝔟 f g := by
  have h := bracket_sub_right (wordBracket K) f 0 g
  rwa [zero_sub, bracket_zero_right, zero_sub] at h

/-- **The relators of the rules vanish on every family of inputs**, by the identities of the
Poisson algebra of polynomials in words. -/
theorem relB_vanish (r : Rule) (v : ℕ → PoisDim.W K) :
    ∑ σ : LTree.Mono (PoisShGen 2) 3, PoisBin.relB K r σ • lev (μ (c K) (φ K)) v σ.1 = 0 := by
  have hmem : ∀ x ∈ PoisBin.relList r, x.2 ∈ LTree.monomials 3 := by
    cases r <;> simp [PoisBin.relList, PoisBin.bL_mem, PoisBin.bT_mem, PoisBin.bR_mem]
  rw [PoisBin.relB, sum_combo _ _ hmem]
  have hJ := jacobi wordBracket_antisymm wordBracket_jac (v 0) (v 1) (v 2)
  rw [jac] at hJ
  cases r <;>
    simp only [PoisBin.relList, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      PoisBin.bL, PoisBin.bT, PoisBin.bR, lev, μ_mul, μ_br, Int.cast_one, Int.cast_neg, one_smul,
      neg_one_smul, add_zero]
  · have h1 := bracket_antisymm wordBracket_antisymm (𝔟 (v 0) (v 1)) (v 2)
    have h2 := bracket_antisymm wordBracket_antisymm (𝔟 (v 0) (v 2)) (v 1)
    have h3 : 𝔟 (v 1) (𝔟 (v 0) (v 2)) = -𝔟 (v 1) (𝔟 (v 2) (v 0)) := by
      rw [bracket_antisymm wordBracket_antisymm (v 0) (v 2), bracket_neg_right]
    linear_combination h1 - h2 + h3 - hJ
  · linear_combination bracket_mul_right (wordBracket K) (v 0) (v 1) (v 2)
  · linear_combination bracket_mul_left (wordBracket K) (v 0) (v 2) (v 1)
      + v 0 * bracket_antisymm wordBracket_antisymm (v 2) (v 1)
  · linear_combination bracket_mul_left (wordBracket K) (v 0) (v 1) (v 2)
  · ring
  · ring

variable (K) in
/-- **The shuffle relators of the symmetric presentation are the relators of `Pois`.** -/
theorem Rsh_eq : ShuffleBarSym.Rsh (c K) (hc K) (rel K) = PoisBin.rel K := by
  ext v
  rw [rel, mem_Rsh_kerRel, PoisBin.rel, LinearMap.mem_ker, PoisBin.evL_apply]
  constructor
  · intro h
    rw [← h fun j => X [j.1]]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← lev_eq]
    congr 1
    refine lev_congr _ σ.1 fun a ha => ?_
    have ha3 : a < 3 := by
      have hl := ((LTree.mem_monomials 3 σ.1).1 σ.2).2
      exact List.mem_range.1 (hl.subset ha)
    simp [ext3, ha3]
  · intro h w
    have hv : v ∈ PoisBin.rel K := LinearMap.mem_ker.2 ((PoisBin.evL_apply v).trans h)
    rw [PoisBin.rel_eq_span_relB] at hv
    clear h
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, rfl⟩ := hx
      exact relB_vanish r _
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, hx, hy, add_zero]
    | smul a x _ hx =>
      simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, hx, smul_zero]

/-- **The symmetric operad `Pois`, presented by a commutative product and a Lie bracket in arity
two and the Poisson relations, is Koszul**, over a field of characteristic zero. -/
theorem isKoszul : Koszul.IsKoszul K (E K) (rel K) :=
  (isKoszul_kerRel_iff (c K) (hc K) (φ K)).2 (by
    rw [← rel, Rsh_eq]
    exact PoisBin.isKoszul K)

end SymPresPois

end Operad
