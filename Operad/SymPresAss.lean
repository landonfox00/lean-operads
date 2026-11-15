/-
# The symmetric presentation of `Ass` is Koszul

Step 3 of the bridge between symmetric and shuffle operads (Dotsenko–Khoroshkin), for the
associative operad. Over a field `K`:

* **The generators** (`SymPresAss.E`): the regular representation `Reg2 K` of `𝔖₂` in arity two,
  two-dimensional and even, with the basis `SymPresAss.c` of the product `x₁x₂` (the identity
  numbering, `AssShGen.mu`) and the opposite product `x₂x₁` (the transposition, `AssShGen.op`).
* **The relators** (`SymPresAss.rel`): the operations of arity three which vanish in the free
  associative algebra `K⟨ℕ⟩ = MonoidAlgebra K (FreeMonoid ℕ)` (`SymPresAss.φ`, through
  `SymPresB.model` of the product), that is, all the associativity relations of arity three.
  They are concentrated in arity three and stable under `𝔖₃`.
* **Their shuffle relators are those of `Ass`** (`SymPresAss.Rsh_eq`):
  `ShuffleBarSym.Rsh = AssBin.rel K`. A monomial evaluates in `K⟨ℕ⟩` to the product of its word
  (`SymPresAss.lev_eq`), and a combination of words vanishes on every family of inputs iff it
  vanishes on the letters.
* Hence, over a field of characteristic zero, **the symmetric operad `T(E)/(rel)` is Koszul**
  (`SymPresAss.isKoszul`), by the bridge `ShuffleBarSym.isKoszul_iff_shuffle` and the Gröbner
  basis of `AssBin.isKoszul`.

The comparison of `T(E)/(rel)` with the library's set-theoretic presentations of `Ass` is not
made here.
-/
import Operad.SymPresBinB
import Operad.ShuffleBinAss

universe u

namespace Operad

namespace SymPresAss

open Sym SymPresB AssShGen

variable (K : Type u) [Field K]

/-- **The numberings of `Fin 2` are the two products**: the identity is `x₁x₂`, the
transposition `x₂x₁`. -/
def genEquiv : (Fin 2 ≃ Fin 2) ≃ AssShGen 2 where
  toFun τ := if τ = Equiv.refl _ then .mu else .op
  invFun g := match g with
    | .mu => Equiv.refl _
    | .op => Equiv.swap 0 1
  left_inv τ := by
    revert τ
    decide
  right_inv g := by
    cases g <;> decide

/-- **The generators of `Ass`**: the regular representation of `𝔖₂` in arity two. -/
abbrev E := Reg2 K

/-- The basis of `E (Fin 2)`: the indicator functions of the two numberings. -/
noncomputable def basis2 : Module.Basis (AssShGen 2) K (Reg2 K (Fin 2)) :=
  (Pi.basisFun K (Fin 2 ≃ Fin 2)).reindex genEquiv

/-- **The basis of the generators**, indexed by `BinGen (AssShGen 2)`. -/
noncomputable def c : ∀ k, Module.Basis (BinGen (AssShGen 2) k) K (Reg2 K (Fin k)) :=
  FreeL.binBasisOf (basis2 K) fun _ hk => Reg2.subsingleton hk

/-- The basis vectors are even. -/
lemma hc : ∀ k (β : BinGen (AssShGen 2) k), GrSpecies.par (R := K) false (c K k β) = c K k β :=
  fun _ _ => Reg2.par_false _

/-- **The free associative algebra** on the letters `ℕ`. -/
abbrev V := MonoidAlgebra K (FreeMonoid ℕ)

/-- **The evaluation in the free associative algebra**: the product to the product. -/
noncomputable def φ : GrOperadHom K (FreeGrL K (Reg2 K)) (SymGr (EndOp K (V K))) :=
  model (LinearMap.mul K (V K))

/-- **The relators of `Ass`**: the operations of arity three vanishing in the free associative
algebra, and none in the other arities. -/
def rel : ∀ n : ℕ, Set (FreeGrL K (Reg2 K) (Fin n)) := kerRel (φ K)

variable {K}

lemma val_c (g : AssShGen 2) (τ : Fin 2 ≃ Fin 2) :
    (c K 2 (BinGen.op g)).val τ = if τ = genEquiv.symm g then 1 else 0 := by
  rw [c, FreeL.binBasisOf_op, basis2]
  show ((Pi.basisFun K (Fin 2 ≃ Fin 2)).reindex genEquiv g : (Fin 2 ≃ Fin 2) → K) τ = _
  rw [Module.Basis.reindex_apply, Pi.basisFun_apply, Pi.single_apply]

lemma μ_mu (x y : V K) : μ (c K) (φ K) mu x y = x * y := by
  rw [φ, μ_model, val_c, val_c]
  simp [genEquiv]

lemma μ_op (x y : V K) : μ (c K) (φ K) op x y = y * x := by
  have hne : Equiv.refl (Fin 2) ≠ Equiv.swap 0 1 := by decide
  rw [φ, μ_model, val_c, val_c]
  simp [genEquiv, hne]

/-- **A binary tree evaluates to the product of its word.** -/
theorem lev_eq (v : ℕ → V K) :
    ∀ t : LTree (AssShGen 2), lev (μ (c K) (φ K)) v t = ((AssBin.ev t).map v).prod
  | .leaf a => by simp [lev, AssBin.ev]
  | .node .mu l r => by
    rw [lev, μ_mu, lev_eq v l, lev_eq v r]
    simp [AssBin.ev, ap]
  | .node .op l r => by
    rw [lev, μ_op, lev_eq v l, lev_eq v r]
    simp [AssBin.ev, ap]

/-- The letter `a` of the free associative algebra. -/
noncomputable def X (a : ℕ) : V K := MonoidAlgebra.single (FreeMonoid.of a) 1

lemma prod_X : ∀ l : List ℕ,
    (l.map (X (K := K))).prod = MonoidAlgebra.single (FreeMonoid.ofList l) 1
  | [] => by simp [MonoidAlgebra.one_def]
  | a :: l => by
    rw [List.map_cons, List.prod_cons, prod_X l, X, MonoidAlgebra.single_mul_single, mul_one,
      FreeMonoid.ofList_cons]

variable (K) in
/-- **The shuffle relators of the symmetric presentation are the relators of `Ass`.** -/
theorem Rsh_eq : ShuffleBarSym.Rsh (c K) (hc K) (rel K) = AssBin.rel K := by
  ext v
  rw [rel, mem_Rsh_kerRel, AssBin.rel, LinearMap.mem_ker, AssBin.evL_apply]
  constructor
  · intro h
    have h0 := h fun j => X j
    have hX : ∀ σ : LTree.Mono (AssShGen 2) 3,
        ((AssBin.ev σ.1).map (ext3 fun j => X (K := K) j)).prod
          = MonoidAlgebra.single (FreeMonoid.ofList (AssBin.ev σ.1)) 1 := fun σ => by
      rw [← prod_X]
      congr 1
      refine List.map_congr_left fun a ha => ?_
      have ha3 : a < 3 := by
        have hl := ((LTree.mem_monomials 3 σ.1).1 σ.2).2
        exact List.mem_range.1 (hl.subset ((AssBin.perm_ev σ.1).subset ha))
      simp [ext3, ha3]
    simp only [lev_eq, hX] at h0
    have h0' : (∑ σ : LTree.Mono (AssShGen 2) 3, v σ • Finsupp.single
        (FreeMonoid.ofList (AssBin.ev σ.1)) (1 : K) : FreeMonoid ℕ →₀ K) = 0 := h0
    have h1 := congrArg (Finsupp.lmapDomain K K FreeMonoid.toList) h0'
    rw [map_zero, map_sum] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [map_smul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, FreeMonoid.toList_ofList]
  · intro h w
    have h1 := congrArg (Finsupp.linearCombination K
      fun l : List ℕ => (l.map (ext3 w)).prod) h
    rw [map_zero, map_sum] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [lev_eq, map_smul, Finsupp.linearCombination_single, one_smul]

/-- **The symmetric operad `Ass`, presented by the regular representation of `𝔖₂` in arity two
and its associativity relations, is Koszul**, over a field of characteristic zero. -/
theorem isKoszul [CharZero K] : Koszul.IsKoszul K (E K) (rel K) :=
  (isKoszul_kerRel_iff (c K) (hc K) (φ K)).2 (by
    rw [← rel, Rsh_eq]
    exact AssBin.isKoszul K)

end SymPresAss

end Operad
