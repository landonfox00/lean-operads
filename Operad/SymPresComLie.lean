/-
# `Com` and `Lie` are Koszul as symmetric graded operads

Step 3 of the bridge between symmetric and shuffle operads (Dotsenko–Khoroshkin) for `Com` and
`Lie`, over a field `K` of characteristic zero, through `ShuffleBarSym.isKoszul_orbitRel_iff`
(`Operad.SymPresBin`). Both are presented by a one-dimensional representation of `𝔖₂` in arity
two, in even degree, with generators indexed by `ComGen 2`, so that the shuffle coordinates live
on the monomials `LTree.Mono (ComGen 2) 3` of `Operad.ShuffleBinCom`.

* **`Com`**: generators `SymPresComLie.ECom K`, the trivial representation `BinSp K K id`, with
  basis `SymPresComLie.cCom K`; relators `SymPresComLie.rCom K`, the `𝔖₃`-orbit of the associator
  `μ(μ(0, 1), 2) - μ(0, μ(1, 2))` (`SymPresComLie.assoc`), with `SymPresComLie.rCom_hr3` and
  `SymPresComLie.rCom_hrS`. The permutations permute the basis vectors of arity three without
  sign, so the sum of the coordinates is invariant (`SymPresComLie.aug_coord3L_map`) and the
  shuffle relators are those of the commutative operad, `Rsh = ComBin.rel K`
  (`SymPresComLie.rsh_com`). Hence **`Koszul.IsKoszul K (ECom K) (rCom K)`**
  (`SymPresComLie.isKoszul_com`), from `ComBin.isKoszul`.
* **`Lie`**: generators `SymPresComLie.ELie K`, the sign representation `BinSp K K (-id)`, with
  basis `SymPresComLie.cLie K`; relators `SymPresComLie.rLie K`, the `𝔖₃`-orbit of the Jacobiator
  `[[0, 1], 2] - [[0, 2], 1] - [0, [1, 2]]` (`SymPresComLie.jacobi`), with
  `SymPresComLie.rLie_hr3` and `SymPresComLie.rLie_hrS`. Both adjacent transpositions send the
  Jacobiator to its negative (`SymPresComLie.map_swap01_jacobi`,
  `SymPresComLie.map_swap12_jacobi`, the sorted trees and signs computed by `decide`), so its
  orbit spans a line (`SymPresComLie.map_mem_span_jacobi`) and `Rsh = K ∙ ComBin.jac K`
  (`SymPresComLie.rsh_lie`), the Koszul dual relators of `Com`
  (`SymPresComLie.rsh_lie_eq_dualRel`). Hence **`Koszul.IsKoszul K (ELie K) (rLie K)`**
  (`SymPresComLie.isKoszul_lie`), from `ComBin.isKoszul_dualRel`.

The presented operads are not compared here with a symmetric `Com` or `Lie` defined elsewhere in
the library.
-/
import Operad.SymPresBin
import Operad.ShuffleKoszulDuals

universe u

namespace Operad

namespace SymPresComLie

open LTree ShuffleBarSym ComBin

variable (K : Type u) [Field K]

/-- **The trivial representation of `𝔖₂`** in arity two. -/
abbrev ECom : (A : Type) → [Fintype A] → [DecidableEq A] → Type u :=
  BinSp K K (LinearMap.id : K →ₗ[K] K)

/-- **The sign representation of `𝔖₂`** in arity two, in even degree. -/
abbrev ELie : (A : Type) → [Fintype A] → [DecidableEq A] → Type u :=
  BinSp K K (-LinearMap.id : K →ₗ[K] K)

/-- The basis of `ECom`: the binary product `μ`. -/
noncomputable def cCom : ∀ k, Module.Basis (BinGen (ComGen 2) k) K (ECom K (Fin k)) :=
  BinSp.basis _ (fun _ => rfl) (Module.Basis.singleton (ComGen 2) K)

/-- The basis of `ELie`: the bracket. -/
noncomputable def cLie : ∀ k, Module.Basis (BinGen (ComGen 2) k) K (ELie K (Fin k)) :=
  BinSp.basis _ (fun _ => by simp) (Module.Basis.singleton (ComGen 2) K)

lemma hcCom : ∀ k (β : BinGen (ComGen 2) k),
    GrSpecies.par (R := K) false (cCom K k β) = cCom K k β :=
  fun k β => BinSp.par_basis _ _ k β

lemma hcLie : ∀ k (β : BinGen (ComGen 2) k),
    GrSpecies.par (R := K) false (cLie K k β) = cLie K k β :=
  fun k β => BinSp.par_basis _ _ k β

lemma swCom (g : ComGen 2) : SymSpecies.map (R := K) (Equiv.swap (0 : Fin 2) 1) (cCom K 2 (.op g))
    = (fun _ => (1 : K)) g • cCom K 2 (.op (id g)) :=
  BinSp.map_swap_basis_of _ _ id (fun _ => (1 : K)) (fun _ => by simp) g

lemma swLie (g : ComGen 2) : SymSpecies.map (R := K) (Equiv.swap (0 : Fin 2) 1) (cLie K 2 (.op g))
    = (fun _ => (-1 : K)) g • cLie K 2 (.op (id g)) :=
  BinSp.map_swap_basis_of _ _ id (fun _ => (-1 : K)) (fun _ => by simp) g

/-! ## Basis vectors of arity three -/

section Gen

variable {K} {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  (c : ∀ k, Module.Basis (BinGen (ComGen 2) k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen (ComGen 2) k), GrSpecies.par (R := K) false (c k β) = c k β)

/-- **The basis vector of a monomial of arity three.** -/
noncomputable def tb (t : LTree (ComGen 2)) (ht : t ∈ monomials 3) : FreeGrL K E (Fin 3) :=
  tBasis c hc (Fin 3) ⟨t, by rw [Fintype.card_fin]; exact ht⟩

lemma coord3L_tb (t : LTree (ComGen 2)) (ht : t ∈ monomials 3) :
    coord3L c hc (tb c hc t ht) = vecOf K 3 t :=
  coord3L_tBasis c hc _

/-- **Relabelling a basis vector of arity three along a permutation**, the sorted tree computed. -/
lemma map_tb (ε : ComGen 2 → K)
    (hsw : ∀ g, SymSpecies.map (R := K) (Equiv.swap (0 : Fin 2) 1) (c 2 (.op g))
      = ε g • c 2 (.op (id g)))
    (σ : Equiv.Perm (Fin 3)) {t t' : LTree (ComGen 2)} (ht : t ∈ monomials 3)
    (ht' : t' ∈ monomials 3) (h : sortL id (t.relabel (permFun σ)) = t') :
    GrOperad.map (R := K) σ (tb c hc t ht) = sgnL ε (t.relabel (permFun σ)) • tb c hc t' ht' := by
  rw [tb, map_tBasis_perm c hc id ε hsw]
  exact congrArg _ (congrArg _ (Subtype.ext h))

end Gen

/-! ## `Com` -/

/-- **The associator** `μ(μ(0, 1), 2) - μ(0, μ(1, 2))` of a commutative product. -/
noncomputable def assoc : FreeGrL K (ECom K) (Fin 3) :=
  tb (cCom K) (hcCom K) lcomb lcomb_mem - tb (cCom K) (hcCom K) rcomb rcomb_mem

/-- **The relators of `Com`**: the `𝔖₃`-orbit of the associator, in arity three. -/
def rCom : ∀ n : ℕ, Set (FreeGrL K (ECom K) (Fin n)) := orbitRel {assoc K}

lemma rCom_hr3 : ∀ n ≠ 3, rCom K n = ∅ := orbitRel_hr3 _

lemma rCom_hrS : ∀ σ : Equiv.Perm (Fin 3), ∀ x ∈ rCom K 3,
    GrOperad.map (R := K) σ x ∈ Submodule.span K (rCom K 3) := orbitRel_hrS _

/-- **The augmentation of the coordinates is invariant** under the permutations: they permute the
basis vectors without sign. -/
lemma aug_coord3L_map (σ : Equiv.Perm (Fin 3)) (x : FreeGrL K (ECom K) (Fin 3)) :
    aug K 3 (coord3L (cCom K) (hcCom K) (GrOperad.map (R := K) σ x))
      = aug K 3 (coord3L (cCom K) (hcCom K) x) := by
  refine LinearMap.congr_fun ((tBasis (cCom K) (hcCom K) (Fin 3)).ext
    (f₁ := aug K 3 ∘ₗ coord3L (cCom K) (hcCom K) ∘ₗ GrOperad.map (R := K) σ)
    (f₂ := aug K 3 ∘ₗ coord3L (cCom K) (hcCom K)) fun t => ?_) x
  simp only [LinearMap.comp_apply]
  rw [map_tBasis_perm (cCom K) (hcCom K) id _ (swCom K), sgnL_one, one_smul, coord3L_tBasis,
    coord3L_tBasis, aug_vecOf (by simp), aug_vecOf (by simp)]

/-- **The shuffle relators of `Com`** are the relators `ComBin.rel` of the commutative operad. -/
theorem rsh_com : Rsh (cCom K) (hcCom K) (rCom K) = ComBin.rel K := by
  rw [rCom, rsh_orbitRel]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro v ⟨σ, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    show _ ∈ LinearMap.ker (aug K 3)
    rw [LinearMap.mem_ker, aug_coord3L_map, assoc, map_sub, coord3L_tb, coord3L_tb,
      map_sub, aug_vecOf lcomb_mem, aug_vecOf rcomb_mem, sub_self]
  · rw [rel_eq_span, Submodule.span_le]
    intro v hv
    rcases hv with rfl | hv
    · refine Submodule.subset_span ⟨Equiv.refl _, assoc K, rfl, ?_⟩
      rw [GrOperad.map_refl, assoc, map_sub, coord3L_tb, coord3L_tb]
    · rw [Set.mem_singleton_iff] at hv
      subst hv
      refine Submodule.subset_span ⟨Equiv.swap 1 2, assoc K, rfl, ?_⟩
      rw [assoc, map_sub, map_tb _ _ _ (swCom K) _ _ tcomb_mem (by decide),
        map_tb _ _ _ (swCom K) _ _ rcomb_mem (by decide), sgnL_one, sgnL_one, one_smul,
        one_smul, map_sub, coord3L_tb, coord3L_tb]

/-- **`Com` is Koszul**, as the graded operad presented by the trivial representation of `𝔖₂`
in arity two and the orbit of the associator, over a field of characteristic zero. -/
theorem isKoszul_com [CharZero K] : Koszul.IsKoszul K (ECom K) (rCom K) := by
  rw [rCom, isKoszul_orbitRel_iff (cCom K) (hcCom K), ← rCom, rsh_com]
  exact ComBin.isKoszul K

/-! ## `Lie` -/

/-- **The Jacobiator** `[[0, 1], 2] - [[0, 2], 1] - [0, [1, 2]]`. -/
noncomputable def jacobi : FreeGrL K (ELie K) (Fin 3) :=
  tb (cLie K) (hcLie K) lcomb lcomb_mem - tb (cLie K) (hcLie K) tcomb tcomb_mem
    - tb (cLie K) (hcLie K) rcomb rcomb_mem

/-- **The relators of `Lie`**: the `𝔖₃`-orbit of the Jacobiator, in arity three. -/
def rLie : ∀ n : ℕ, Set (FreeGrL K (ELie K) (Fin n)) := orbitRel {jacobi K}

lemma rLie_hr3 : ∀ n ≠ 3, rLie K n = ∅ := orbitRel_hr3 _

lemma rLie_hrS : ∀ σ : Equiv.Perm (Fin 3), ∀ x ∈ rLie K 3,
    GrOperad.map (R := K) σ x ∈ Submodule.span K (rLie K 3) := orbitRel_hrS _

lemma coord3L_jacobi : coord3L (cLie K) (hcLie K) (jacobi K) = jac K := by
  rw [jacobi, map_sub, map_sub, coord3L_tb, coord3L_tb, coord3L_tb, jac_eq]

lemma map_swap01_jacobi :
    GrOperad.map (R := K) (Equiv.swap (0 : Fin 3) 1) (jacobi K) = -jacobi K := by
  rw [jacobi, map_sub, map_sub, map_tb _ _ _ (swLie K) _ _ lcomb_mem (by decide),
    map_tb _ _ _ (swLie K) _ _ rcomb_mem (by decide),
    map_tb _ _ _ (swLie K) _ _ tcomb_mem (by decide), sgnL_const, sgnL_const, sgnL_const,
    show nSwap (lcomb.relabel (permFun (Equiv.swap (0 : Fin 3) 1))) = 1 by decide,
    show nSwap (tcomb.relabel (permFun (Equiv.swap (0 : Fin 3) 1))) = 1 by decide,
    show nSwap (rcomb.relabel (permFun (Equiv.swap (0 : Fin 3) 1))) = 1 by decide]
  module

lemma map_swap12_jacobi :
    GrOperad.map (R := K) (Equiv.swap (1 : Fin 3) 2) (jacobi K) = -jacobi K := by
  rw [jacobi, map_sub, map_sub, map_tb _ _ _ (swLie K) _ _ tcomb_mem (by decide),
    map_tb _ _ _ (swLie K) _ _ lcomb_mem (by decide),
    map_tb _ _ _ (swLie K) _ _ rcomb_mem (by decide), sgnL_const, sgnL_const, sgnL_const,
    show nSwap (lcomb.relabel (permFun (Equiv.swap (1 : Fin 3) 2))) = 0 by decide,
    show nSwap (tcomb.relabel (permFun (Equiv.swap (1 : Fin 3) 2))) = 0 by decide,
    show nSwap (rcomb.relabel (permFun (Equiv.swap (1 : Fin 3) 2))) = 1 by decide]
  module

/-- **The Jacobiator spans a line stable under the permutations.** -/
lemma map_mem_span_jacobi (σ : Equiv.Perm (Fin 3)) :
    GrOperad.map (R := K) σ (jacobi K) ∈ K ∙ jacobi K := by
  have key : ∀ (s : Equiv.Perm (Fin 3)),
      GrOperad.map (R := K) s (jacobi K) = -jacobi K →
      ∀ x ∈ K ∙ jacobi K, GrOperad.map (R := K) s x ∈ K ∙ jacobi K := fun s hs x hx => by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [map_smul, hs]
    exact Submodule.smul_mem _ _ (neg_mem (Submodule.mem_span_singleton_self _))
  exact map_mem_of_swaps _ (key _ (map_swap01_jacobi K)) (key _ (map_swap12_jacobi K)) σ _
    (Submodule.mem_span_singleton_self _)

/-- **The shuffle relators of `Lie`** are the multiples of the Jacobi relator `ComBin.jac`. -/
theorem rsh_lie : Rsh (cLie K) (hcLie K) (rLie K) = K ∙ jac K := by
  rw [rLie, rsh_orbitRel]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro v ⟨σ, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (map_mem_span_jacobi K σ)
    rw [← ha, map_smul, coord3L_jacobi]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_singleton_le_iff_mem]
    refine Submodule.subset_span ⟨Equiv.refl _, jacobi K, rfl, ?_⟩
    rw [GrOperad.map_refl, coord3L_jacobi]

/-- **The shuffle relators of `Lie` are the Koszul dual relators of `Com`.** -/
theorem rsh_lie_eq_dualRel :
    Rsh (cLie K) (hcLie K) (rLie K) = ShuffleBar.dualRel K (ComBin.rel K) := by
  rw [rsh_lie, dualRel_rel]

/-- **`Lie` is Koszul**, as the graded operad presented by the sign representation of `𝔖₂` in
arity two (in even degree) and the orbit of the Jacobiator, over a field of characteristic zero.
-/
theorem isKoszul_lie [CharZero K] : Koszul.IsKoszul K (ELie K) (rLie K) := by
  rw [rLie, isKoszul_orbitRel_iff (cLie K) (hcLie K), ← rLie, rsh_lie_eq_dualRel]
  exact ComBin.isKoszul_dualRel K

end SymPresComLie

end Operad
