/-
# Weights on the cobar construction of the Koszul dual dg cooperad

For quadratic-linear data (`Koszul.IsQL`, `Operad.KoszulInhom`), the cobar construction
`Ω(qP^¡, d_φ)` is graded by a weight, and its differential is a part preserving the weights minus
a part lowering them by one. This file has the weights and an exactness criterion by weights;
the resolution theorem is in `Operad.KoszulInhomQIso`.

* **Components.** A submodule stable under an endomorphism contains the eigencomponents, for
  distinct natural numbers, of its elements (`Submodule.mem_of_sum_eigen`,
  `Submodule.mem_iSup_inf_eigenspace`), over a `ℚ`-algebra.
* **An exactness criterion by weights** (`exists_eq_D_of_graded`). Let `M` be spanned by the
  eigenspaces `M_n` of `W`, and `D = d - δ` a differential, `d` preserving the weights and `δ`
  lowering them by one. Let `γ` be a map with `γ ∘ D = 0` and `σ` a map such that an element of
  top weight `n` killed by `γ` has its component of weight `n` killed by `σ`, and a `d`-cycle of
  weight `n` killed by `σ` is the `d`-boundary of an element of weight `n`. Then a `D`-cycle
  killed by `γ` is a `D`-boundary, by induction on the top weight.
* **The vertex count** (`FreeGrL.vcount`) is a coderivation of the cut cooperad
  (`FreeGrL.decomp_vcount`), and the Koszul dual cooperad is stable under it
  (`Koszul.vcount_mem_dual`): `κ_T ⋆ κ_T` only sees the trees with two vertices
  (`Koszul.star_vcount`), and `K + N K` is a subcooperad (`GrSubCooperad.addCoder`). So `qP^¡` is
  spanned by its elements with a number of vertices (`Koszul.mem_iSup_dual_inf_vx`).
* **The weights of `Ω(qP^¡, d_φ)`.** The vertex count of the generators (`Koszul.vcountRed`)
  extends to the weight derivation (`Koszul.wtQL`), whose eigenspaces span
  (`Koszul.iSup_wtQL`). The cobar differential commutes with it (`Koszul.d_wtQL`), through the
  injection `Ω(qP^¡) → Ω(T^c(sE))` (`Koszul.cobarIncl_injective`) and the case of a cut cooperad
  (`Cobar.d_wtΩ`). `d_φ` lowers the number of vertices by one, as the bar differential does
  (`Koszul.vcountL_dQL`, `Bar.wtD_d`), so the part `δ` of the differential coming from `d_φ`
  lowers the weight by one (`Koszul.deltaQL`, `Koszul.wtQL_deltaQL`); the differential is
  `d_Ω - δ` (`Koszul.cobarDG_d_app`).
* **The morphisms.** `Ω(qP^¡, d_φ) → P` and `Ω(qP^¡) → qP` are the projections after one
  morphism of graded operads `Ω(qP^¡) → T(E)` (`Koszul.cobarToFree`, `Koszul.cobarMorQL_eq`,
  `Koszul.cobarMorQ_eq`), which takes the weight `n` to the trees with `n` vertices
  (`Koszul.cobarToFree_mem_vx`).
* **The two inputs.** With **the Poincaré–Birkhoff–Witt property** (`Koszul.IsPBW`), an element
  of top weight `n` killed by `Ω(qP^¡, d_φ) → P` has its component of weight `n` killed by
  `Ω(qP^¡) → qP` (`Koszul.cobarMorQ_eq_zero_of_pbw`). When `qP` is Koszul, a cycle of weight `n`
  of the cobar differential killed by `Ω(qP^¡) → qP` is the boundary of an element of weight `n`
  (`Koszul.exists_d_eq_of_isKoszul`).
-/
import Operad.KoszulInhom
import Operad.CobarWeight
import Operad.BarCobarQIso

universe u v w

namespace Operad

open Sym GerBV TreeOfArity FreeGr
open scoped TensorProduct

/-! ## Components of an element of a stable submodule -/

section Components

variable {R : Type u} [CommRing R] [Algebra ℚ R] {M : Type*} [AddCommGroup M] [Module R M]

/-- **The eigencomponents of an element of a stable submodule lie in it**: if a sum of
eigenvectors of `E` for distinct natural numbers lies in a submodule stable under `E`, so does
each of them, over a `ℚ`-algebra. -/
theorem Submodule.mem_of_sum_eigen (E : M →ₗ[R] M) (p : Submodule R M)
    (hp : ∀ x ∈ p, E x ∈ p) (s : Finset ℕ) :
    ∀ x : ℕ → M, (∀ j ∈ s, x j ∈ Module.End.eigenspace E (j : R)) → ∑ j ∈ s, x j ∈ p →
      ∀ j ∈ s, x j ∈ p := by
  classical
  induction s using Finset.induction_on with
  | empty => exact fun _ _ _ j hj => absurd hj (Finset.notMem_empty j)
  | insert a s ha ih =>
    intro x hx hsum
    have hE : ∑ j ∈ s, ((j : R) - a) • x j ∈ p := by
      have h1 := p.sub_mem (hp _ hsum) (p.smul_mem (a : R) hsum)
      have h2 : E (∑ j ∈ insert a s, x j) - (a : R) • ∑ j ∈ insert a s, x j
          = ∑ j ∈ s, ((j : R) - a) • x j := by
        rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.sum_insert ha,
          Module.End.mem_eigenspace_iff.1 (hx a (Finset.mem_insert_self a s)), sub_self,
          zero_add]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Module.End.mem_eigenspace_iff.1 (hx j (Finset.mem_insert_of_mem hj)), sub_smul]
      rwa [h2] at h1
    have hs : ∀ j ∈ s, x j ∈ p := fun j hj => by
      have h3 : ((j : R) - a) • x j ∈ p := ih (fun j => ((j : R) - a) • x j)
        (fun j hj => Submodule.smul_mem _ _ (hx j (Finset.mem_insert_of_mem hj))) hE j hj
      have hu : IsUnit ((j : R) - a) := isUnit_natCast_sub fun h => ha (h ▸ hj)
      obtain ⟨u, hu'⟩ := hu
      have h4 := p.smul_mem (↑u⁻¹ : R) h3
      rwa [← hu', smul_smul, Units.inv_mul, one_smul] at h4
    intro j hj
    rcases Finset.mem_insert.1 hj with rfl | hj'
    · have h5 : x j = ∑ k ∈ insert j s, x k - ∑ k ∈ s, x k := by
        rw [Finset.sum_insert ha, add_sub_cancel_right]
      rw [h5]
      exact p.sub_mem hsum (p.sum_mem hs)
    · exact hs j hj'

/-- **A stable submodule is spanned by its eigenvectors**, as far as it lies in the span of the
eigenspaces for the natural numbers, over a `ℚ`-algebra. -/
theorem Submodule.mem_iSup_inf_eigenspace (E : M →ₗ[R] M) (p : Submodule R M)
    (hp : ∀ x ∈ p, E x ∈ p) {x : M} (hx : x ∈ p)
    (hx' : x ∈ ⨆ j : ℕ, Module.End.eigenspace E (j : R)) :
    x ∈ ⨆ j : ℕ, p ⊓ Module.End.eigenspace E (j : R) := by
  classical
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx'
  have hmem := Submodule.mem_of_sum_eigen E p hp f.support (fun j => f j) (fun j _ => hf j) hx
  refine Submodule.sum_mem _ fun j hj => ?_
  exact Submodule.mem_iSup_of_mem j ⟨hmem j hj, hf j⟩

end Components

/-! ## Cycles killed by a map injective on homology -/

/-- **A cycle killed by a chain map injective on homology is a boundary.** -/
lemma Homology.exists_eq_of_map_injective {R : Type*} [CommRing R] {V W : Type*}
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] {dV : V →ₗ[R] V}
    {dW : W →ₗ[R] W} (f : V →ₗ[R] W) (hf : ∀ v, f (dV v) = dW (f v))
    (hinj : Function.Injective (Homology.map f hf)) {x : V} (hdx : dV x = 0) (hfx : f x = 0) :
    ∃ v, dV v = x := by
  have hx' : x ∈ LinearMap.ker dV := hdx
  have hc : Homology.cycleMap f hf ⟨x, hx'⟩ = 0 := Subtype.ext hfx
  have h0 : Homology.mk dV ⟨x, hx'⟩ = Homology.mk dV 0 :=
    hinj ((Homology.map_mk f hf _).trans ((congrArg (Homology.mk dW) hc).trans
      ((map_zero (Homology.mk dW)).trans
        ((map_zero (Homology.map f hf)).symm.trans
          (congrArg (Homology.map f hf) (map_zero (Homology.mk dV)).symm)))))
  obtain ⟨v, hv⟩ := (Homology.mk_eq_mk_iff (⟨x, hx'⟩ : LinearMap.ker dV) 0).1 h0
  exact ⟨v, hv.trans (sub_zero x)⟩

/-! ## An exactness criterion by weights -/

section WeightInduction

variable {R : Type u} [CommRing R] [Algebra ℚ R] {M P' Q' : Type*} [AddCommGroup M]
  [Module R M] [AddCommGroup P'] [Module R P'] [AddCommGroup Q'] [Module R Q']

/-- An eigenvector for `-1` of an endomorphism whose eigenspaces for the natural numbers span
vanishes, over a `ℚ`-algebra. -/
lemma eq_zero_of_eigen_neg_one (W : M →ₗ[R] M)
    (htop : ⨆ j : ℕ, Module.End.eigenspace W (j : R) = ⊤) {x : M} (hx : W x = -x) : x = 0 := by
  have hp : ∀ y ∈ Submodule.span R {x}, W y ∈ Submodule.span R {x} := by
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [map_smul, hx, smul_neg, ← neg_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
  have h1 := Submodule.mem_iSup_inf_eigenspace W (Submodule.span R {x}) hp
    (Submodule.mem_span_singleton_self x) (htop ▸ Submodule.mem_top)
  have hle : (⨆ j : ℕ, Submodule.span R {x} ⊓ Module.End.eigenspace W (j : R)) ≤ ⊥ := by
    refine iSup_le fun j y hy => ?_
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy.1
    have h2 := Module.End.mem_eigenspace_iff.1 hy.2
    rw [map_smul, hx, smul_neg] at h2
    have h3 : ((j : R) + 1) • (a • x) = 0 := by
      rw [add_smul, one_smul, ← h2, neg_add_cancel]
    have hu : IsUnit ((j : R) + 1) := by
      have := isUnit_natCast_of_ne_zero (R := R) (Nat.succ_ne_zero j)
      rwa [Nat.cast_succ] at this
    exact (Submodule.mem_bot R).2 (hu.smul_left_cancel.1 (h3.trans (smul_zero _).symm))
  exact (Submodule.mem_bot R).1 (hle h1)

/-- **An exactness criterion by weights.** Let `M` be spanned by the eigenspaces `M_n` of `W` for
the natural numbers, over a `ℚ`-algebra, and `D = d - δ` a differential, `d` preserving the
weights and `δ` lowering them by one. Let `γ` be a map with `γ ∘ D = 0` and `σ` a map such that

* an element of top weight `n` killed by `γ` has its component of weight `n` killed by `σ`;
* a `d`-cycle of weight `n` killed by `σ` is the `d`-boundary of an element of weight `n`.

Then a `D`-cycle killed by `γ` is a `D`-boundary. -/
theorem exists_eq_D_of_graded (W d δ : M →ₗ[R] M) (γ : M →ₗ[R] P') (σ : M →ₗ[R] Q')
    (htop : ⨆ j : ℕ, Module.End.eigenspace W (j : R) = ⊤)
    (hdW : ∀ z, d (W z) = W (d z)) (hWδ : ∀ z, W (δ z) = δ (W z) - δ z)
    (hDD : ∀ z, (d - δ) ((d - δ) z) = 0) (hγ : ∀ z, γ ((d - δ) z) = 0)
    (hT : ∀ (n : ℕ), ∀ x ∈ Module.End.eigenspace W (n : R),
      ∀ y ∈ ⨆ k < n, Module.End.eigenspace W ((k : ℕ) : R), γ (x + y) = 0 → σ x = 0)
    (hH : ∀ (n : ℕ), ∀ x ∈ Module.End.eigenspace W (n : R), d x = 0 → σ x = 0 →
      ∃ u ∈ Module.End.eigenspace W (n : R), d u = x)
    (z : M) (hz : (d - δ) z = 0) (hγz : γ z = 0) : ∃ u, (d - δ) u = z := by
  have mem := fun (n : ℕ) (x : M) => Module.End.mem_eigenspace_iff (f := W) (μ := (n : R))
    (x := x)
  have hd_eg : ∀ (n : ℕ) (x : M), x ∈ Module.End.eigenspace W (n : R) →
      d x ∈ Module.End.eigenspace W (n : R) := fun n x hx =>
    (mem n _).2 ((hdW x).symm.trans ((congrArg d ((mem n x).1 hx)).trans (map_smul d _ x)))
  have hδ_eg : ∀ (n : ℕ) (x : M), x ∈ Module.End.eigenspace W ((n + 1 : ℕ) : R) →
      δ x ∈ Module.End.eigenspace W (n : R) := fun n x hx => by
    rw [mem, hWδ, (mem (n + 1) x).1 hx, map_smul, Nat.cast_succ, add_smul, one_smul,
      add_sub_cancel_right]
  have hδ0 : ∀ x : M, x ∈ Module.End.eigenspace W ((0 : ℕ) : R) → δ x = 0 := fun x hx =>
    eq_zero_of_eigen_neg_one W htop (by
      rw [hWδ, (mem 0 x).1 hx, Nat.cast_zero, zero_smul, map_zero, zero_sub])
  have hmono : ∀ {n m : ℕ}, n ≤ m →
      (⨆ k < n, Module.End.eigenspace W ((k : ℕ) : R))
        ≤ ⨆ k < m, Module.End.eigenspace W ((k : ℕ) : R) := fun {n m} hnm =>
    iSup₂_le fun k hk => le_iSup₂_of_le k (hk.trans_le hnm) le_rfl
  have hδ_egL : ∀ (n : ℕ) (x : M), x ∈ Module.End.eigenspace W (n : R) →
      δ x ∈ ⨆ k < n, Module.End.eigenspace W ((k : ℕ) : R) := fun n x hx => by
    cases n with
    | zero => rw [hδ0 x hx]; exact zero_mem _
    | succ n => exact (le_iSup₂ (f := fun (k : ℕ) (_ : k < n + 1) =>
        Module.End.eigenspace W ((k : ℕ) : R)) n (Nat.lt_succ_self n)) (hδ_eg n x hx)
  have hd_L : ∀ (n : ℕ) (y : M), y ∈ ⨆ k < n, Module.End.eigenspace W ((k : ℕ) : R) →
      d y ∈ ⨆ k < n, Module.End.eigenspace W ((k : ℕ) : R) := fun n y hy =>
    (iSup₂_le (fun k hk x hx => (le_iSup₂ (f := fun (k : ℕ) (_ : k < n) =>
        Module.End.eigenspace W ((k : ℕ) : R)) k hk) (hd_eg k x hx)) :
      (⨆ k < n, Module.End.eigenspace W ((k : ℕ) : R))
        ≤ (⨆ k < n, Module.End.eigenspace W ((k : ℕ) : R)).comap d) hy
  have hδ_L : ∀ (n : ℕ) (y : M), y ∈ ⨆ k < n, Module.End.eigenspace W ((k : ℕ) : R) →
      δ y ∈ ⨆ k < n, Module.End.eigenspace W ((k : ℕ) : R) := fun n y hy =>
    (iSup₂_le (fun k hk x hx => hmono hk.le (hδ_egL k x hx)) :
      (⨆ k < n, Module.End.eigenspace W ((k : ℕ) : R))
        ≤ (⨆ k < n, Module.End.eigenspace W ((k : ℕ) : R)).comap δ) hy
  have hdisj : ∀ n : ℕ, Disjoint (Module.End.eigenspace W (n : R))
      (⨆ k < n, Module.End.eigenspace W ((k : ℕ) : R)) := fun n =>
    (iSupIndep_eigenspace_nat W n).mono_right
      (iSup₂_le fun k hk => le_iSup₂_of_le k (ne_of_lt hk) le_rfl)
  have key : ∀ (n : ℕ) (y : M), y ∈ ⨆ k < n, Module.End.eigenspace W ((k : ℕ) : R) →
      (d - δ) y = 0 → γ y = 0 → ∃ u, (d - δ) u = y := by
    intro n
    induction n with
    | zero =>
      intro y hy _ _
      have h0 : (⨆ k < 0, Module.End.eigenspace W ((k : ℕ) : R)) = ⊥ := by simp
      rw [h0, Submodule.mem_bot] at hy
      exact ⟨0, by rw [map_zero, hy]⟩
    | succ n ih =>
      intro y hy hDy hγy
      rw [Nat.iSup_lt_succ] at hy
      obtain ⟨y', hy', x, hx, rfl⟩ := Submodule.mem_sup.1 hy
      have hdx : d x = 0 := by
        have h1 : d x ∈ Module.End.eigenspace W (n : R) := hd_eg n x hx
        have h2 : d x ∈ ⨆ k < n, Module.End.eigenspace W ((k : ℕ) : R) := by
          have e : d x = δ y' + δ x - d y' := by
            have h3 := hDy
            rw [LinearMap.sub_apply, map_add, map_add, sub_eq_zero] at h3
            rw [← h3]
            abel
          rw [e]
          exact sub_mem (add_mem (hδ_L n y' hy') (hδ_egL n x hx)) (hd_L n y' hy')
        exact Submodule.disjoint_def.1 (hdisj n) _ h1 h2
      have hσx : σ x = 0 := hT n x hx y' hy' (by rwa [add_comm] at hγy)
      obtain ⟨u, hu, hdu⟩ := hH n x hx hdx hσx
      have e : y' + δ u = y' + x - (d - δ) u := by
        rw [LinearMap.sub_apply, hdu]
        abel
      obtain ⟨u', hu'⟩ := ih (y' + δ u) (add_mem hy' (hδ_egL n u hu))
        (by rw [e, map_sub, hDy, hDD, sub_zero]) (by rw [e, map_sub, hγy, hγ, sub_zero])
      exact ⟨u + u', by rw [map_add, hu', e]; abel⟩
  have hz' : z ∈ ⨆ n : ℕ, ⨆ k < n, Module.End.eigenspace W ((k : ℕ) : R) := by
    have hle : (⨆ j : ℕ, Module.End.eigenspace W (j : R))
        ≤ ⨆ n : ℕ, ⨆ k < n, Module.End.eigenspace W ((k : ℕ) : R) :=
      iSup_le fun j => le_iSup_of_le (j + 1)
        (le_iSup₂ (f := fun (k : ℕ) (_ : k < j + 1) => Module.End.eigenspace W ((k : ℕ) : R))
          j (Nat.lt_succ_self j))
    exact hle (htop ▸ Submodule.mem_top)
  obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _
    (Monotone.directed_le fun _ _ hnm => hmono hnm)).1 hz'
  exact key n z hn hz hγz

end WeightInduction

/-! ## The vertex count is a coderivation of the cut cooperad -/

namespace FreeGrL

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable (R V) in
/-- **The vertex count**: the derivation of the free graded operad extending the identity of the
generators, multiplying a tree with `n` vertices by `n`. -/
noncomputable abbrev vcount (A : Type) [Fintype A] [DecidableEq A] :
    FreeGrL R V A →ₗ[R] FreeGrL R V A :=
  (derSp (GrSpEnd.id R V)).app A

lemma vcount_of_mem_wtEqL {n : ℕ} {y : FreeGrL R V A} (hy : y ∈ wtEqL R V n A) :
    vcount R V A y = (n : R) • y :=
  mem_eig.1 (wtEqL_le_vx n hy)

/-- **The vertex count is a coderivation of the cut cooperad**: the vertices of the two parts of
a cut add up. -/
theorem decomp_vcount (i : A) (y : FreeGrL R V (Without A i ⊕ B)) :
    GrCooperad.decomp (R := R) (C := FreeGrL R V) i (vcount R V _ y)
      = TensorProduct.map (vcount R V A) LinearMap.id
          (GrCooperad.decomp (R := R) (C := FreeGrL R V) i y)
        + TensorProduct.map LinearMap.id (vcount R V B)
          (GrCooperad.decomp (R := R) (C := FreeGrL R V) i y) := by
  have hsub : ∀ (a : ℕ) (A : Type) [Fintype A] [DecidableEq A],
      vcount R V A ∘ₗ (wtEqL R V a A).subtype = (a : R) • (wtEqL R V a A).subtype :=
    fun a A _ _ => LinearMap.ext fun x => vcount_of_mem_wtEqL x.2
  have hle : ∀ n : ℕ, wtEqL R V n (Without A i ⊕ B)
      ≤ LinearMap.eqLocus
          (GrCooperad.decomp (R := R) (C := FreeGrL R V) (B := B) i ∘ₗ vcount R V _)
          ((TensorProduct.map (vcount R V A) LinearMap.id
            + TensorProduct.map LinearMap.id (vcount R V B)) ∘ₗ
              GrCooperad.decomp (R := R) (C := FreeGrL R V) i) := by
    intro n y hy
    have hS : (⨆ (a : ℕ) (b : ℕ) (_ : a + b = n), LinearMap.range (TensorProduct.map
          (wtEqL R V a A).subtype (wtEqL R V b B).subtype))
        ≤ LinearMap.eqLocus ((n : R) • LinearMap.id)
          (TensorProduct.map (vcount R V A) LinearMap.id
            + TensorProduct.map LinearMap.id (vcount R V B)) := by
      refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
      rintro _ ⟨t, rfl⟩
      have e1 : TensorProduct.map (vcount R V A) LinearMap.id
          (TensorProduct.map (wtEqL R V a A).subtype (wtEqL R V b B).subtype t)
          = (a : R) • TensorProduct.map (wtEqL R V a A).subtype (wtEqL R V b B).subtype t := by
        rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, hsub a A, LinearMap.id_comp,
          TensorProduct.map_smul_left, LinearMap.smul_apply]
      have e2 : TensorProduct.map LinearMap.id (vcount R V B)
          (TensorProduct.map (wtEqL R V a A).subtype (wtEqL R V b B).subtype t)
          = (b : R) • TensorProduct.map (wtEqL R V a A).subtype (wtEqL R V b B).subtype t := by
        rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, hsub b B, LinearMap.id_comp,
          TensorProduct.map_smul_right, LinearMap.smul_apply]
      rw [LinearMap.mem_eqLocus, LinearMap.add_apply, e1, e2, ← add_smul, ← Nat.cast_add, hab]
      rfl
    have h1 := LinearMap.mem_eqLocus.1 (hS (decomp_mem_wtEqL i hy))
    exact LinearMap.mem_eqLocus.2
      (((congrArg (GrCooperad.decomp (R := R) (C := FreeGrL R V) (B := B) i)
        (vcount_of_mem_wtEqL hy)).trans (map_smul _ _ _)).trans h1)
  have hy : y ∈ ⨆ n, wtEqL R V n (Without A i ⊕ B) :=
    (iSup_wtEqL (R := R) (V := V) (Without A i ⊕ B)).symm ▸ Submodule.mem_top
  exact LinearMap.mem_eqLocus.1 ((iSup_le hle) hy)

/-- A linear map vanishing on the trees whose number of vertices is not two takes the vertex
count to twice itself. -/
lemma apply_vcount_of_two {N' : Type*} [AddCommGroup N'] [Module R N']
    (S : FreeGrL R V A →ₗ[R] N')
    (hS : ∀ n : ℕ, n ≠ 2 → ∀ y ∈ wtEqL R V n A, S y = 0) (x : FreeGrL R V A) :
    S (vcount R V A x) = (2 : R) • S x := by
  have hle : ∀ n : ℕ, wtEqL R V n A
      ≤ LinearMap.eqLocus (S ∘ₗ vcount R V A) ((2 : R) • S) := by
    intro n y hy
    rw [LinearMap.mem_eqLocus, LinearMap.comp_apply, LinearMap.smul_apply,
      vcount_of_mem_wtEqL hy, map_smul]
    by_cases hn : n = 2
    · subst hn
      rw [Nat.cast_ofNat]
    · rw [hS n hn y hy, smul_zero, smul_zero]
  have hx : x ∈ ⨆ n, wtEqL R V n A :=
    (iSup_wtEqL (R := R) (V := V) A).symm ▸ Submodule.mem_top
  exact LinearMap.mem_eqLocus.1 ((iSup_le hle) hx)

end FreeGrL

/-! ## The subcooperad `K + N K` for an even coderivation -/

namespace GrSubCooperad

variable {R : Type u} [CommRing R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  (K : GrSubCooperad R C)

/-- **The subcooperad `K + N K`**, for linear maps `N` commuting with the parity projections and
the relabellings and satisfying the coderivation rule without signs. -/
def addCoder (N : ∀ (A : Type) [Fintype A] [DecidableEq A], C A →ₗ[R] C A)
    (hpar : ∀ (A : Type) [Fintype A] [DecidableEq A] (b : Bool) (x : C A),
      N A (GrSpecies.par (R := R) b x) = GrSpecies.par (R := R) b (N A x))
    (hmap : ∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
      (x : C A), N B (SymSpecies.map (R := R) e x) = SymSpecies.map (R := R) e (N A x))
    (hdec : ∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
      (x : C (Without A i ⊕ B)), GrCooperad.decomp (R := R) (C := C) i (N _ x)
        = TensorProduct.map (N A) LinearMap.id (GrCooperad.decomp (R := R) (C := C) i x)
          + TensorProduct.map LinearMap.id (N B) (GrCooperad.decomp (R := R) (C := C) i x)) :
    GrSubCooperad R C where
  sub A _ _ := K.sub A ⊔ (K.sub A).map (N A)
  par_mem := by
    intro A _ _ b x hx
    obtain ⟨a, ha, _, ⟨c, hc, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem_sup (K.par_mem b ha)
      ⟨GrSpecies.par (R := R) b c, K.par_mem b hc, hpar A b c⟩
  map_mem := by
    intro A B _ _ _ _ e x hx
    obtain ⟨a, ha, _, ⟨c, hc, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem_sup (K.map_mem e ha)
      ⟨SymSpecies.map (R := R) e c, K.map_mem e hc, hmap A B e c⟩
  decomp_mem := by
    intro A B _ _ _ _ i x hx
    obtain ⟨a, ha, _, ⟨c, hc, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
    have hK : ∀ (A : Type) [Fintype A] [DecidableEq A],
        K.sub A ≤ K.sub A ⊔ (K.sub A).map (N A) := fun A _ _ => le_sup_left
    have hd : ∀ (A : Type) [Fintype A] [DecidableEq A],
        (K.sub A).map (N A) ≤ K.sub A ⊔ (K.sub A).map (N A) := fun A _ _ => le_sup_right
    rw [map_add]
    refine add_mem (range_map_subtype_mono (hK A) (hK B) (K.decomp_mem i ha)) ?_
    rw [hdec]
    refine add_mem ?_ ?_
    · have h1 := map_range_map_subtype_le (N A) LinearMap.id
        (K.sub A) (K.sub B) (Submodule.mem_map_of_mem (K.decomp_mem i hc))
      rw [Submodule.map_id] at h1
      exact range_map_subtype_mono (hd A) (hK B) h1
    · have h1 := map_range_map_subtype_le LinearMap.id (N B)
        (K.sub A) (K.sub B) (Submodule.mem_map_of_mem (K.decomp_mem i hc))
      rw [Submodule.map_id] at h1
      exact range_map_subtype_mono (hK A) (hd B) h1

end GrSubCooperad

/-! ## The Koszul dual cooperad is graded by the vertices -/

namespace Koszul

open FreeGrL

variable {R : Type u} [Field R] [CharZero R]
  {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (E A)] [GrSpecies R E]
  {q : ∀ n : ℕ, Set (FreeGrL R E (Fin n))} {A : Type} [Fintype A] [DecidableEq A]

/-- **`κ_T ⋆ κ_T` after the vertex count is twice `κ_T ⋆ κ_T`**: it only sees the trees with two
vertices. -/
lemma star_vcount (x : Cut R E A) :
    ConvOp.toLin ((GrOperad.Inv.star R _ (kapT R E) (kapT R E)).1 A)
        (vcount R (GrSpecies.Shift E R) A x)
      = (2 : R) • ConvOp.toLin ((GrOperad.Inv.star R _ (kapT R E) (kapT R E)).1 A) x := by
  exact FreeGrL.apply_vcount_of_two _ (fun n hn y hy => star_wtEqL hn hy) x

/-- **The Koszul dual cooperad is stable under the vertex count.** -/
theorem vcount_mem_dual {x : Cut R E A} (hx : x ∈ (dualSub R E q).sub A) :
    vcount R (GrSpecies.Shift E R) A x ∈ (dualSub R E q).sub A := by
  have hK : (dualSub R E q).addCoder (fun A _ _ => vcount R (GrSpecies.Shift E R) A)
      (fun A _ _ b x => by
        have h := (derSp (GrSpEnd.id R (GrSpecies.Shift E R))).app_par b x
        rwa [Bool.xor_false] at h)
      (fun A B _ _ _ _ e x => (derSp (GrSpEnd.id R (GrSpecies.Shift E R))).app_map e x)
      (fun A B _ _ _ _ i x => decomp_vcount i x) ≤ dualSub R E q := by
    refine le_dualSub q fun A _ _ y hy => ?_
    obtain ⟨a, ha, _, ⟨c, hc, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add, star_vcount]
    exact add_mem (GrSubCooperad.cogen_le (admissible R E q) A ha)
      (Submodule.smul_mem _ _ (GrSubCooperad.cogen_le (admissible R E q) A hc))
  exact hK A (Submodule.mem_sup_right ⟨x, hx, rfl⟩)

/-- **The Koszul dual cooperad is spanned by its elements with a number of vertices.** -/
theorem mem_iSup_dual_inf_vx {x : Cut R E A} (hx : x ∈ (dualSub R E q).sub A) :
    x ∈ ⨆ n : ℕ, (dualSub R E q).sub A ⊓ vx R (GrSpecies.Shift E R) n A :=
  Submodule.mem_iSup_inf_eigenspace (vcount R (GrSpecies.Shift E R) A) _
    (fun _ hy => vcount_mem_dual hy) hx
    ((iSup_vx (R := R) (V := GrSpecies.Shift E R) A).symm ▸ Submodule.mem_top)

end Koszul

/-! ## The weights of the cobar construction of the Koszul dual dg cooperad -/

namespace Koszul

open FreeGrL

variable {R : Type u} [Field R] [CharZero R]
  {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (E A)] [GrSpecies R E]
  {r : ∀ n : ℕ, Set (FreeGrL R E (Fin n))} {I : GrOperadIdeal R (Pres R E r)}
  (hE : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : E A),
    (GrOperadIdeal.span R r).proj A ((FreeGrL.ι R E).app A v) ∈ I.sub A)
  {q : ∀ n : ℕ, Set (FreeGrL R E (Fin n))} (h : IsQL I q)
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

local notation "𝒥" => GrOperadIdeal.span R r

/-- The inclusion of the Koszul dual dg cooperad into the cut cooperad `T^c(sE)`, a morphism of
graded cooperads. -/
noncomputable def inclQL : GrCooperadHom R (DualQL hE h) (Cut R E) := (dualSub R E q).inclHom

lemma inclQL_injective : Function.Injective ((inclQL hE h).app A) :=
  (dualSub R E q).incl_injective A

/-- The vertex count of an element of the Koszul dual cooperad, in `T^c(sE)`. -/
noncomputable def vcountL (A : Type) [Fintype A] [DecidableEq A] :
    DualQL hE h A →ₗ[R] DualQL hE h A :=
  LinearMap.codRestrict ((dualSub R E q).sub A)
    (vcount R (GrSpecies.Shift E R) A ∘ₗ (inclQL hE h).app A) (fun x => vcount_mem_dual x.2)

lemma inclQL_vcountL (x : DualQL hE h A) :
    (inclQL hE h).app A (vcountL hE h A x)
      = vcount R (GrSpecies.Shift E R) A ((inclQL hE h).app A x) := rfl

/-- **The vertex count on the Koszul dual cooperad**, an even endomorphism of the species. -/
noncomputable def vcountD : GrSpEnd R (DualQL hE h) false where
  app A _ _ := vcountL hE h A
  app_map {A B} _ _ _ _ e x := inclQL_injective hE h (by
    rw [inclQL_vcountL, (inclQL hE h).app_map, (inclQL hE h).app_map, inclQL_vcountL]
    exact (derSp (GrSpEnd.id R (GrSpecies.Shift E R))).app_map e _)
  app_par {A} _ _ c x := inclQL_injective hE h (by
    rw [inclQL_vcountL, (inclQL hE h).app_par, (inclQL hE h).app_par, inclQL_vcountL,
      Bool.xor_false]
    have h1 := (derSp (GrSpEnd.id R (GrSpecies.Shift E R))).app_par c
      ((inclQL hE h).app A x)
    rwa [Bool.xor_false] at h1)

lemma vcountD_app (x : DualQL hE h A) : (vcountD hE h).app A x = vcountL hE h A x := rfl

/-- The vertex count kills the coaugmentation. -/
lemma vcountL_unitSpan {x : DualQL hE h A}
    (hx : x ∈ GrCooperad.unitSpan R (DualQL hE h) A) : vcountL hE h A x = 0 := by
  refine Submodule.span_induction (p := fun x _ => vcountL hE h A x = 0) ?_ (map_zero _) ?_ ?_ hx
  · rintro _ ⟨e, rfl⟩
    apply inclQL_injective hE h
    have h1 : (inclQL hE h).app A (vcountL hE h A (SymSpecies.map (R := R) e
        (GrCooperad.Coaug.one (R := R) (C := DualQL hE h)))) = 0 :=
      ((derSp (GrSpEnd.id R (GrSpecies.Shift E R))).app_map e _).trans
        ((congrArg _ (derSp (GrSpEnd.id R (GrSpecies.Shift E R))).app_one).trans (map_zero _))
    exact h1.trans (map_zero ((inclQL hE h).app A)).symm
  · intro x y _ _ hx hy
    rw [map_add, hx, hy, add_zero]
  · intro a x _ hx
    rw [map_smul, hx, smul_zero]

/-- **The vertex count on the generators `s⁻¹ (qP^¡)‾` of the cobar construction.** -/
noncomputable def vcountRed : GrSpEnd R (CobarGen R (DualQL hE h)) false where
  app A _ _ := Submodule.mapQ (GrCooperad.unitSpan R (DualQL hE h) A)
    (GrCooperad.unitSpan R (DualQL hE h) A) (vcountL hE h A) fun x hx => by
      rw [Submodule.mem_comap, vcountL_unitSpan hE h hx]
      exact zero_mem _
  app_map {A B} _ _ _ _ σ' v := by
    obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := DualQL hE h) A v
    exact congrArg (GrCooperad.Red.proj R (DualQL hE h) B) ((vcountD hE h).app_map σ' x)
  app_par {A} _ _ b v := by
    obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := DualQL hE h) A v
    have h1 := (vcountD hE h).app_par (!b) x
    rw [Bool.xor_false] at h1 ⊢
    exact congrArg (GrCooperad.Red.proj R (DualQL hE h) A) h1

lemma vcountRed_gen (x : DualQL hE h A) :
    (vcountRed hE h).app A (CobarMap.gen R (DualQL hE h) A x)
      = CobarMap.gen R (DualQL hE h) A (vcountL hE h A x) := rfl

/-- **The generators of the cobar construction are spanned by the eigenvectors of the vertex
count.** -/
theorem gen_mem_iSup_eigenspace (v : CobarGen R (DualQL hE h) A) :
    v ∈ ⨆ j : ℕ, Module.End.eigenspace ((vcountRed hE h).app A) (j : R) := by
  obtain ⟨x, rfl⟩ := CobarMap.gen_surjective (R := R) (C := DualQL hE h) A v
  have hmem : (inclQL hE h).app A x
      ∈ ⨆ n : ℕ, (dualSub R E q).sub A ⊓ vx R (GrSpecies.Shift E R) n A :=
    mem_iSup_dual_inf_vx x.2
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hmem
  have hx : x = ∑ j ∈ f.support, (⟨f j, (hf j).1⟩ : DualQL hE h A) :=
    inclQL_injective hE h (hsum.symm.trans (map_sum ((inclQL hE h).app A)
      (fun j => (⟨f j, (hf j).1⟩ : DualQL hE h A)) f.support).symm)
  have hgen : CobarMap.gen R (DualQL hE h) A x
      = ∑ j ∈ f.support, CobarMap.gen R (DualQL hE h) A (⟨f j, (hf j).1⟩ : DualQL hE h A) :=
    (congrArg (CobarMap.gen R (DualQL hE h) A) hx).trans
      (map_sum (CobarMap.gen R (DualQL hE h) A)
        (fun j => (⟨f j, (hf j).1⟩ : DualQL hE h A)) f.support)
  rw [hgen]
  refine Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j ?_
  have hj : vcountL hE h A (⟨f j, (hf j).1⟩ : DualQL hE h A)
      = (j : R) • (⟨f j, (hf j).1⟩ : DualQL hE h A) :=
    inclQL_injective hE h ((mem_eig.1 (hf j).2).trans
      (map_smul ((inclQL hE h).app A) (j : R) (⟨f j, (hf j).1⟩ : DualQL hE h A)).symm)
  exact Module.End.mem_eigenspace_iff.2 ((vcountRed_gen hE h _).trans
    ((congrArg (CobarMap.gen R (DualQL hE h) A) hj).trans (map_smul _ _ _)))

/-- **The weight derivation of `Ω(qP^¡, d_φ)`**: the even derivation counting the vertices of
the cooperations decorating the generators. -/
noncomputable def wtQL : GrDer (GrOperadHom.id R (CobarGr R (DualQL hE h))) false :=
  derSp (vcountRed hE h)

/-- **`Ω(qP^¡, d_φ)` is spanned by its elements with a weight.** -/
theorem iSup_wtQL (A : Type) [Fintype A] [DecidableEq A] :
    ⨆ j : ℕ, eig R (CobarGen R (DualQL hE h)) (vcountRed hE h) j A = ⊤ :=
  iSup_eig_eq_top (a := vcountRed hE h) (fun _ _ _ v => gen_mem_iSup_eigenspace hE h v) A

end Koszul

/-! ## The two parts of the differential and the weights -/

namespace FreeGrL

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)] [GrSpecies R W]
  {A : Type} [Fintype A] [DecidableEq A]

/-- The morphisms extending morphisms of the generators commute with the vertex counts. -/
lemma vcount_mapSp (φ : GrSpeciesHom R V W) (x : FreeGrL R V A) :
    vcount R W A ((mapSp φ).app A x) = (mapSp φ).app A (vcount R V A x) :=
  derSp_mapSp (a := GrSpEnd.id R V) (b := GrSpEnd.id R W) (fun _ _ _ _ => rfl) x

end FreeGrL

namespace Koszul

open FreeGrL

variable {R : Type u} [Field R] [CharZero R]
  {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (E A)] [GrSpecies R E]
  {r : ∀ n : ℕ, Set (FreeGrL R E (Fin n))} {I : GrOperadIdeal R (Pres R E r)}
  (hE : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : E A),
    (GrOperadIdeal.span R r).proj A ((FreeGrL.ι R E).app A v) ∈ I.sub A)
  {q : ∀ n : ℕ, Set (FreeGrL R E (Fin n))} (h : IsQL I q)
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

local notation "𝒥" => GrOperadIdeal.span R r

/-- **`d_φ` lowers the number of vertices by one**: `N d_φ = d_φ N - d_φ`, `N` the vertex
count, as the bar differential does. -/
theorem vcountL_dQL (x : DualQL hE h A) :
    vcountL hE h A (dQL hE h A x) = dQL hE h A (vcountL hE h A x) - dQL hE h A x := by
  apply toBarQ_injective hE h
  have hw : ∀ c : BarCoop I A, vcount R (BarGen I) A c
      = (FreeGrL.wtD R (BarGen I)).app A c := fun c =>
    (congrArg (fun D : GrDer (GrOperadHom.id R (FreeGrL R (BarGen I))) false => D.app A c)
      Cobar.wtD_eq_derSp).symm
  have s1 : (toBarQ hE q).app A (vcountL hE h A (dQL hE h A x))
      = vcount R (BarGen I) A ((toBarQ hE q).app A (dQL hE h A x)) :=
    (FreeGrL.vcount_mapSp (barGen I hE) _).symm
  have s2 : vcount R (BarGen I) A ((toBarQ hE q).app A (dQL hE h A x))
      = vcount R (BarGen I) A (DGCooperad.d (R := R) (C := BarCoop I) ((toBarQ hE q).app A x)) :=
    congrArg (vcount R (BarGen I) A) (toBarQ_dQL hE h x)
  have s3 : vcount R (BarGen I) A (DGCooperad.d (R := R) (C := BarCoop I)
        ((toBarQ hE q).app A x))
      = DGCooperad.d (R := R) (C := BarCoop I)
          (vcount R (BarGen I) A ((toBarQ hE q).app A x))
        - DGCooperad.d (R := R) (C := BarCoop I) ((toBarQ hE q).app A x) :=
    (hw _).trans ((Bar.wtD_d ((toBarQ hE q).app A x)).trans
      (congrArg (fun y => Bar.d I A y - Bar.d I A ((toBarQ hE q).app A x)) (hw _).symm))
  have s4 : DGCooperad.d (R := R) (C := BarCoop I)
        (vcount R (BarGen I) A ((toBarQ hE q).app A x))
      = (toBarQ hE q).app A (dQL hE h A (vcountL hE h A x)) :=
    (congrArg (DGCooperad.d (R := R) (C := BarCoop I))
      (FreeGrL.vcount_mapSp (barGen I hE) _)).trans (toBarQ_dQL hE h (vcountL hE h A x)).symm
  have s5 : DGCooperad.d (R := R) (C := BarCoop I) ((toBarQ hE q).app A x)
      = (toBarQ hE q).app A (dQL hE h A x) := (toBarQ_dQL hE h x).symm
  exact s1.trans (s2.trans (s3.trans ((congrArg₂ (· - ·) s4 s5).trans
    (map_sub ((toBarQ hE q).app A) _ _).symm)))

/-- **The part of the differential of `Ω(qP^¡, d_φ)` coming from `d_φ`**: the odd derivation
extending the differential of the generators. -/
noncomputable def deltaQL : GrDer (GrOperadHom.id R (CobarGr R (DualQL hE h))) true :=
  derSp (CobarDG.redD R (DualQL hE h))

/-- **The differential of `Ω(qP^¡, d_φ)` is the cobar differential minus the part coming from
`d_φ`.** -/
lemma cobarDG_d_app (z : CobarGr R (DualQL hE h) A) :
    (CobarDG.d R (DualQL hE h)).app A z
      = (Cobar.d R (DualQL hE h)).app A z - (deltaQL hE h).app A z :=
  congrArg (fun D : GrDer (GrOperadHom.id R (CobarGr R (DualQL hE h))) true => D.app A z)
    (CobarDG.d_eq_sub R (DualQL hE h))

/-- **The part coming from `d_φ` lowers the weight by one**: `W δ = δ W - δ`. -/
theorem wtQL_deltaQL (z : CobarGr R (DualQL hE h) A) :
    (wtQL hE h).app A ((deltaQL hE h).app A z)
      = (deltaQL hE h).app A ((wtQL hE h).app A z) - (deltaQL hE h).app A z := by
  have hD : ((wtQL hE h).gcomm (deltaQL hE h) :
      GrDer (GrOperadHom.id R (CobarGr R (DualQL hE h))) true)
      = (GrDer.zero (GrOperadHom.id R (CobarGr R (DualQL hE h))) true).sub (deltaQL hE h) :=
    FreeGrL.der_ext fun A _ _ v => by
      obtain ⟨x, rfl⟩ := CobarMap.gen_surjective (R := R) (C := DualQL hE h) A v
      have e1 : (deltaQL hE h).app A ((FreeGrL.ι R (CobarGen R (DualQL hE h))).app A
          (CobarMap.gen R (DualQL hE h) A x))
          = (FreeGrL.ι R (CobarGen R (DualQL hE h))).app A
            (CobarMap.gen R (DualQL hE h) A (dQL hE h A x)) := derSp_ι _ _
      have e2 : (wtQL hE h).app A ((FreeGrL.ι R (CobarGen R (DualQL hE h))).app A
          (CobarMap.gen R (DualQL hE h) A x))
          = (FreeGrL.ι R (CobarGen R (DualQL hE h))).app A
            (CobarMap.gen R (DualQL hE h) A (vcountL hE h A x)) := derSp_ι _ _
      have e3 : (wtQL hE h).app A ((FreeGrL.ι R (CobarGen R (DualQL hE h))).app A
          (CobarMap.gen R (DualQL hE h) A (dQL hE h A x)))
          = (FreeGrL.ι R (CobarGen R (DualQL hE h))).app A
            (CobarMap.gen R (DualQL hE h) A (vcountL hE h A (dQL hE h A x))) := derSp_ι _ _
      have e4 : (deltaQL hE h).app A ((FreeGrL.ι R (CobarGen R (DualQL hE h))).app A
          (CobarMap.gen R (DualQL hE h) A (vcountL hE h A x)))
          = (FreeGrL.ι R (CobarGen R (DualQL hE h))).app A
            (CobarMap.gen R (DualQL hE h) A (dQL hE h A (vcountL hE h A x))) := derSp_ι _ _
      show (wtQL hE h).app A ((deltaQL hE h).app A _)
          - σ R (false && true) • (deltaQL hE h).app A ((wtQL hE h).app A _)
        = 0 - (deltaQL hE h).app A _
      have hk : (FreeGrL.ι R (CobarGen R (DualQL hE h))).app A
            (CobarMap.gen R (DualQL hE h) A (vcountL hE h A (dQL hE h A x)))
          = (FreeGrL.ι R (CobarGen R (DualQL hE h))).app A
              (CobarMap.gen R (DualQL hE h) A (dQL hE h A (vcountL hE h A x)))
            - (FreeGrL.ι R (CobarGen R (DualQL hE h))).app A
              (CobarMap.gen R (DualQL hE h) A (dQL hE h A x)) :=
        (congrArg (fun y : DualQL hE h A => (FreeGrL.ι R (CobarGen R (DualQL hE h))).app A
          (CobarMap.gen R (DualQL hE h) A y)) (vcountL_dQL hE h x)).trans
          ((congrArg ((FreeGrL.ι R (CobarGen R (DualQL hE h))).app A)
            (map_sub (CobarMap.gen R (DualQL hE h) A) _ _)).trans (map_sub _ _ _))
      rw [e1, e2, e3, e4, Bool.false_and, σ_false, one_smul, zero_sub, hk]
      abel
  have h1 := congrArg (fun D : GrDer (GrOperadHom.id R (CobarGr R (DualQL hE h))) true =>
    D.app A z) hD
  have h2 : (wtQL hE h).app A ((deltaQL hE h).app A z)
      - σ R (false && true) • (deltaQL hE h).app A ((wtQL hE h).app A z)
      = 0 - (deltaQL hE h).app A z := h1
  have hσ : σ R (false && true) • (deltaQL hE h).app A ((wtQL hE h).app A z)
      = (deltaQL hE h).app A ((wtQL hE h).app A z) := by
    rw [Bool.false_and, σ_false, one_smul]
  exact ((sub_eq_iff_eq_add.1 (h2.trans (zero_sub _))).trans (neg_add_eq_sub _ _)).trans
    (congrArg (fun y => y - (deltaQL hE h).app A z) hσ)

/-- The inclusion `qP^¡ → T^c(sE)` preserves the coaugmentations. -/
lemma inclQL_one : (inclQL hE h).app Unit (GrCooperad.Coaug.one (R := R) (C := DualQL hE h))
    = GrCooperad.Coaug.one (R := R) (C := Cut R E) := rfl

/-- The morphism `Ω(qP^¡) → Ω(T^c(sE))` of the inclusion. -/
noncomputable def cobarIncl :
    GrOperadHom R (CobarGr R (DualQL hE h)) (CobarGr R (Cut R E)) :=
  CobarMap.map (inclQL hE h) (inclQL_one hE h)

/-- The inclusion is injective on the generators of the cobar constructions. -/
lemma redMap_inclQL_injective :
    Function.Injective ((CobarMap.redMap (inclQL hE h) (inclQL_one hE h)).app A) := by
  refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
  obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := DualQL hE h) A v
  have h1 : (inclQL hE h).app A x ∈ GrCooperad.unitSpan R (Cut R E) A :=
    (Submodule.Quotient.mk_eq_zero _).1 hv
  have h2 : Submodule.map ((inclQL hE h).app A) (GrCooperad.unitSpan R (DualQL hE h) A)
      = GrCooperad.unitSpan R (Cut R E) A := by
    rw [GrCooperad.unitSpan, GrCooperad.unitSpanOf, Submodule.map_span, ← Set.range_comp]
    rfl
  rw [← h2] at h1
  obtain ⟨y, hy, hxy⟩ := h1
  have hyx : y = x := inclQL_injective hE h hxy
  subst hyx
  exact (Submodule.Quotient.mk_eq_zero _).2 hy

/-- **`Ω(qP^¡) → Ω(T^c(sE))` is injective**, over a field of characteristic zero. -/
lemma cobarIncl_injective : Function.Injective ((cobarIncl hE h).app A) := by
  obtain ⟨g, hg⟩ := GrSpeciesHom.exists_retraction
    (CobarMap.redMap (inclQL hE h) (inclQL_one hE h))
    (fun A _ _ => redMap_inclQL_injective hE h)
  exact FreeGrL.mapSp_injective_of_retraction hg

/-- The weight derivations of `Ω(qP^¡)` and of `Ω(T^c(sE))` are intertwined. -/
lemma wtΩ_cobarIncl (z : CobarGr R (DualQL hE h) A) :
    (Cobar.wtΩ R (GrSpecies.Shift E R)).app A ((cobarIncl hE h).app A z)
      = (cobarIncl hE h).app A ((wtQL hE h).app A z) := by
  have hD : (Cobar.wtΩ R (GrSpecies.Shift E R)).compHom (cobarIncl hE h)
      = GrDer.homComp (cobarIncl hE h) (wtQL hE h) :=
    FreeGrL.der_ext fun A _ _ v => by
      obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := DualQL hE h) A v
      have e1 : (cobarIncl hE h).app A (Cobar.ιL R (DualQL hE h) A x)
          = Cobar.ιL R (Cut R E) A ((inclQL hE h).app A x) :=
        CobarMap.map_ιL (inclQL hE h) (inclQL_one hE h) x
      have e2 : (wtQL hE h).app A (Cobar.ιL R (DualQL hE h) A x)
          = Cobar.ιL R (DualQL hE h) A (vcountL hE h A x) := derSp_ι _ _
      have e3 : (cobarIncl hE h).app A (Cobar.ιL R (DualQL hE h) A (vcountL hE h A x))
          = Cobar.ιL R (Cut R E) A ((inclQL hE h).app A (vcountL hE h A x)) :=
        CobarMap.map_ιL (inclQL hE h) (inclQL_one hE h) _
      have e4 : (FreeGrL.wtD R (GrSpecies.Shift E R)).app A ((inclQL hE h).app A x)
          = (inclQL hE h).app A (vcountL hE h A x) :=
        congrArg (fun D : GrDer (GrOperadHom.id R (Cut R E)) false =>
          D.app A ((inclQL hE h).app A x)) Cobar.wtD_eq_derSp
      exact (congrArg ((Cobar.wtΩ R (GrSpecies.Shift E R)).app A) e1).trans
        ((Cobar.wtΩ_ιL _).trans ((congrArg (Cobar.ιL R (Cut R E) A) e4).trans
          (e3.symm.trans (congrArg ((cobarIncl hE h).app A) e2.symm))))
  exact congrArg (fun D : GrDer (cobarIncl hE h) false => D.app A z) hD

/-- **The cobar differential preserves the weights**: it commutes with the weight
derivation. -/
theorem d_wtQL (z : CobarGr R (DualQL hE h) A) :
    (Cobar.d R (DualQL hE h)).app A ((wtQL hE h).app A z)
      = (wtQL hE h).app A ((Cobar.d R (DualQL hE h)).app A z) := by
  apply cobarIncl_injective hE h
  have hV0 : ∀ v : GrSpecies.Shift E R (Fin 0), v = 0 := fun v =>
    h.gen_eq_zero hE (Fin 0) (by simp) v
  exact (CobarMap.d_map (inclQL hE h) (inclQL_one hE h) _).symm.trans
    ((congrArg ((Cobar.d R (Cut R E)).app A) (wtΩ_cobarIncl hE h z).symm).trans
      ((Cobar.d_wtΩ hV0 _).trans
        ((congrArg ((Cobar.wtΩ R (GrSpecies.Shift E R)).app A)
          (CobarMap.d_map (inclQL hE h) (inclQL_one hE h) z)).trans
          (wtΩ_cobarIncl hE h _))))

end Koszul

/-! ## The morphisms to `T(E)`, `qP` and `P`, and the weights -/

namespace FreeGrL

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {A : Type} [Fintype A] [DecidableEq A]

/-- A linear map vanishing on the trees whose number of vertices is not one does not see the
vertex count. -/
lemma apply_vcount_of_one {N' : Type*} [AddCommGroup N'] [Module R N']
    (S : FreeGrL R V A →ₗ[R] N')
    (hS : ∀ n : ℕ, n ≠ 1 → ∀ y ∈ wtEqL R V n A, S y = 0) (x : FreeGrL R V A) :
    S (vcount R V A x) = S x := by
  have hle : ∀ n : ℕ, wtEqL R V n A ≤ LinearMap.eqLocus (S ∘ₗ vcount R V A) S := by
    intro n y hy
    rw [LinearMap.mem_eqLocus, LinearMap.comp_apply, vcount_of_mem_wtEqL hy, map_smul]
    by_cases hn : n = 1
    · subst hn
      rw [Nat.cast_one, one_smul]
    · rw [hS n hn y hy, smul_zero]
  have hx : x ∈ ⨆ n, wtEqL R V n A :=
    (iSup_wtEqL (R := R) (V := V) A).symm ▸ Submodule.mem_top
  exact LinearMap.mem_eqLocus.1 ((iSup_le hle) hx)

end FreeGrL

namespace Koszul

variable {R : Type u} [Field R] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (E A)] [GrSpecies R E]
  {q : ∀ n : ℕ, Set (FreeGrL R E (Fin n))} {A : Type} [Fintype A] [DecidableEq A]

/-- The morphism `ΩP^¡ → P` desuspends the cogenerators. -/
lemma cobarMor_ιL (x : Dual R E q A) :
    (cobarMor R E q).1.app A (Cobar.ιL R (Dual R E q) A x)
      = (GrOperadIdeal.span R q).proj A (kapL R E A ((dualSub R E q).incl A x)) :=
  (Cobar.homOf_ιL _ _ _ x).trans (kappa_apply q x)

/-- **For a Koszul operad, a cycle of the cobar construction of `P^¡` killed by `ΩP^¡ → P` is a
boundary.** -/
lemma exists_cobar_d_eq (hK : IsKoszul R E q) {x : CobarGr R (Dual R E q) A}
    (hdx : (Cobar.d R (Dual R E q)).app A x = 0) (hσ : (cobarMor R E q).1.app A x = 0) :
    ∃ u₀ : CobarGr R (Dual R E q) A, (Cobar.d R (Dual R E q)).app A u₀ = x := by
  exact Homology.exists_eq_of_map_injective _ _ (hK A).1 hdx hσ

end Koszul

/-- A morphism of graded operads into `P` with the zero differential, into `P`. -/
def GrOperadHom.dropZeroDG {R : Type u} [CommRing R]
    {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
    {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
    (φ : GrOperadHom R Q (ZeroDG R P)) : GrOperadHom R Q P where
  app A _ _ := φ.app A
  app_par := φ.app_par
  app_map := φ.app_map
  app_one := φ.app_one
  app_comp := φ.app_comp

namespace Koszul

open FreeGrL

variable {R : Type u} [Field R] [CharZero R]
  {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (E A)] [GrSpecies R E]
  {r : ∀ n : ℕ, Set (FreeGrL R E (Fin n))} {I : GrOperadIdeal R (Pres R E r)}
  (hE : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : E A),
    (GrOperadIdeal.span R r).proj A ((FreeGrL.ι R E).app A v) ∈ I.sub A)
  {q : ∀ n : ℕ, Set (FreeGrL R E (Fin n))} (h : IsQL I q)
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

local notation "𝒥" => GrOperadIdeal.span R r

/-- The desuspension map `κ_T` on the Koszul dual dg cooperad, with values in `T(E)` with the
zero differential. -/
noncomputable def kapQL :
    GrOperad.Inv R (ConvOp R (DualQL hE h) (ZeroDG R (FreeGrL R E))) :=
  kapD R E q

lemma kapQL_apply (c : DualQL hE h A) :
    ConvOp.toLin ((kapQL hE h).1 A) c = kapL R E A ((inclQL hE h).app A c) := rfl

lemma isPar_kapQL : GrOperad.Inv.IsPar true (kapQL hE h) :=
  isPar_kapD (R := R) (E := E) (r := q)

/-- The desuspension map on `qP^¡` vanishes on the coaugmentation. -/
lemma killsUnit_kapQL :
    KillsUnit R (DualQL hE h) (ZeroDG R (FreeGrL R E)) (kapQL hE h) :=
  fun A _ _ _ hx => killsUnit_kapT (R := R) (E := E) A _ (incl_unitSpan q hx)

/-- **The morphism of graded operads `Ω(qP^¡) → T(E)` desuspending the cogenerators**:
`s⁻¹ c̄ ↦ κ_T c`. -/
noncomputable def cobarToFree : GrOperadHom R (CobarGr R (DualQL hE h)) (FreeGrL R E) :=
  (Cobar.homOf (kapQL hE h) (isPar_kapQL hE h) (killsUnit_kapQL hE h)).dropZeroDG

lemma cobarToFree_ιL (c : DualQL hE h A) :
    (cobarToFree hE h).app A (Cobar.ιL R (DualQL hE h) A c)
      = kapL R E A ((inclQL hE h).app A c) :=
  Cobar.homOf_ιL (kapQL hE h) (isPar_kapQL hE h) (killsUnit_kapQL hE h) c

/-- **The morphism `Ω(qP^¡, d_φ) → P` is the projection onto `P` after the morphism to
`T(E)`.** -/
theorem cobarMorQL_eq (z : CobarGr R (DualQL hE h) A) :
    (cobarMorQL hE h).app A z = (𝒥).proj A ((cobarToFree hE h).app A z) := by
  have hc : cobarMorQL hE h
      = (GrOperadHom.toZeroDG (𝒥).projHom).comp (cobarToFree hE h) :=
    FreeGrL.hom_ext fun A _ _ v => by
      obtain ⟨x, rfl⟩ := CobarMap.gen_surjective (R := R) (C := DualQL hE h) A v
      exact (cobarMorQL_ιL hE h x).trans
        (congrArg ((𝒥).proj A) (cobarToFree_ιL hE h x).symm)
  exact congrArg (fun φ : GrOperadHom R (CobarGr R (DualQL hE h)) (ZeroDG R (Pres R E r)) =>
    φ.app A z) hc

/-- The morphism `Ω(qP^¡) → qP` of the quadratic part, on the cobar construction of
`(qP^¡, d_φ)`, which has the same underlying graded operad. -/
noncomputable def cobarMorQ :
    GrOperadHom R (CobarGr R (DualQL hE h)) (ZeroDG R (Pres R E q)) :=
  (cobarMor R E q).1

/-- **The morphism `Ω(qP^¡) → qP` is the projection onto `qP` after the morphism to `T(E)`.** -/
theorem cobarMorQ_eq (z : CobarGr R (DualQL hE h) A) :
    (cobarMorQ hE h).app A z
      = (GrOperadIdeal.span R q).proj A ((cobarToFree hE h).app A z) := by
  have hc : cobarMorQ hE h
      = (GrOperadHom.toZeroDG (GrOperadIdeal.span R q).projHom).comp (cobarToFree hE h) :=
    FreeGrL.hom_ext fun A _ _ v => by
      obtain ⟨x, rfl⟩ := CobarMap.gen_surjective (R := R) (C := DualQL hE h) A v
      exact (cobarMor_ιL x).trans
        (congrArg ((GrOperadIdeal.span R q).proj A) (cobarToFree_ιL hE h x).symm)
  exact congrArg (fun φ : GrOperadHom R (CobarGr R (DualQL hE h)) (ZeroDG R (Pres R E q)) =>
    φ.app A z) hc

/-- **The morphism to `T(E)` takes the weight `n` to the trees with `n` vertices.** -/
theorem cobarToFree_mem_vx {n : ℕ} {z : CobarGr R (DualQL hE h) A}
    (hz : z ∈ eig R (CobarGen R (DualQL hE h)) (vcountRed hE h) n A) :
    (cobarToFree hE h).app A z ∈ vx R E n A := by
  have hD : (derSp (GrSpEnd.id R E)).compHom (cobarToFree hE h)
      = GrDer.homComp (cobarToFree hE h) (wtQL hE h) :=
    FreeGrL.der_ext fun A _ _ v => by
      obtain ⟨x, rfl⟩ := CobarMap.gen_surjective (R := R) (C := DualQL hE h) A v
      have e1 := cobarToFree_ιL hE h x
      have e2 : (wtQL hE h).app A (Cobar.ιL R (DualQL hE h) A x)
          = Cobar.ιL R (DualQL hE h) A (vcountL hE h A x) := derSp_ι _ _
      have e3 := cobarToFree_ιL hE h (vcountL hE h A x)
      have e4 : kapL R E A (vcount R (GrSpecies.Shift E R) A ((inclQL hE h).app A x))
          = kapL R E A ((inclQL hE h).app A x) :=
        FreeGrL.apply_vcount_of_one (kapL R E A)
          (fun n hn y hy => kapL_vx hn (wtEqL_le_vx n hy)) _
      have e5 : vcount R E A (kapL R E A ((inclQL hE h).app A x))
          = kapL R E A ((inclQL hE h).app A x) :=
        (mem_eig.1 (kapL_mem_vx _)).trans (by rw [Nat.cast_one, one_smul])
      exact (congrArg (vcount R E A) e1).trans (e5.trans (e4.symm.trans (e3.symm.trans
        (congrArg ((cobarToFree hE h).app A) e2.symm))))
  have h1 := congrArg (fun D : GrDer (cobarToFree hE h) false => D.app A z) hD
  exact mem_eig.2 (h1.trans ((congrArg ((cobarToFree hE h).app A) (mem_eig.1 hz)).trans
    (map_smul _ _ _)))

variable (r q) in
/-- **The Poincaré–Birkhoff–Witt property** of `P = T(E)/(r)` with quadratic part
`qP = T(E)/(q)`: an element of `(r)` with at most `n` vertices has its component with `n`
vertices in `(q)`. Then the associated graded of `P`, for the filtration by the vertices, is
`qP`. -/
def IsPBW : Prop :=
  ∀ (n : ℕ) (A : Type) [Fintype A] [DecidableEq A] (x y : FreeGrL R E A),
    x ∈ vx R E n A → y ∈ ⨆ k < n, vx R E k A → (𝒥).proj A (x + y) = 0 →
      x ∈ (GrOperadIdeal.span R q).sub A

/-- **The Poincaré–Birkhoff–Witt property gives the symbol condition**: an element of top
weight `n` killed by `Ω(qP^¡, d_φ) → P` has its component of weight `n` killed by
`Ω(qP^¡) → qP`. -/
theorem cobarMorQ_eq_zero_of_pbw
    (hPBW : IsPBW r q)
    {n : ℕ} {x y : CobarGr R (DualQL hE h) A}
    (hx : x ∈ eig R (CobarGen R (DualQL hE h)) (vcountRed hE h) n A)
    (hy : y ∈ ⨆ k < n, eig R (CobarGen R (DualQL hE h)) (vcountRed hE h) k A)
    (hγ : (cobarMorQL hE h).app A (x + y) = 0) : (cobarMorQ hE h).app A x = 0 := by
  have hy' : (cobarToFree hE h).app A y ∈ ⨆ k < n, vx R E k A :=
    (iSup₂_le (fun k hk z hz => (le_iSup₂ (f := fun (k : ℕ) (_ : k < n) => vx R E k A) k hk)
        (cobarToFree_mem_vx hE h hz)) :
      (⨆ k < n, eig R (CobarGen R (DualQL hE h)) (vcountRed hE h) k A)
        ≤ (⨆ k < n, vx R E k A).comap ((cobarToFree hE h).app A)) hy
  have h1 : (𝒥).proj A ((cobarToFree hE h).app A x + (cobarToFree hE h).app A y) = 0 :=
    (congrArg ((𝒥).proj A) (map_add ((cobarToFree hE h).app A) x y).symm).trans
      ((cobarMorQL_eq hE h (x + y)).symm.trans hγ)
  have h2 := hPBW n A _ _ (cobarToFree_mem_vx hE h hx) hy' h1
  exact (cobarMorQ_eq hE h x).trans (((GrOperadIdeal.span R q).proj_eq_zero_iff _).2 h2)

/-- The cobar differential preserves the weight spaces. -/
lemma d_mem_eig {n : ℕ} {z : CobarGr R (DualQL hE h) A}
    (hz : z ∈ eig R (CobarGen R (DualQL hE h)) (vcountRed hE h) n A) :
    (Cobar.d R (DualQL hE h)).app A z
      ∈ eig R (CobarGen R (DualQL hE h)) (vcountRed hE h) n A :=
  mem_eig.2 ((d_wtQL hE h z).symm.trans
    ((congrArg ((Cobar.d R (DualQL hE h)).app A) (mem_eig.1 hz)).trans (map_smul _ _ _)))

/-- **Koszulness of the quadratic part gives the exactness in each weight**: a cycle of weight
`n` of the cobar differential killed by `Ω(qP^¡) → qP` is the boundary of an element of weight
`n`. -/
theorem exists_d_eq_of_isKoszul (hK : IsKoszul R E q) {n : ℕ}
    {x : CobarGr R (DualQL hE h) A}
    (hx : x ∈ eig R (CobarGen R (DualQL hE h)) (vcountRed hE h) n A)
    (hdx : (Cobar.d R (DualQL hE h)).app A x = 0) (hσ : (cobarMorQ hE h).app A x = 0) :
    ∃ u ∈ eig R (CobarGen R (DualQL hE h)) (vcountRed hE h) n A,
      (Cobar.d R (DualQL hE h)).app A u = x := by
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : CobarGr R (DualQL hE h) A,
      (Cobar.d R (DualQL hE h)).app A u₀ = x := exists_cobar_d_eq hK (x := x) hdx hσ
  have htop : u₀ ∈ ⨆ j : ℕ, eig R (CobarGen R (DualQL hE h)) (vcountRed hE h) j A :=
    (iSup_wtQL hE h A).symm ▸ Submodule.mem_top
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 htop
  have hsum' : ∑ j ∈ insert n f.support, f j = u₀ :=
    (Finset.sum_subset (Finset.subset_insert n f.support)
      (fun j _ hj => Finsupp.notMem_support_iff.1 hj)).symm.trans hsum
  have hxs : ∀ j ∈ insert n f.support,
      (Cobar.d R (DualQL hE h)).app A (f j) - (if j = n then x else 0)
        ∈ Module.End.eigenspace ((wtQL hE h).app A) (j : R) := fun j _ => by
    refine sub_mem (d_mem_eig hE h (hf j)) ?_
    split_ifs with hj
    · subst hj
      exact hx
    · exact zero_mem _
  have hsum0 : ∑ j ∈ insert n f.support,
      ((Cobar.d R (DualQL hE h)).app A (f j) - (if j = n then x else 0)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_insert_self n _),
      ← map_sum, hsum', hu₀, sub_self]
  have hbot := Submodule.mem_of_sum_eigen ((wtQL hE h).app A) ⊥
    (fun y hy => by rw [(Submodule.mem_bot R).1 hy, map_zero]; exact zero_mem _)
    (insert n f.support)
    (fun j => (Cobar.d R (DualQL hE h)).app A (f j) - (if j = n then x else 0)) hxs
    (by rw [hsum0]; exact zero_mem _) n (Finset.mem_insert_self n _)
  have h1 : (Cobar.d R (DualQL hE h)).app A (f n) - (if n = n then x else 0) = 0 :=
    (Submodule.mem_bot R).1 hbot
  rw [if_pos rfl] at h1
  exact ⟨f n, hf n, sub_eq_zero.1 h1⟩

end Koszul

end Operad
