/-
# Decompositions at a splitting of the inputs

For a graded cooperad, every infinitesimal decomposition `C((A / i) ⊔ B) → C(A) ⊗ C(B)` is a
relabelling of the decomposition at a splitting of the inputs by a subset `S`, the one of the
inputs of the inner cooperation: `C(X) → C(X / S) ⊗ C(S)`.

* **A morphism of linear species commuting with the decompositions at the splittings commutes
  with all decompositions** (`GrCooperad.decomp_app_of_split`).
* **The counit laws at an input set with one element**, with the relabelling made explicit
  (`GrCooperad.lid_counit_decomp`, `GrCooperad.rid_counit_decomp`): the counit applied to the
  outer or the inner factor of a decomposition gives back the cooperation, relabelled. The
  relabelling depends only on the input sets, so the laws of two cooperads can be compared.
-/
import Operad.GrCooperad
import Operad.InvPreLie

universe u v w

namespace Operad

open Sym GerBV
open scoped TensorProduct

namespace GrCooperad

variable {R : Type u} [CommRing R]
  {K : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (K A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (K A)] [GrCooperad R K]
  {D : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (D A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (D A)] [GrCooperad R D]
  {A A' B B' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype B]
  [DecidableEq B] [Fintype B'] [DecidableEq B']

/-! ## The counit laws, with explicit relabellings -/

/-- The bijection of `Unit` onto a type all of whose elements are `i`. -/
def unitTo (i : A) (hA : ∀ a : A, a = i) : Unit ≃ A where
  toFun _ := i
  invFun _ := ()
  left_inv _ := rfl
  right_inv a := (hA a).symm

/-- The relabelling of the left counit law at an input set with one element `i`. -/
def lidEquiv (i : A) (hA : ∀ a : A, a = i) (B : Type) : Without A i ⊕ B ≃ B :=
  (compEquiv (unitTo i hA) (Equiv.refl B) ()).symm.trans (leftUnitEquiv B)

/-- The relabelling of the right counit law at an inner input set with one element `j`. -/
def ridEquiv (i : A) (j : B) (hB : ∀ b : B, b = j) : Without A i ⊕ B ≃ A :=
  (compEquiv (Equiv.refl A) (unitTo j hB) i).symm.trans (rightUnitEquiv i)

/-- **The left counit law at an input set with one element `i`**: the counit applied to the outer
factor of a decomposition at `i` gives back the cooperation, relabelled. -/
lemma lid_counit_decomp (i : A) (hA : ∀ a : A, a = i) (x : K (Without A i ⊕ B)) :
    TensorProduct.lid R (K B) (LinearMap.rTensor (K B)
      (GrCooperad.counit (R := R) (C := K) ∘ₗ SymSpecies.map (R := R) (unitTo i hA).symm)
      (GrCooperad.decomp (R := R) (C := K) i x))
      = SymSpecies.map (R := R) (lidEquiv i hA B) x := by
  set e := unitTo i hA
  set σ := compEquiv e (Equiv.refl B) ()
  have hnat : GrCooperad.decomp (R := R) (C := K) i x
      = TensorProduct.map (SymSpecies.map (R := R) e) (SymSpecies.map (R := R) (Equiv.refl B))
        (GrCooperad.decomp (R := R) (C := K) () (SymSpecies.map (R := R) σ.symm x)) := by
    have h := LinearMap.congr_fun (GrCooperad.decomp_map (R := R) (C := K) e (Equiv.refl B) ())
      (SymSpecies.map (R := R) σ.symm x)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, SymSpecies.map_map_symm] at h
    exact h
  have hcl := LinearMap.congr_fun (GrCooperad.counit_left (R := R) (C := K) (B := B))
    (SymSpecies.map (R := R) (leftUnitEquiv B) (SymSpecies.map (R := R) σ.symm x))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, SymSpecies.map_symm_map,
    LinearMap.id_apply] at hcl
  refine Eq.trans ?_ ((SymSpecies.map_trans (R := R) σ.symm (leftUnitEquiv B) x).trans
    hcl.symm).symm
  rw [hnat]
  generalize GrCooperad.decomp (R := R) (C := K) () (SymSpecies.map (R := R) σ.symm x) = s
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.comp_apply,
      TensorProduct.lid_tmul, SymSpecies.map_symm_map, SymSpecies.map_refl]
  | add s s' hs hs' => simp only [map_add, hs, hs']

/-- **The right counit law at an inner input set with one element `j`**: the counit applied to
the inner factor of a decomposition gives back the cooperation, relabelled. -/
lemma rid_counit_decomp (i : A) (j : B) (hB : ∀ b : B, b = j) (x : K (Without A i ⊕ B)) :
    TensorProduct.rid R (K A) (LinearMap.lTensor (K A)
      (GrCooperad.counit (R := R) (C := K) ∘ₗ SymSpecies.map (R := R) (unitTo j hB).symm)
      (GrCooperad.decomp (R := R) (C := K) i x))
      = SymSpecies.map (R := R) (ridEquiv i j hB) x := by
  set e := unitTo j hB
  set σ := compEquiv (Equiv.refl A) e i
  have hnat : GrCooperad.decomp (R := R) (C := K) i x
      = TensorProduct.map (SymSpecies.map (R := R) (Equiv.refl A)) (SymSpecies.map (R := R) e)
        (GrCooperad.decomp (R := R) (C := K) i (SymSpecies.map (R := R) σ.symm x)) := by
    have h := LinearMap.congr_fun (GrCooperad.decomp_map (R := R) (C := K) (Equiv.refl A) e i)
      (SymSpecies.map (R := R) σ.symm x)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, SymSpecies.map_map_symm] at h
    exact h
  have hcl := LinearMap.congr_fun (GrCooperad.counit_right (R := R) (C := K) i)
    (SymSpecies.map (R := R) (rightUnitEquiv i) (SymSpecies.map (R := R) σ.symm x))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, SymSpecies.map_symm_map,
    LinearMap.id_apply] at hcl
  refine Eq.trans ?_ ((SymSpecies.map_trans (R := R) σ.symm (rightUnitEquiv i) x).trans
    hcl.symm).symm
  rw [hnat]
  generalize GrCooperad.decomp (R := R) (C := K) i (SymSpecies.map (R := R) σ.symm x) = s
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.comp_apply,
      TensorProduct.rid_tmul, SymSpecies.map_symm_map, SymSpecies.map_refl]
  | add s s' hs hs' => simp only [map_add, hs, hs']

/-! ## Decompositions at a splitting -/

/-- **Naturality of the decomposition, at a slot given up to equality** and along a bijection
given by its values. -/
lemma decomp_map_of_eq (σ : A ≃ A') (τ : B ≃ B') {i : A} {i' : A'} (hi : σ i = i')
    (Θ : Without A i ⊕ B ≃ Without A' i' ⊕ B')
    (hl : ∀ a : Without A i, ∃ h, Θ (Sum.inl a) = Sum.inl ⟨σ a.1, h⟩)
    (hr : ∀ b : B, Θ (Sum.inr b) = Sum.inr (τ b)) (x : K (Without A i ⊕ B)) :
    GrCooperad.decomp (R := R) (C := K) i' (SymSpecies.map (R := R) Θ x)
      = TensorProduct.map (SymSpecies.map (R := R) σ) (SymSpecies.map (R := R) τ)
          (GrCooperad.decomp (R := R) (C := K) i x) := by
  subst hi
  have e : Θ = compEquiv σ τ i := Equiv.ext fun z => by
    rcases z with a | b
    · obtain ⟨h, ha⟩ := hl a
      exact ha
    · exact hr b
  rw [e]
  exact LinearMap.congr_fun (GrCooperad.decomp_map (R := R) (C := K) σ τ i) x

/-- **A morphism of linear species commuting with the decompositions at the splittings of the
inputs commutes with all decompositions.** -/
theorem decomp_app_of_split (F : SymSpeciesHom R K D)
    (h : ∀ (X : Type) [Fintype X] [DecidableEq X] (S : Finset X)
      (x : K (Without (SOut S) none ⊕ SIn S)),
      GrCooperad.decomp (R := R) (C := D) none (F.app _ x)
        = TensorProduct.map (F.app (SOut S)) (F.app (SIn S))
            (GrCooperad.decomp (R := R) (C := K) none x))
    (i : A) (x : K (Without A i ⊕ B)) :
    GrCooperad.decomp (R := R) (C := D) i (F.app _ x)
      = TensorProduct.map (F.app A) (F.app B) (GrCooperad.decomp (R := R) (C := K) i x) := by
  set S : Finset (Without A i ⊕ B) := Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩ with hSdef
  have hS : ∀ z, z ∈ S ↔ ∃ b, (Equiv.refl (Without A i ⊕ B)) (Sum.inr b) = z := fun z => by
    simp [S, eq_comm]
  obtain ⟨σ, hσ⟩ : ∃ σ : A ≃ SOut S, σ = GrOperad.canonOut (Equiv.refl _) S hS := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : B ≃ SIn S, τ = GrOperad.canonIn (Equiv.refl _) S hS := ⟨_, rfl⟩
  have hi : σ i = none := by rw [hσ, GrOperad.canonOut_self]
  have hl : ∀ a : Without A i, ∃ h,
      (splitEquiv S).symm (Sum.inl a) = Sum.inl ⟨σ a.1, h⟩ := fun a => by
    have hne : σ a.1 ≠ none := fun h0 => a.2 (σ.injective (h0.trans hi.symm))
    refine ⟨hne, (Equiv.symm_apply_eq _).2 ?_⟩
    rw [splitEquiv_inl]
    exact (outVal_eq_of_eq hne (by rw [hσ, GrOperad.canonOut_ne _ S hS a.2])).symm
  have hr : ∀ b : B, (splitEquiv S).symm (Sum.inr b) = Sum.inr (τ b) := fun b =>
    (Equiv.symm_apply_eq _).2 (by rw [splitEquiv_inr, hτ, GrOperad.canonIn_apply]; rfl)
  have hK := decomp_map_of_eq (R := R) (K := K) σ τ hi (splitEquiv S).symm hl hr x
  have hD := decomp_map_of_eq (R := R) (K := D) σ τ hi (splitEquiv S).symm hl hr (F.app _ x)
  have h1 : ∀ t : K A ⊗[R] K B, TensorProduct.map (F.app (SOut S)) (F.app (SIn S))
      (TensorProduct.map (SymSpecies.map (R := R) σ) (SymSpecies.map (R := R) τ) t)
        = TensorProduct.map (SymSpecies.map (R := R) σ) (SymSpecies.map (R := R) τ)
          (TensorProduct.map (F.app A) (F.app B) t) := fun t => by
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp,
      show F.app (SOut S) ∘ₗ SymSpecies.map (R := R) σ = SymSpecies.map (R := R) σ ∘ₗ F.app A
        from LinearMap.ext (F.app_map σ),
      show F.app (SIn S) ∘ₗ SymSpecies.map (R := R) τ = SymSpecies.map (R := R) τ ∘ₗ F.app B
        from LinearMap.ext (F.app_map τ),
      TensorProduct.map_comp, LinearMap.comp_apply]
  have h0 := h _ S (SymSpecies.map (R := R) (splitEquiv S).symm x)
  rw [F.app_map, hD, hK, h1] at h0
  have hinv : ∀ t : D A ⊗[R] D B,
      TensorProduct.map (SymSpecies.map (R := R) σ.symm) (SymSpecies.map (R := R) τ.symm)
        (TensorProduct.map (SymSpecies.map (R := R) σ) (SymSpecies.map (R := R) τ) t) = t :=
    fun t => by
      rw [← LinearMap.comp_apply, ← TensorProduct.map_comp,
        show SymSpecies.map (R := R) (V := D) σ.symm ∘ₗ SymSpecies.map (R := R) σ = LinearMap.id
          from LinearMap.ext (SymSpecies.map_symm_map σ),
        show SymSpecies.map (R := R) (V := D) τ.symm ∘ₗ SymSpecies.map (R := R) τ = LinearMap.id
          from LinearMap.ext (SymSpecies.map_symm_map τ),
        TensorProduct.map_id, LinearMap.id_apply]
  have h2 := congrArg (TensorProduct.map (SymSpecies.map (R := R) σ.symm)
    (SymSpecies.map (R := R) τ.symm)) h0
  rwa [hinv, hinv] at h2

end GrCooperad

end Operad
