/-
# Splittings of differentials on graded linear species, over fields of characteristic zero

Over a field of characteristic zero, **every odd endomorphism `d` of a graded linear species with
`d² = 0` has a splitting** (`Splitting.exists_of_field`): an idempotent `p` onto a complement of the
boundaries in the cycles and a homotopy `h` with `d h + h d = 1 - p`, both commuting with the
relabellings and compatible with the parities.

On the standard finite type `Fin n`, a projection onto a subspace stable under the permutations
and the parities is made equivariant by averaging over the permutations (`avgPerm`) and taking its
diagonal part for the parities (`diagPar`) (`exists_proj`). With equivariant projections `π_Z`
onto the cycles and `π_B` onto the boundaries, `p = (1 - π_B) π_Z`, and `h` inverts `d` from the
kernel of `π_Z` onto the boundaries. Endomorphisms on the standard finite types commuting with
their permutations extend to all finite types through numberings (`GrSpEnd.extend`).
-/
import Operad.FreeGrKunneth
import Mathlib.LinearAlgebra.Basis.VectorSpace

universe u v w

namespace Operad

open Sym GerBV

variable {R : Type u} [Field R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]

/-! ## Endomorphisms on the standard finite types -/

namespace GrSpEnd

lemma map_symm_map' {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (σ : A ≃ B) (x : V A) :
    SymSpecies.map (R := R) σ.symm (SymSpecies.map (R := R) σ x) = x := by
  rw [← SymSpecies.map_trans, Equiv.self_trans_symm, SymSpecies.map_refl]

lemma map_map_symm' {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (σ : A ≃ B) (x : V B) :
    SymSpecies.map (R := R) σ (SymSpecies.map (R := R) σ.symm x) = x := by
  rw [← SymSpecies.map_trans, Equiv.symm_trans_self, SymSpecies.map_refl]

variable {e : Bool} (f : ∀ n : ℕ, V (Fin n) →ₗ[R] V (Fin n))
  (hf : ∀ (n : ℕ) (σ : Fin n ≃ Fin n) (x : V (Fin n)),
    f n (SymSpecies.map (R := R) σ x) = SymSpecies.map (R := R) σ (f n x))

include hf in
/-- The extension through a numbering does not depend on the numbering. -/
lemma extendApp_chart' {A : Type} [Fintype A] [DecidableEq A] {n : ℕ} (φ : Fin n ≃ A)
    (x : V A) :
    GrSpeciesHom.extendApp f A x
      = SymSpecies.map (R := R) φ (f n (SymSpecies.map (R := R) φ.symm x)) := by
  have hn : n = Fintype.card A := by simpa using Fintype.card_congr φ
  subst hn
  set ψ := (Fintype.equivFin A).symm
  have hσ : SymSpecies.map (R := R) ψ.symm x
      = SymSpecies.map (R := R) (φ.trans ψ.symm) (SymSpecies.map (R := R) φ.symm x) := by
    rw [← SymSpecies.map_trans, ← Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.refl_trans]
  show SymSpecies.map (R := R) ψ (f _ (SymSpecies.map (R := R) ψ.symm x)) = _
  rw [hσ, hf, ← SymSpecies.map_trans, Equiv.trans_assoc, Equiv.symm_trans_self,
    Equiv.trans_refl]

/-- **The endomorphism extending a family on the standard finite types** commuting with their
permutations and shifting the parities by `e`. -/
noncomputable def extend
    (hp : ∀ (n : ℕ) (c : Bool) (x : V (Fin n)),
      f n (GrSpecies.par (R := R) c x) = GrSpecies.par (R := R) (xor c e) (f n x)) :
    GrSpEnd R V e where
  app A _ _ := GrSpeciesHom.extendApp f A
  app_map {A B} _ _ _ _ σ' x := by
    have h1 : SymSpecies.map (R := R) ((Fintype.equivFin A).symm.trans σ').symm
        (SymSpecies.map (R := R) σ' x) = SymSpecies.map (R := R) (Fintype.equivFin A) x := by
      rw [← SymSpecies.map_trans]
      exact congrArg (fun g => SymSpecies.map (R := R) g x) (Equiv.ext fun a => by simp)
    rw [extendApp_chart' f hf ((Fintype.equivFin A).symm.trans σ'), h1, SymSpecies.map_trans]
    rfl
  app_par {A} _ _ c x := by
    show SymSpecies.map (R := R) _ (f _ (SymSpecies.map (R := R) _ (GrSpecies.par (R := R) c x)))
      = GrSpecies.par (R := R) (xor c e)
        (SymSpecies.map (R := R) _ (f _ (SymSpecies.map (R := R) _ x)))
    rw [GrSpecies.map_par, hp, GrSpecies.map_par]

variable {f hf}

lemma extend_app_chart
    {hp : ∀ (n : ℕ) (c : Bool) (x : V (Fin n)),
      f n (GrSpecies.par (R := R) c x) = GrSpecies.par (R := R) (xor c e) (f n x)}
    {A : Type} [Fintype A] [DecidableEq A] {n : ℕ} (φ : Fin n ≃ A) (x : V A) :
    (extend f hf hp).app A x
      = SymSpecies.map (R := R) φ (f n (SymSpecies.map (R := R) φ.symm x)) :=
  extendApp_chart' f hf φ x

end GrSpEnd

/-- An endomorphism computed through a numbering. -/
lemma GrSpEnd.app_chart {e : Bool} (a : GrSpEnd R V e) {A : Type} [Fintype A] [DecidableEq A]
    {n : ℕ} (φ : Fin n ≃ A) (x : V A) :
    a.app A x = SymSpecies.map (R := R) φ (a.app (Fin n) (SymSpecies.map (R := R) φ.symm x)) := by
  rw [← a.app_map, GrSpEnd.map_map_symm']

/-! ## Averaging over the permutations -/

section Average

variable {n : ℕ}

/-- **The average over the permutations** of a linear map on `V (Fin n)`. -/
noncomputable def avgPerm (q : V (Fin n) →ₗ[R] V (Fin n)) : V (Fin n) →ₗ[R] V (Fin n) :=
  ((Fintype.card (Equiv.Perm (Fin n)) : R)⁻¹) • ∑ σ : Equiv.Perm (Fin n),
    SymSpecies.map (R := R) (V := V) σ ∘ₗ q ∘ₗ SymSpecies.map (R := R) (V := V) σ.symm

lemma avgPerm_apply (q : V (Fin n) →ₗ[R] V (Fin n)) (x : V (Fin n)) :
    avgPerm q x = ((Fintype.card (Equiv.Perm (Fin n)) : R)⁻¹) • ∑ σ : Equiv.Perm (Fin n),
      SymSpecies.map (R := R) σ (q (SymSpecies.map (R := R) σ.symm x)) := by
  simp only [avgPerm, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]

/-- **The average commutes with the permutations.** -/
lemma avgPerm_map (q : V (Fin n) →ₗ[R] V (Fin n)) (τ : Equiv.Perm (Fin n)) (x : V (Fin n)) :
    avgPerm q (SymSpecies.map (R := R) τ x) = SymSpecies.map (R := R) τ (avgPerm q x) := by
  rw [avgPerm_apply, avgPerm_apply, map_smul, map_sum]
  congr 1
  rw [← Equiv.sum_comp (Equiv.mulLeft τ)]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  simp only [Equiv.coe_mulLeft, Equiv.Perm.mul_def]
  rw [← SymSpecies.map_trans (R := R) (V := V) ρ τ (q _)]
  congr 2
  rw [← SymSpecies.map_trans]
  exact congrArg (fun g => SymSpecies.map (R := R) g x) (Equiv.ext fun a => by simp)

/-- The average of a map commuting with the parities commutes with them. -/
lemma avgPerm_par {q : V (Fin n) →ₗ[R] V (Fin n)}
    (hq : ∀ (b : Bool) (x : V (Fin n)),
      q (GrSpecies.par (R := R) b x) = GrSpecies.par (R := R) b (q x)) (b : Bool)
    (x : V (Fin n)) :
    avgPerm q (GrSpecies.par (R := R) b x) = GrSpecies.par (R := R) b (avgPerm q x) := by
  rw [avgPerm_apply, avgPerm_apply, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [GrSpecies.map_par, hq, GrSpecies.map_par]

/-- The average of a map into a stable subspace maps into it. -/
lemma avgPerm_mem {W : Submodule R (V (Fin n))}
    (hW : ∀ (σ : Equiv.Perm (Fin n)), ∀ w ∈ W, SymSpecies.map (R := R) σ w ∈ W)
    {q : V (Fin n) →ₗ[R] V (Fin n)} (hq : ∀ x, q x ∈ W) (x : V (Fin n)) : avgPerm q x ∈ W := by
  rw [avgPerm_apply]
  exact W.smul_mem _ (W.sum_mem fun σ _ => hW σ _ (hq _))

/-- The average of a map fixing a stable subspace fixes it. -/
lemma avgPerm_self [CharZero R] {W : Submodule R (V (Fin n))}
    (hW : ∀ (σ : Equiv.Perm (Fin n)), ∀ w ∈ W, SymSpecies.map (R := R) σ w ∈ W)
    {q : V (Fin n) →ₗ[R] V (Fin n)} (hq : ∀ w ∈ W, q w = w) {w : V (Fin n)} (hw : w ∈ W) :
    avgPerm q w = w := by
  rw [avgPerm_apply]
  have : ∀ σ : Equiv.Perm (Fin n),
      SymSpecies.map (R := R) σ (q (SymSpecies.map (R := R) σ.symm w)) = w := fun σ => by
    rw [hq _ (hW _ w hw), GrSpEnd.map_map_symm']
  rw [Finset.sum_congr rfl fun σ _ => this σ, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul R, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_smul]

/-- **The diagonal part for the parities** of a linear map. -/
noncomputable def diagPar (q : V (Fin n) →ₗ[R] V (Fin n)) : V (Fin n) →ₗ[R] V (Fin n) :=
  GrSpecies.par (R := R) false ∘ₗ q ∘ₗ GrSpecies.par (R := R) false
    + GrSpecies.par (R := R) true ∘ₗ q ∘ₗ GrSpecies.par (R := R) true

lemma diagPar_apply (q : V (Fin n) →ₗ[R] V (Fin n)) (x : V (Fin n)) :
    diagPar q x = GrSpecies.par (R := R) false (q (GrSpecies.par (R := R) false x))
      + GrSpecies.par (R := R) true (q (GrSpecies.par (R := R) true x)) := rfl

lemma diagPar_par (q : V (Fin n) →ₗ[R] V (Fin n)) (b : Bool) (x : V (Fin n)) :
    diagPar q (GrSpecies.par (R := R) b x) = GrSpecies.par (R := R) b (diagPar q x) := by
  simp only [diagPar_apply, map_add, GrSpecies.par_par]
  cases b <;> simp

lemma diagPar_map {q : V (Fin n) →ₗ[R] V (Fin n)}
    (hq : ∀ (σ : Equiv.Perm (Fin n)) (x : V (Fin n)),
      q (SymSpecies.map (R := R) σ x) = SymSpecies.map (R := R) σ (q x))
    (σ : Equiv.Perm (Fin n)) (x : V (Fin n)) :
    diagPar q (SymSpecies.map (R := R) σ x) = SymSpecies.map (R := R) σ (diagPar q x) := by
  simp only [diagPar_apply, map_add, ← GrSpecies.map_par, hq]

lemma diagPar_mem {W : Submodule R (V (Fin n))}
    (hW : ∀ (b : Bool), ∀ w ∈ W, GrSpecies.par (R := R) b w ∈ W)
    {q : V (Fin n) →ₗ[R] V (Fin n)} (hq : ∀ x, q x ∈ W) (x : V (Fin n)) : diagPar q x ∈ W :=
  W.add_mem (hW _ _ (hq _)) (hW _ _ (hq _))

lemma diagPar_self {W : Submodule R (V (Fin n))}
    (hW : ∀ (b : Bool), ∀ w ∈ W, GrSpecies.par (R := R) b w ∈ W)
    {q : V (Fin n) →ₗ[R] V (Fin n)} (hq : ∀ w ∈ W, q w = w) {w : V (Fin n)} (hw : w ∈ W) :
    diagPar q w = w := by
  rw [diagPar_apply, hq _ (hW _ w hw), hq _ (hW _ w hw), GrSpecies.par_par_self,
    GrSpecies.par_par_self, GrSpecies.par_add]

/-- **Equivariant projections**: a subspace of `V (Fin n)` stable under the permutations and the
parities is the image of a projection commuting with them, over a field of characteristic zero. -/
theorem exists_proj [CharZero R] (W : Submodule R (V (Fin n)))
    (hWm : ∀ (σ : Equiv.Perm (Fin n)), ∀ w ∈ W, SymSpecies.map (R := R) σ w ∈ W)
    (hWp : ∀ (b : Bool), ∀ w ∈ W, GrSpecies.par (R := R) b w ∈ W) :
    ∃ π : V (Fin n) →ₗ[R] V (Fin n), (∀ x, π x ∈ W) ∧ (∀ w ∈ W, π w = w) ∧
      (∀ (σ : Equiv.Perm (Fin n)) (x : V (Fin n)),
        π (SymSpecies.map (R := R) σ x) = SymSpecies.map (R := R) σ (π x)) ∧
      (∀ (b : Bool) (x : V (Fin n)),
        π (GrSpecies.par (R := R) b x) = GrSpecies.par (R := R) b (π x)) := by
  obtain ⟨K, hK⟩ := Submodule.exists_isCompl W
  set q₀ := W.projection K hK
  have hq₀ : ∀ x, q₀ x ∈ W := fun x => Submodule.projection_apply_mem hK x
  have hq₀' : ∀ w ∈ W, q₀ w = w := fun w hw => Submodule.projection_apply_left hK ⟨w, hw⟩
  refine ⟨avgPerm (diagPar q₀), fun x => avgPerm_mem hWm (fun x => diagPar_mem hWp hq₀ x) x,
    fun w hw => avgPerm_self hWm (fun w hw => diagPar_self hWp hq₀' hw) hw,
    fun σ x => avgPerm_map _ σ x, fun b x => avgPerm_par (fun b x => diagPar_par q₀ b x) b x⟩

end Average


/-! ## Splittings -/

section Split

variable [CharZero R] (d : GrSpEnd R V true)
  (hdd : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : V A), d.app A (d.app A x) = 0)
include hdd

/-- **A splitting on a standard finite type.** -/
theorem exists_level_splitting (n : ℕ) :
    ∃ p h : V (Fin n) →ₗ[R] V (Fin n),
      (∀ (σ : Equiv.Perm (Fin n)) (x : V (Fin n)),
        p (SymSpecies.map (R := R) σ x) = SymSpecies.map (R := R) σ (p x)) ∧
      (∀ (σ : Equiv.Perm (Fin n)) (x : V (Fin n)),
        h (SymSpecies.map (R := R) σ x) = SymSpecies.map (R := R) σ (h x)) ∧
      (∀ (c : Bool) (x : V (Fin n)),
        p (GrSpecies.par (R := R) c x) = GrSpecies.par (R := R) (xor c false) (p x)) ∧
      (∀ (c : Bool) (x : V (Fin n)),
        h (GrSpecies.par (R := R) c x) = GrSpecies.par (R := R) (xor c true) (h x)) ∧
      (∀ x, p (p x) = p x) ∧ (∀ x, d.app (Fin n) (p x) = 0) ∧ (∀ x, p (d.app (Fin n) x) = 0) ∧
      (∀ x, d.app (Fin n) (h x) + h (d.app (Fin n) x) = x - p x) := by
  set D := d.app (Fin n) with hD
  have hZm : ∀ (σ : Equiv.Perm (Fin n)), ∀ z ∈ LinearMap.ker D,
      SymSpecies.map (R := R) σ z ∈ LinearMap.ker D := fun σ z hz => by
    rw [LinearMap.mem_ker] at hz ⊢
    rw [hD, d.app_map, ← hD, hz, map_zero]
  have hZp : ∀ (b : Bool), ∀ z ∈ LinearMap.ker D, GrSpecies.par (R := R) b z ∈ LinearMap.ker D :=
    fun b z hz => by
      rw [LinearMap.mem_ker] at hz ⊢
      rw [hD, d.app_par, ← hD, hz, map_zero]
  have hBm : ∀ (σ : Equiv.Perm (Fin n)), ∀ w ∈ LinearMap.range D,
      SymSpecies.map (R := R) σ w ∈ LinearMap.range D := fun σ w hw => by
    obtain ⟨x, rfl⟩ := hw
    exact ⟨_, d.app_map σ x⟩
  have hBp : ∀ (b : Bool), ∀ w ∈ LinearMap.range D,
      GrSpecies.par (R := R) b w ∈ LinearMap.range D :=
    fun b w hw => by
      obtain ⟨x, rfl⟩ := hw
      refine ⟨GrSpecies.par (R := R) (!b) x, ?_⟩
      rw [hD, d.app_par]
      cases b <;> rfl
  have hBZ : ∀ w ∈ LinearMap.range D, D w = 0 := fun w hw => by
    obtain ⟨x, rfl⟩ := hw
    exact hdd _ x
  obtain ⟨πZ, hZ1, hZ2, hZ3, hZ4⟩ := exists_proj (LinearMap.ker D) hZm hZp
  obtain ⟨πB, hB1, hB2, hB3, hB4⟩ := exists_proj (LinearMap.range D) hBm hBp
  have hDZ : ∀ x, D (πZ x) = 0 := fun x => hZ1 x
  set K := LinearMap.ker πZ
  have injK : ∀ k₁ ∈ K, ∀ k₂ ∈ K, D k₁ = D k₂ → k₁ = k₂ := fun k₁ h₁ k₂ h₂ he => by
    have hz : k₁ - k₂ ∈ LinearMap.ker D := by rw [LinearMap.mem_ker, map_sub, he, sub_self]
    have := hZ2 _ hz
    rw [map_sub, LinearMap.mem_ker.1 h₁, LinearMap.mem_ker.1 h₂, sub_self] at this
    exact sub_eq_zero.1 this.symm
  have hsubK : ∀ x, x - πZ x ∈ K := fun x => by
    rw [LinearMap.mem_ker, map_sub, hZ2 _ (hZ1 x), sub_self]
  let dK : K →ₗ[R] LinearMap.range D :=
    LinearMap.codRestrict (LinearMap.range D) (D ∘ₗ K.subtype) fun k => LinearMap.mem_range_self D k
  have hdK : Function.Bijective dK := by
    refine ⟨fun k₁ k₂ he => Subtype.ext (injK _ k₁.2 _ k₂.2 (congrArg Subtype.val he)), ?_⟩
    rintro ⟨w, x, rfl⟩
    refine ⟨⟨x - πZ x, hsubK x⟩, Subtype.ext ?_⟩
    show D (x - πZ x) = D x
    rw [map_sub, hDZ, sub_zero]
  let eK := LinearEquiv.ofBijective dK hdK
  let h : V (Fin n) →ₗ[R] V (Fin n) := K.subtype ∘ₗ eK.symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range D) (πB ∘ₗ πZ) fun x => hB1 _
  have hh1 : ∀ x, h x ∈ K := fun x => (eK.symm _).2
  have hh2 : ∀ x, D (h x) = πB (πZ x) := fun x => by
    have := congrArg Subtype.val (eK.apply_symm_apply
      (LinearMap.codRestrict (LinearMap.range D) (πB ∘ₗ πZ) (fun x => hB1 _) x))
    exact this
  have hKm : ∀ (σ : Equiv.Perm (Fin n)), ∀ k ∈ K, SymSpecies.map (R := R) σ k ∈ K :=
    fun σ k hk => by rw [LinearMap.mem_ker, hZ3, LinearMap.mem_ker.1 hk, map_zero]
  have hKp : ∀ (b : Bool), ∀ k ∈ K, GrSpecies.par (R := R) b k ∈ K :=
    fun b k hk => by rw [LinearMap.mem_ker, hZ4, LinearMap.mem_ker.1 hk, map_zero]
  refine ⟨πZ - πB ∘ₗ πZ, h, fun σ x => ?_, fun σ x => ?_, fun c x => ?_, fun c x => ?_,
    fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · simp only [LinearMap.sub_apply, LinearMap.comp_apply, hZ3, hB3, map_sub]
  · refine injK _ (hh1 _) _ (hKm σ _ (hh1 x)) ?_
    rw [hh2, hD, d.app_map, ← hD, hh2, hZ3, hB3]
  · simp only [LinearMap.sub_apply, LinearMap.comp_apply, hZ4, hB4, map_sub, Bool.xor_false]
  · refine injK _ (hh1 _) _ (hKp _ _ (hh1 x)) ?_
    rw [hh2, hD, d.app_par, ← hD, hh2, hZ4, hB4]
    cases c <;> rfl
  · have hpZ : πZ x - πB (πZ x) ∈ LinearMap.ker D :=
      Submodule.sub_mem _ (hZ1 x) (hBZ _ (hB1 _))
    simp only [LinearMap.sub_apply, LinearMap.comp_apply]
    rw [hZ2 _ hpZ, map_sub, hB2 _ (hB1 _), sub_self, sub_zero]
  · simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
    rw [hDZ, hBZ _ (hB1 _), sub_self]
  · simp only [LinearMap.sub_apply, LinearMap.comp_apply]
    rw [hZ2 _ (hBZ _ (LinearMap.mem_range_self D x)), hB2 _ (LinearMap.mem_range_self D x),
      sub_self]
  · have e1 : h (D x) = x - πZ x := injK _ (hh1 _) _ (hsubK x) (by
      rw [hh2, hZ2 _ (hBZ _ (LinearMap.mem_range_self D x)), hB2 _ (LinearMap.mem_range_self D x),
        map_sub, hDZ, sub_zero])
    rw [hh2, e1, LinearMap.sub_apply, LinearMap.comp_apply]
    abel

/-- **Over a field of characteristic zero, every odd endomorphism of square zero of a graded
linear species has a splitting.** -/
theorem Splitting.exists_of_field : Nonempty (Splitting d) := by
  choose p h hpm hhm hpp hhp hpp' hdp hpd hdh using exists_level_splitting d hdd
  let P := GrSpEnd.extend p hpm hpp
  let H := GrSpEnd.extend h hhm hhp
  have cP : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : V A), P.app A x
      = SymSpecies.map (R := R) (Fintype.equivFin A).symm
        (p _ (SymSpecies.map (R := R) (Fintype.equivFin A).symm.symm x)) :=
    fun A _ _ x => GrSpEnd.extend_app_chart _ x
  have cH : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : V A), H.app A x
      = SymSpecies.map (R := R) (Fintype.equivFin A).symm
        (h _ (SymSpecies.map (R := R) (Fintype.equivFin A).symm.symm x)) :=
    fun A _ _ x => GrSpEnd.extend_app_chart _ x
  have cD : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : V A), d.app A x
      = SymSpecies.map (R := R) (Fintype.equivFin A).symm
        (d.app _ (SymSpecies.map (R := R) (Fintype.equivFin A).symm.symm x)) :=
    fun A _ _ x => d.app_chart _ x
  refine ⟨⟨P, H, fun A _ _ x => ?_, fun A _ _ x => ?_, fun A _ _ x => ?_, fun A _ _ x => ?_⟩⟩
  · rw [cP, cP, GrSpEnd.map_symm_map', hpp']
  · rw [cD, cP, GrSpEnd.map_symm_map', hdp, map_zero]
  · rw [cP, cD, GrSpEnd.map_symm_map', hpd, map_zero]
  · have e1 : d.app A (H.app A x) = SymSpecies.map (R := R) (Fintype.equivFin A).symm
        (d.app _ (h _ (SymSpecies.map (R := R) (Fintype.equivFin A).symm.symm x))) := by
      rw [cH, cD, GrSpEnd.map_symm_map']
    have e2 : H.app A (d.app A x) = SymSpecies.map (R := R) (Fintype.equivFin A).symm
        (h _ (d.app _ (SymSpecies.map (R := R) (Fintype.equivFin A).symm.symm x))) := by
      rw [cD, cH, GrSpEnd.map_symm_map']
    rw [e1, e2, cP, ← map_add, hdh, map_sub, GrSpEnd.map_map_symm']

end Split


/-! ## Splittings compatible with a quasi-isomorphism -/

section Compat

variable {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)] [GrSpecies R W]
  {dV : GrSpEnd R V true} {dW : GrSpEnd R W true} (f : GrSpeciesHom R V W)
  (hf : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : V A),
    dW.app A (f.app A x) = f.app A (dV.app A x))
  (s : Splitting dV) (s' : Splitting dW)

include hf in
/-- **On a standard finite type where `f` is a quasi-isomorphism, `p' f` is invertible from the
image of `p` onto the image of `p'`.** -/
theorem exists_level_inv (n : ℕ)
    (hsurj : ∀ y : W (Fin n), dW.app _ y = 0 →
      ∃ x, dV.app _ x = 0 ∧ ∃ w', f.app _ x - y = dW.app _ w')
    (hinj : ∀ x : V (Fin n), dV.app _ x = 0 → ∀ w', f.app _ x = dW.app _ w' →
      ∃ z, dV.app _ z = x) :
    ∃ k : W (Fin n) →ₗ[R] V (Fin n),
      (∀ (σ : Equiv.Perm (Fin n)) (y : W (Fin n)),
        k (SymSpecies.map (R := R) σ y) = SymSpecies.map (R := R) σ (k y)) ∧
      (∀ (c : Bool) (y : W (Fin n)),
        k (GrSpecies.par (R := R) c y) = GrSpecies.par (R := R) c (k y)) ∧
      (∀ x, k (s'.p.app _ (f.app _ (s.p.app _ x))) = s.p.app _ x) ∧
      (∀ y, s'.p.app _ (f.app _ (s.p.app _ (k y))) = s'.p.app _ y) := by
  set p := s.p.app (Fin n) with hp
  set p' := s'.p.app (Fin n) with hp'
  set H := LinearMap.range p
  set H' := LinearMap.range p'
  have hH : ∀ x ∈ H, p x = x := fun x hx => by
    obtain ⟨y, rfl⟩ := hx
    exact s.pp _ y
  -- a cycle of `W` differs from its projection by a boundary
  have hcyc' : ∀ y : W (Fin n), dW.app _ y = 0 → y - p' y = dW.app _ (s'.h.app _ y) := by
    intro y hy
    have := s'.dh _ y
    rw [hy, map_zero, add_zero] at this
    exact this.symm
  let φ : H →ₗ[R] H' := LinearMap.codRestrict H' (p' ∘ₗ f.app (Fin n) ∘ₗ H.subtype)
    fun x => LinearMap.mem_range_self p' _
  have hφ : Function.Bijective φ := by
    constructor
    · intro x₁ x₂ he
      have he' : p' (f.app _ (x₁.1 - x₂.1)) = 0 := by
        rw [map_sub, map_sub]
        exact sub_eq_zero.2 (congrArg Subtype.val he)
      have hx : x₁.1 - x₂.1 ∈ H := H.sub_mem x₁.2 x₂.2
      have hcy : dV.app _ (x₁.1 - x₂.1) = 0 := by rw [← hH _ hx]; exact s.dp _ _
      have hfcy : dW.app _ (f.app _ (x₁.1 - x₂.1)) = 0 := by rw [hf, hcy, map_zero]
      obtain ⟨z, hz⟩ := hinj _ hcy _ (by have := hcyc' _ hfcy; rwa [he', sub_zero] at this)
      have h0 : x₁.1 - x₂.1 = 0 := by rw [← hH _ hx, ← hz]; exact s.pd _ z
      exact Subtype.ext (sub_eq_zero.1 h0)
    · rintro ⟨y, y₀, rfl⟩
      have hcy : dW.app _ (p' y₀) = 0 := s'.dp _ y₀
      obtain ⟨x, hx, w', hxw⟩ := hsurj _ hcy
      refine ⟨⟨p x, LinearMap.mem_range_self p x⟩, Subtype.ext ?_⟩
      show p' (f.app _ (p x)) = p' y₀
      have e1 : x - p x = dV.app _ (s.h.app _ x) := by
        have := s.dh _ x
        rw [hx, map_zero, add_zero] at this
        exact this.symm
      have e2 : p x = x - dV.app _ (s.h.app _ x) := by rw [← e1]; abel
      rw [e2, map_sub, map_sub, ← hf, s'.pd, sub_zero, sub_eq_iff_eq_add.1 hxw, map_add, s'.pd,
        zero_add, s'.pp]
  let e := LinearEquiv.ofBijective φ hφ
  let k : W (Fin n) →ₗ[R] V (Fin n) := H.subtype ∘ₗ e.symm.toLinearMap ∘ₗ
    LinearMap.codRestrict H' p' fun y => LinearMap.mem_range_self p' y
  have hk1 : ∀ y, k y ∈ H := fun y => (e.symm _).2
  have hk2 : ∀ y, p' (f.app _ (k y)) = p' y := fun y =>
    congrArg Subtype.val (e.apply_symm_apply (LinearMap.codRestrict H' p'
      (fun y => LinearMap.mem_range_self p' y) y))
  have hinjφ : ∀ x₁ ∈ H, ∀ x₂ ∈ H, p' (f.app _ x₁) = p' (f.app _ x₂) → x₁ = x₂ :=
    fun x₁ h₁ x₂ h₂ he => congrArg Subtype.val (hφ.1 (a₁ := ⟨x₁, h₁⟩) (a₂ := ⟨x₂, h₂⟩)
      (Subtype.ext he))
  have hHm : ∀ (σ : Equiv.Perm (Fin n)), ∀ x ∈ H, SymSpecies.map (R := R) σ x ∈ H :=
    fun σ x hx => ⟨SymSpecies.map (R := R) σ x, by rw [hp, s.p.app_map, ← hp, hH x hx]⟩
  have hHp : ∀ (c : Bool), ∀ x ∈ H, GrSpecies.par (R := R) c x ∈ H :=
    fun c x hx => ⟨GrSpecies.par (R := R) c x, by
      rw [hp, s.p.app_par, Bool.xor_false, ← hp, hH x hx]⟩
  refine ⟨k, fun σ y => ?_, fun c y => ?_, fun x => ?_, fun y => ?_⟩
  · refine hinjφ _ (hk1 _) _ (hHm σ _ (hk1 y)) ?_
    rw [hk2, f.app_map, hp']
    simp only [s'.p.app_map]
    rw [← hp', hk2]
  · refine hinjφ _ (hk1 _) _ (hHp c _ (hk1 y)) ?_
    rw [hk2, f.app_par, hp']
    simp only [s'.p.app_par]
    rw [← hp', hk2]
  · exact hinjφ _ (hk1 _) _ (LinearMap.mem_range_self p x) (by rw [hk2, s'.pp])
  · rw [hH _ (hk1 y), hk2]

include hf in
/-- **A morphism inverting `p' f p` on the arities where `f` is a quasi-isomorphism.** -/
theorem exists_compat (S : ℕ → Prop) [DecidablePred S]
    (hsurj : ∀ n, S n → ∀ y : W (Fin n), dW.app _ y = 0 →
      ∃ x, dV.app _ x = 0 ∧ ∃ w', f.app _ x - y = dW.app _ w')
    (hinj : ∀ n, S n → ∀ x : V (Fin n), dV.app _ x = 0 → ∀ w', f.app _ x = dW.app _ w' →
      ∃ z, dV.app _ z = x) :
    ∃ k : GrSpeciesHom R W V, ∀ (A : Type) [Fintype A] [DecidableEq A], S (Fintype.card A) →
      (∀ x, k.app A (s'.p.app A (f.app A (s.p.app A x))) = s.p.app A x) ∧
      (∀ y, s'.p.app A (f.app A (s.p.app A (k.app A y))) = s'.p.app A y) := by
  have hex : ∀ n, ∃ k : W (Fin n) →ₗ[R] V (Fin n),
      (∀ (σ : Equiv.Perm (Fin n)) (y : W (Fin n)),
        k (SymSpecies.map (R := R) σ y) = SymSpecies.map (R := R) σ (k y)) ∧
      (∀ (c : Bool) (y : W (Fin n)),
        k (GrSpecies.par (R := R) c y) = GrSpecies.par (R := R) c (k y)) ∧
      (S n → (∀ x, k (s'.p.app _ (f.app _ (s.p.app _ x))) = s.p.app _ x) ∧
        (∀ y, s'.p.app _ (f.app _ (s.p.app _ (k y))) = s'.p.app _ y)) := fun n => by
    by_cases hn : S n
    · obtain ⟨k, h1, h2, h3, h4⟩ := exists_level_inv f hf s s' n (hsurj n hn) (hinj n hn)
      exact ⟨k, h1, h2, fun _ => ⟨h3, h4⟩⟩
    · exact ⟨0, fun _ _ => by simp, fun _ _ => by simp, fun h => absurd h hn⟩
  choose k hk1 hk2 hk3 using hex
  refine ⟨GrSpeciesHom.extend k ⟨hk1, hk2⟩, fun A _ _ hA => ?_⟩
  set φ := (Fintype.equivFin A).symm
  have cK : ∀ y : W A, (GrSpeciesHom.extend k ⟨hk1, hk2⟩).app A y
      = SymSpecies.map (R := R) φ (k _ (SymSpecies.map (R := R) φ.symm y)) := fun y =>
    GrSpeciesHom.extendApp_chart ⟨hk1, hk2⟩ φ y
  obtain ⟨h3, h4⟩ := hk3 _ hA
  constructor
  · intro x
    rw [s.p.app_chart φ, f.app_eq_chart φ, s'.p.app_chart φ, cK, GrSpEnd.map_symm_map',
      GrSpEnd.map_symm_map', GrSpEnd.map_symm_map', h3]
  · intro y
    rw [cK, s.p.app_chart φ, GrSpEnd.map_symm_map', f.app_eq_chart φ, GrSpEnd.map_symm_map',
      s'.p.app_chart φ, GrSpEnd.map_symm_map', h4, ← s'.p.app_chart φ]

end Compat

end Operad
