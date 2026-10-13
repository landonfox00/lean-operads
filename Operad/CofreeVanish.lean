/-
# Cogenerated elements of the cut cooperad

For the cut cooperad `C = T^c(V)` on a graded linear species without generators without inputs,
over a `ℚ`-algebra, the weight derivation of the cobar construction `ΩC` relates the convolution
square `ι ⋆ ι` of the universal twisting morphism to the number of vertices: by the contraction
identity `d h + h d = E - (1 - ε)` (`Cobar.dh_hd`) on a generator `ι y`, with `h (ι y) = 0` and
`d (ι y) = -(ι ⋆ ι)(y)`, **`h ((ι ⋆ ι)(y)) = -(n - 1) ι y` for `y` with `n` vertices**.

So **an element with at least `k ≥ 2` vertices whose convolution square has weight at least `k + 1`
has at least `k + 1` vertices** (`Cobar.mem_vxGe_succ`): its part with `k` vertices has a
convolution square of weight `k` and at least `k + 1`, which vanishes, so it is a multiple of the
units, which have no vertices. This is the uniqueness part of the universal property of the cut
cooperad, cofree among the conilpotent cooperads.
-/
import Operad.FreeGrCompare
import Operad.BarCobarRes

universe u v

namespace Operad

open Sym GerBV FreeGrL

namespace Cobar

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {A : Type} [Fintype A] [DecidableEq A]

local notation "𝒞" => FreeGrL R V

/-- The weight derivation counts the vertices. -/
lemma wtD_eq_derSp : FreeGrL.wtD R V = derSp (GrSpEnd.id R V) :=
  der_ext fun A _ _ v => by rw [wtD_ι, derSp_ι, GrSpEnd.id_app]

/-- The generator of a tree with `j` vertices has weight `j`. -/
lemma ιL_mem_wt {j : ℕ} {y : 𝒞 A} (hy : y ∈ vx R V j A) : ιL R 𝒞 A y ∈ wt R V j A :=
  mem_wt.2 (by rw [wtΩ_ιL, wtD_eq_derSp, mem_eig.1 hy, map_smul])

/-- **The convolution square `ι ⋆ ι` preserves the weights.** -/
lemma ιι_mem_wt (hV0 : ∀ v : V (Fin 0), v = 0) {j : ℕ} {y : 𝒞 A} (hy : y ∈ vx R V j A) :
    ConvOp.toLin ((ιι R 𝒞).1 A) y ∈ wt R V j A := by
  have h := d_mem_wt hV0 (ιL_mem_wt hy)
  rw [d_ιL] at h
  simpa using neg_mem h

lemma ιι_mem_iSup_wt (hV0 : ∀ v : V (Fin 0), v = 0) {k : ℕ} {y : 𝒞 A} (hy : y ∈ vxGe R V k A) :
    ConvOp.toLin ((ιι R 𝒞).1 A) y ∈ ⨆ j : {j : ℕ // k ≤ j}, wt R V j.1 A :=
  (iSup_le (fun j _ hz => Submodule.mem_iSup_of_mem j (ιι_mem_wt hV0 hz)) :
    vxGe R V k A ≤ (⨆ j : {j : ℕ // k ≤ j}, wt R V j.1 A).comap
      (ConvOp.toLin ((ιι R 𝒞).1 A))) hy

/-- The units have no vertices. -/
lemma unitSpan_le_vx : GrCooperad.unitSpan R 𝒞 A ≤ vx R V 0 A :=
  Submodule.span_le.2 (by
    rintro _ ⟨e, rfl⟩
    show SymSpecies.map (R := R) e _ ∈ vx R V 0 A
    rw [symMap_eq]
    exact unit_mem_eig e)

/-- The cobar differential of a generator of a tree with `j` vertices has weight `j`. -/
lemma d_ιL_mem_wt (hV0 : ∀ v : V (Fin 0), v = 0) {j : ℕ} {y : 𝒞 A} (hy : y ∈ vx R V j A) :
    (d R 𝒞).app A (ιL R 𝒞 A y) ∈ wt R V j A :=
  d_mem_wt hV0 (ιL_mem_wt hy)

lemma d_ιL_mem_iSup_wt (hV0 : ∀ v : V (Fin 0), v = 0) {k : ℕ} {y : 𝒞 A}
    (hy : y ∈ vxGe R V k A) :
    (d R 𝒞).app A (ιL R 𝒞 A y) ∈ ⨆ j : {j : ℕ // k ≤ j}, wt R V j.1 A :=
  (iSup_le (fun j _ hz => Submodule.mem_iSup_of_mem j (d_ιL_mem_wt hV0 hz)) :
    vxGe R V k A ≤ (⨆ j : {j : ℕ // k ≤ j}, wt R V j.1 A).comap
      ((d R 𝒞).app A ∘ₗ ιL R 𝒞 A)) hy

lemma d_ιL_mem_of_ιι {S : Submodule R (CobarGr R 𝒞 A)} {y : 𝒞 A}
    (hy : ConvOp.toLin ((ιι R 𝒞).1 A) y ∈ S) : (d R 𝒞).app A (ιL R 𝒞 A y) ∈ S := by
  rw [d_ιL]
  exact neg_mem hy

/-- **A generator with `k ≥ 2` vertices killed by the cobar differential vanishes**, by the
contraction identity. -/
lemma eq_zero_of_d_ιL [Algebra ℚ R] (hV0 : ∀ v : V (Fin 0), v = 0) {k : ℕ} (hk : 2 ≤ k)
    {z : 𝒞 A} (hz : z ∈ vx R V k A) (h0 : (d R 𝒞).app A (ιL R 𝒞 A z) = 0) :
    ιL R 𝒞 A z = 0 := by
  have h2 := dh_hd hV0 (ιL R 𝒞 A z)
  have hl : (d R 𝒞).app A (hM R V A (ιL R 𝒞 A z)) + hM R V A ((d R 𝒞).app A (ιL R 𝒞 A z))
      = 0 :=
    (congrArg₂ (· + ·) ((congrArg _ (hM_ιL z)).trans (map_zero _))
      ((congrArg _ h0).trans (map_zero _))).trans (add_zero 0)
  have eE : (wtΩ R V).app A (ιL R 𝒞 A z) = (k : R) • ιL R 𝒞 A z :=
    (wtΩ_ιL z).trans ((congrArg (ιL R 𝒞 A) (by rw [wtD_eq_derSp]; exact mem_eig.1 hz)).trans
      (map_smul _ _ _))
  have eS : FreeGrL.secC R (CobarGen R 𝒞) A (ιL R 𝒞 A z) = ιL R 𝒞 A z :=
    FreeGrL.secC_of_unitCoeff (unitCoeffL_ιL z)
  have e : ((k - 1 : ℕ) : R) • ιL R 𝒞 A z = 0 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    exact ((sub_smul (k : R) 1 _).trans (congrArg (_ - ·) (one_smul R _))).trans
      ((congrArg₂ (· - ·) eE.symm eS.symm).trans (h2.symm.trans hl))
  exact (isUnit_natCast_of_ne_zero (show k - 1 ≠ 0 by omega)).smul_left_cancel.1
    (e.trans (smul_zero _).symm)

/-- **An element with `k ≥ 1` vertices whose generator vanishes vanishes.** -/
lemma eq_zero_of_ιL [Algebra ℚ R] {k : ℕ} (hk : 1 ≤ k) {z : 𝒞 A} (hz : z ∈ vx R V k A)
    (h3 : ιL R 𝒞 A z = 0) : z = 0 := by
  rw [ιL_apply, ← map_zero ((FreeGrL.ι R (CobarGen R 𝒞)).app A)] at h3
  have h4 : z ∈ GrCooperad.unitSpan R 𝒞 A :=
    (Submodule.Quotient.mk_eq_zero _).1 (FreeGrL.ι_injective h3)
  have hle' : vx R V 0 A ≤ ⨆ (i : ℕ) (_ : i ≠ k), vx R V i A :=
    le_iSup₂_of_le (f := fun (i : ℕ) (_ : i ≠ k) => vx R V i A) 0 (by omega) le_rfl
  exact Submodule.disjoint_def.1
    (iSupIndep_eigenspace_nat ((derSp (GrSpEnd.id R V)).app A) k) _ hz
    (hle' (unitSpan_le_vx h4))

/-- **An element with at least `k ≥ 2` vertices whose convolution square has weight at least
`k + 1` has at least `k + 1` vertices.** -/
theorem mem_vxGe_succ [Algebra ℚ R] (hV0 : ∀ v : V (Fin 0), v = 0) {k : ℕ} (hk : 2 ≤ k)
    {y : 𝒞 A} (hy : y ∈ vxGe R V k A)
    (hyy : ConvOp.toLin ((ιι R 𝒞).1 A) y ∈ ⨆ j : {j : ℕ // k + 1 ≤ j}, wt R V j.1 A) :
    y ∈ vxGe R V (k + 1) A := by
  have hd := d_ιL_mem_of_ιι hyy
  rw [vxGe_eq k] at hy
  obtain ⟨z, hz, y', hy', rfl⟩ := Submodule.mem_sup.1 hy
  -- the cobar differential of the generator of the part with `k` vertices vanishes
  rw [(ιL R 𝒞 A).map_add, ((d R 𝒞).app A).map_add] at hd
  have h1 := (Submodule.add_mem_iff_left _ (d_ιL_mem_iSup_wt hV0 hy')).1 hd
  have hle : (⨆ j : {j : ℕ // k + 1 ≤ j}, wt R V j.1 A) ≤ ⨆ (i : ℕ) (_ : i ≠ k), wt R V i A :=
    iSup_le fun j => le_iSup₂_of_le (f := fun (i : ℕ) (_ : i ≠ k) => wt R V i A) j.1
      (by have := j.2; omega) le_rfl
  have h0 : (d R 𝒞).app A (ιL R 𝒞 A z) = 0 :=
    Submodule.disjoint_def.1 (iSupIndep_eigenspace_nat ((wtΩ R V).app A) k) _
      (d_ιL_mem_wt hV0 hz) (hle h1)
  rw [eq_zero_of_ιL (by omega) hz (eq_zero_of_d_ιL hV0 hk hz h0), zero_add]
  exact hy'

end Cobar

end Operad
