/-
# Retractions of injective morphisms of graded linear species

Over a field of characteristic zero, the image of a morphism of graded linear species is the
image of an even endomorphism of the target fixing it (`GrSpeciesHom.exists_proj_range`): on the
standard finite types by the equivariant projections of `Operad.SpSplitting` (`exists_proj`),
extended through numberings (`GrSpEnd.extend`). So **an injective morphism of graded linear
species has a retraction** (`GrSpeciesHom.exists_retraction`), commuting with the relabellings
and the parities.
-/
import Operad.SpSplitting

universe u v w

namespace Operad

open Sym GerBV

variable {R : Type u} [Field R] [CharZero R]
  {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)] [GrSpecies R W]

namespace GrSpeciesHom

/-- **An equivariant projection onto the image of a morphism of graded linear species**, over a
field of characteristic zero: an even endomorphism of the target with values in the image, fixing
it. -/
theorem exists_proj_range (f : GrSpeciesHom R V W) :
    ∃ p : GrSpEnd R W false,
      (∀ (A : Type) [Fintype A] [DecidableEq A] (w : W A),
        p.app A w ∈ LinearMap.range (f.app A)) ∧
      (∀ (A : Type) [Fintype A] [DecidableEq A] (v : V A), p.app A (f.app A v) = f.app A v) := by
  have hWm : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)), ∀ w ∈ LinearMap.range (f.app (Fin n)),
      SymSpecies.map (R := R) σ w ∈ LinearMap.range (f.app (Fin n)) := by
    rintro n σ _ ⟨v, rfl⟩
    exact ⟨SymSpecies.map (R := R) σ v, f.app_map σ v⟩
  have hWp : ∀ (n : ℕ) (b : Bool), ∀ w ∈ LinearMap.range (f.app (Fin n)),
      GrSpecies.par (R := R) b w ∈ LinearMap.range (f.app (Fin n)) := by
    rintro n b _ ⟨v, rfl⟩
    exact ⟨GrSpecies.par (R := R) b v, f.app_par b v⟩
  choose π hπ1 hπ2 hπ3 hπ4 using fun n : ℕ =>
    exists_proj (LinearMap.range (f.app (Fin n))) (hWm n) (hWp n)
  have hp : ∀ (n : ℕ) (c : Bool) (x : W (Fin n)),
      π n (GrSpecies.par (R := R) c x) = GrSpecies.par (R := R) (xor c false) (π n x) :=
    fun n c x => by
      rw [Bool.xor_false]
      exact hπ4 n c x
  refine ⟨GrSpEnd.extend π hπ3 hp, fun A _ _ w => ?_, fun A _ _ v => ?_⟩
  · rw [GrSpEnd.extend_app_chart (Fintype.equivFin A).symm w]
    obtain ⟨v, hv⟩ := hπ1 _ (SymSpecies.map (R := R) (Fintype.equivFin A).symm.symm w)
    exact ⟨SymSpecies.map (R := R) (Fintype.equivFin A).symm v, by rw [f.app_map, hv]⟩
  · rw [GrSpEnd.extend_app_chart (Fintype.equivFin A).symm, ← f.app_map,
      hπ2 _ _ ⟨_, rfl⟩, f.app_map, GrSpEnd.map_map_symm']

/-- **An injective morphism of graded linear species has a retraction**, over a field of
characteristic zero. -/
theorem exists_retraction (f : GrSpeciesHom R V W)
    (hf : ∀ (A : Type) [Fintype A] [DecidableEq A], Function.Injective (f.app A)) :
    ∃ g : GrSpeciesHom R W V,
      ∀ (A : Type) [Fintype A] [DecidableEq A] (v : V A), g.app A (f.app A v) = v := by
  obtain ⟨p, hp1, hp2⟩ := exists_proj_range f
  have key : ∀ (A : Type) [Fintype A] [DecidableEq A] (w : W A),
      f.app A ((LinearEquiv.ofInjective (f.app A) (hf A)).symm ⟨p.app A w, hp1 A w⟩)
        = p.app A w := fun A _ _ w =>
    congrArg Subtype.val
      ((LinearEquiv.ofInjective (f.app A) (hf A)).apply_symm_apply ⟨p.app A w, hp1 A w⟩)
  let g : ∀ (A : Type) [Fintype A] [DecidableEq A], W A →ₗ[R] V A := fun A _ _ =>
    ((LinearEquiv.ofInjective (f.app A) (hf A)).symm :
      LinearMap.range (f.app A) →ₗ[R] V A) ∘ₗ
      (p.app A).codRestrict (LinearMap.range (f.app A)) (hp1 A)
  have hg : ∀ (A : Type) [Fintype A] [DecidableEq A] (w : W A),
      f.app A (g A w) = p.app A w := fun A _ _ w => key A w
  have hmap : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
      (e : A ≃ B) (w : W A),
      g B (SymSpecies.map (R := R) e w) = SymSpecies.map (R := R) e (g A w) := by
    intro A B _ _ _ _ e w
    apply hf B
    exact (hg B _).trans ((p.app_map e w).trans
      ((congrArg (SymSpecies.map (R := R) e) (hg A w)).symm.trans (f.app_map e _).symm))
  have hpar : ∀ {A : Type} [Fintype A] [DecidableEq A] (b : Bool) (w : W A),
      g A (GrSpecies.par (R := R) b w) = GrSpecies.par (R := R) b (g A w) := by
    intro A _ _ b w
    apply hf A
    refine (hg A _).trans ((p.app_par b w).trans ?_)
    rw [Bool.xor_false]
    exact (congrArg (GrSpecies.par (R := R) b) (hg A w)).symm.trans (f.app_par b _).symm
  refine ⟨⟨⟨g, hmap⟩, hpar⟩, fun A _ _ v => ?_⟩
  apply hf A
  exact (hg A _).trans (hp2 A v)

end GrSpeciesHom

end Operad
