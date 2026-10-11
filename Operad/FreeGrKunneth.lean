/-
# The homology of a free graded operad with a differential on the generators

Let `d` be an odd endomorphism of a graded linear species `V` and `δ` the derivation of the free
graded operad `T(V)` extending it. **A splitting** of `d` (`Splitting`) is an even idempotent `p`,
the projection onto a complement of the boundaries in the cycles, with an odd homotopy `h`:
`d h + h d = 1 - p` and `d p = p d = 0`.

**The derivation trick.** The derivations `D_h` and `N` extending `h` and `1 - p` satisfy
`δ D_h + D_h δ = N`, and `N` counts the vertices decorated outside the image of `p`. Over a
`ℚ`-algebra, `N` is diagonalizable, so a `δ`-cycle with no component of eigenvalue zero is a
`δ`-boundary: on the eigenspace for `j ≥ 1`, `δ (D_h / j) + (D_h / j) δ = 1`
(`exists_eq_of_contract`). The eigenvalue zero part is the image of the projection `T(p)`, on
which `δ` vanishes: **`T(p)` is a retraction of `T(V)` onto `T(im p)` with acyclic kernel**
(`Splitting.retract`), compatibly with the eigenspaces of any derivation extending an even
endomorphism commuting with `d`, `p` and `h`.
-/
import Operad.FreeGrDer
import Operad.QIsoLemmas

universe u v

namespace Operad

open Sym GerBV

/-! ## A contraction on the positive eigenspaces -/

section Contract

variable {R : Type u} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- Components in an independent family of submodules of a vanishing finite sum vanish. -/
lemma iSupIndep_finsupp_eq_zero {p : ℕ → Submodule R M} (hp : iSupIndep p) (f : ℕ →₀ M)
    (hf : ∀ j, f j ∈ p j) (hs : f.sum (fun _ v => v) = 0) (j : ℕ) : f j = 0 := by
  classical
  by_cases hj : j ∈ f.support
  · exact ((iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero p).1 hp) f.support f
      (fun i _ => hf i) hs j hj
  · exact Finsupp.notMem_support_iff.1 hj

/-- **A contraction on the positive eigenspaces**: if `δ D + D δ = N`, with `δ` commuting with
`N`, and `N` and `D` with an endomorphism `Nv`, a `δ`-cycle in the sum of the eigenspaces of `N`
for the positive integers is a `δ`-boundary, of an element of the same eigenvalue for `Nv`, over
a `ℚ`-algebra. -/
theorem exists_eq_of_contract [Algebra ℚ R] (N δ D Nv : M →ₗ[R] M) (k : R)
    (hNδ : ∀ x, N (δ x) = δ (N x))
    (hNNv : ∀ x, N (Nv x) = Nv (N x)) (hNvD : ∀ x, Nv (D x) = D (Nv x))
    (hc : ∀ x, δ (D x) + D (δ x) = N x) {x : M}
    (hx : x ∈ ⨆ j : ℕ, Module.End.eigenspace N ((j + 1 : ℕ) : R)) (hδx : δ x = 0)
    (hNv : Nv x = k • x) : ∃ z, Nv z = k • z ∧ δ z = x := by
  have hind : iSupIndep fun j : ℕ => Module.End.eigenspace N ((j + 1 : ℕ) : R) :=
    iSupIndep.comp (t := fun j : ℕ => Module.End.eigenspace N (j : R))
      (iSupIndep_eigenspace_nat N) (f := fun j => j + 1) (fun a b h => Nat.succ_injective h)
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ x).1 hx
  have hmem : ∀ (φ : M →ₗ[R] M), (∀ y, N (φ y) = φ (N y)) → ∀ j,
      φ (f j) ∈ Module.End.eigenspace N ((j + 1 : ℕ) : R) := fun φ hφ j => by
    rw [Module.End.mem_eigenspace_iff, hφ, Module.End.mem_eigenspace_iff.1 (hf j), map_smul]
  -- the components are `δ`-cycles and eigenvectors of `Nv`
  have hδf : ∀ j, δ (f j) = 0 := iSupIndep_finsupp_eq_zero hind (f.mapRange δ (map_zero δ))
    (fun j => by rw [Finsupp.mapRange_apply]; exact hmem δ hNδ j)
    (by rw [Finsupp.sum_mapRange_index (fun _ => rfl), ← map_finsuppSum]; exact hδx)
  let φ : M →ₗ[R] M := Nv - k • LinearMap.id
  have hφ : ∀ y, N (φ y) = φ (N y) := fun y => by
    simp only [φ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub,
      map_smul, hNNv]
  have hNvf : ∀ j, Nv (f j) = k • f j := fun j => by
    have h := iSupIndep_finsupp_eq_zero hind (f.mapRange φ (map_zero φ))
      (fun j => by rw [Finsupp.mapRange_apply]; exact hmem φ hφ j)
      (by
        rw [Finsupp.sum_mapRange_index (fun _ => rfl), ← map_finsuppSum]
        simp only [φ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hNv,
          sub_self]) j
    rw [Finsupp.mapRange_apply] at h
    simpa only [φ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] using h
  let c : ℕ → R := fun j => algebraMap ℚ R ((j + 1 : ℕ) : ℚ)⁻¹
  have hc1 : ∀ j, c j * ((j + 1 : ℕ) : R) = 1 := fun j => by
    rw [show ((j + 1 : ℕ) : R) = algebraMap ℚ R ((j + 1 : ℕ) : ℚ) from (map_natCast _ _).symm,
      ← map_mul, inv_mul_cancel₀ (by positivity), map_one]
  refine ⟨f.sum fun j v => c j • D v, ?_, ?_⟩
  · rw [map_finsuppSum, Finsupp.smul_sum]
    refine Finsupp.sum_congr fun j _ => ?_
    rw [map_smul, hNvD, hNvf, map_smul, smul_comm]
  · rw [map_finsuppSum]
    refine Finsupp.sum_congr fun j _ => ?_
    have := hc (f j)
    rw [hδf, map_zero, add_zero, Module.End.mem_eigenspace_iff.1 (hf j)] at this
    rw [map_smul, this, smul_smul, hc1, one_smul]

end Contract

/-! ## Splittings of a differential on the generators -/

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]

/-- **A splitting of an odd endomorphism `d`**: an idempotent `p` onto a complement of the
boundaries in the cycles, and a homotopy `h` with `d h + h d = 1 - p`. -/
structure Splitting (d : GrSpEnd R V true) where
  /-- The projection onto the chosen representatives of the homology. -/
  p : GrSpEnd R V false
  /-- The homotopy. -/
  h : GrSpEnd R V true
  pp : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : V A), p.app A (p.app A x) = p.app A x
  dp : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : V A), d.app A (p.app A x) = 0
  pd : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : V A), p.app A (d.app A x) = 0
  dh : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : V A),
    d.app A (h.app A x) + h.app A (d.app A x) = x - p.app A x

namespace FreeGrL

variable {e e' : Bool}

/-- **Derivations extending commuting endomorphisms commute.** -/
lemma derSp_comm {a : GrSpEnd R V e} {b : GrSpEnd R V e'}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : V A),
      a.app A (b.app A x) = σ R (e && e') • b.app A (a.app A x))
    {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R V A) :
    (derSp a).app A ((derSp b).app A x) = σ R (e && e') • (derSp b).app A ((derSp a).app A x) := by
  have h0 := derSp_gcomm_app a b x
  rw [derSp_congr (ψ := GrSpEnd.zero R V (xor e e')) (fun A _ _ x => by
    rw [GrSpEnd.gcomm_app, h, sub_self, GrSpEnd.zero_app]), derSp_zero_app] at h0
  exact sub_eq_zero.1 h0

/-- A morphism extending a map commuting with an even endomorphism commutes with its
derivation. -/
lemma mapSp_derSp_comm {a : GrSpEnd R V false} {φ : GrSpEnd R V false}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : V A),
      a.app A (φ.app A x) = φ.app A (a.app A x))
    {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R V A) :
    (derSp a).app A ((mapSp φ.toHom).app A x) = (mapSp φ.toHom).app A ((derSp a).app A x) :=
  derSp_mapSp (fun A _ _ v => h A v) x

end FreeGrL

namespace Splitting

open FreeGrL

variable {d : GrSpEnd R V true} (s : Splitting d)

/-- The projection `T(p)` kills `δ`. -/
lemma mapSp_derSp {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R V A) :
    (mapSp s.p.toHom).app A ((derSp d).app A x) = 0 := by
  rw [← derSp_mapSp (b := GrSpEnd.zero R V true) (fun A _ _ v => by
    rw [GrSpEnd.zero_app, GrSpEnd.toHom_app, s.pd]), derSp_zero_app]

/-- `δ` kills the image of the projection `T(p)`. -/
lemma derSp_mapSp {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R V A) :
    (derSp d).app A ((mapSp s.p.toHom).app A x) = 0 := by
  rw [FreeGrL.derSp_mapSp (a := GrSpEnd.zero R V true) (fun A _ _ v => by
    rw [GrSpEnd.toHom_app, s.dp, GrSpEnd.zero_app, map_zero]), derSp_zero_app, map_zero]

/-- The projection `T(p)` is idempotent. -/
lemma mapSp_mapSp {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R V A) :
    (mapSp s.p.toHom).app A ((mapSp s.p.toHom).app A x) = (mapSp s.p.toHom).app A x := by
  rw [mapSp_comp]
  exact mapSp_congr (fun A _ _ v => s.pp A v) x

/-- **The derivation trick**: `δ D_h + D_h δ = N`. -/
lemma contract {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R V A) :
    (derSp d).app A ((derSp s.h).app A x) + (derSp s.h).app A ((derSp d).app A x)
      = (derSp (GrSpEnd.compl R V s.p)).app A x := by
  have h0 := derSp_gcomm_app d s.h x
  rw [Bool.and_self, σ_true, neg_one_smul, sub_neg_eq_add] at h0
  rw [h0]
  exact derSp_congr (fun A _ _ v => by
    rw [GrSpEnd.gcomm_app, Bool.and_self, σ_true, neg_one_smul, sub_neg_eq_add, s.dh]; rfl) x

variable (c : GrSpEnd R V false)
  (hcd : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : V A),
    c.app A (d.app A x) = d.app A (c.app A x))
  (hcp : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : V A),
    c.app A (s.p.app A x) = s.p.app A (c.app A x))
  (hch : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : V A),
    c.app A (s.h.app A x) = s.h.app A (c.app A x))
include hcd hcp hch

/-- **`T(p)` is a retraction onto `T(im p)` with acyclic kernel**, on each eigenspace of the
derivation extending an even endomorphism commuting with `d`, `p` and `h`, over a `ℚ`-algebra. -/
theorem retract [Algebra ℚ R] (k : ℕ) (A : Type) [Fintype A] [DecidableEq A] :
    QIso.Retract (eig R V c k A) ((derSp d).app A) ((mapSp s.p.toHom).app A) where
  mem x hx := mem_eig.2 (by rw [mapSp_derSp_comm hcp, mem_eig.1 hx, map_smul])
  memD x hx := mem_eig.2 (by
    rw [derSp_comm (e := false) (e' := true) (fun A _ _ x => by rw [hcd, Bool.false_and, σ_false,
      one_smul]), Bool.false_and, σ_false, one_smul, mem_eig.1 hx, map_smul])
  rr x := s.mapSp_mapSp x
  rD x := s.mapSp_derSp x
  Dr x := s.derSp_mapSp x
  acyc x hx hδx hpx := by
    have hpos := sub_mapSp_mem s.p s.pp x
    rw [hpx, sub_zero] at hpos
    have hcompl : ∀ (A : Type) [Fintype A] [DecidableEq A] (y : V A),
        (GrSpEnd.compl R V s.p).app A (c.app A y) = c.app A ((GrSpEnd.compl R V s.p).app A y) :=
      fun A _ _ y => by rw [GrSpEnd.compl_app, GrSpEnd.compl_app, map_sub, hcp]
    obtain ⟨z, hz, hδz⟩ := exists_eq_of_contract ((derSp (GrSpEnd.compl R V s.p)).app A)
      ((derSp d).app A) ((derSp s.h).app A) ((derSp c).app A) (k : R)
      (fun y => by
        rw [derSp_comm (e := false) (e' := true) (fun A _ _ y => by
          rw [GrSpEnd.compl_app, GrSpEnd.compl_app, map_sub, s.pd, s.dp, Bool.false_and,
            σ_false, one_smul])]
        rw [Bool.false_and, σ_false, one_smul])
      (fun y => by
        rw [derSp_comm (e := false) (e' := false) (fun A _ _ y => by
          rw [hcompl, Bool.false_and, σ_false, one_smul])]
        rw [Bool.false_and, σ_false, one_smul])
      (fun y => by
        rw [derSp_comm (e := false) (e' := true) (fun A _ _ y => by
          rw [hch, Bool.false_and, σ_false, one_smul])]
        rw [Bool.false_and, σ_false, one_smul])
      (fun y => s.contract y) hpos hδx (mem_eig.1 hx)
    exact ⟨z, mem_eig.2 hz, hδz⟩

end Splitting

end Operad
