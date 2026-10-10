/-
# Values of the operations of a presented graded operad

For an algebra `φ` over a presented graded operad `P` and odd inputs `w a` attached to the letters
`a : ℕ`, the values of the homogeneous operations with inputs `s`, at any order, span a submodule
`AlgVal.Tsp φ w s`. It lies in the range of the evaluation at the default order
(`AlgVal.Tsp_le`), it contains the inputs (`AlgVal.input_mem_Tsp`) and the values of a unary
operation at the inputs (`AlgVal.unary_mem_Tsp`), and it is closed under the binary operations on
disjoint sets of letters (`AlgVal.binop_mem_Tsp`), by filling the two inputs of a binary operation
(`GerDim.gbin_fam_apply`).
-/
import Operad.GerModel

universe u v w

namespace Operad

namespace AlgVal

open Sym GrEnd EndGr GerDim

variable {K : Type u} [Field K] {T : ℕ → Type} {gp : ∀ k, T k → Bool}
  {r : ∀ n : ℕ, Set (FreeGr K gp (Fin n))}
  {V : Type v} [AddCommGroup V] [Module K V] [SuperMod K V]
  (φ : GrAlgebra K V (GrOperadIdeal.span K r).Quot) (w : ℕ → V)

/-- **Evaluation at the inputs of the letters**, at the default order. -/
noncomputable def ev (s : Finset ℕ) : (GrOperadIdeal.span K r).Quot ↥s →ₗ[K] V where
  toFun q := (φ.app ↥s q).fam (dord ↥s) fun a => w a.1
  map_add' q q' := by rw [map_add, add_fam]; rfl
  map_smul' c q := by rw [map_smul, smul_fam]; rfl

/-- **The values of the homogeneous operations** on the letters `s`, at any order. -/
noncomputable def Tsp (s : Finset ℕ) : Submodule K V :=
  Submodule.span K {y | ∃ (q : (GrOperadIdeal.span K r).Quot ↥s) (b : Bool) (L : LinOrd ↥s),
    GrOperad.par (R := K) b q = q ∧ y = (φ.app ↥s q).fam L fun a => w a.1}

variable {φ w}

lemma val_mem_Tsp {s : Finset ℕ} {q : (GrOperadIdeal.span K r).Quot ↥s} {b : Bool}
    (hq : GrOperad.par (R := K) b q = q) (L : LinOrd ↥s) : ((φ.app ↥s q).fam L fun a => w a.1) ∈ Tsp φ w s :=
  Submodule.subset_span ⟨q, b, L, hq, rfl⟩

variable (hw : ∀ a, SuperMod.pr (R := K) true (w a) = w a)
include hw

lemma isHom_w {A : Type} [Fintype A] [DecidableEq A] (f : A → ℕ) :
    IsHom (R := K) (fun _ => true) fun a => w (f a) :=
  fun a => hw (f a)

/-- **The values are values of the evaluation.** -/
lemma Tsp_le (s : Finset ℕ) : Tsp φ w s ≤ LinearMap.range (ev φ w s) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨q, b, L, -, rfl⟩
  refine ⟨rsg K (dord ↥s) L (fun _ => true) • q, ?_⟩
  rw [map_smul, fam_change _ (dord ↥s) L (isHom_w hw _)]
  rfl

omit hw in
/-- **The value of a unary operation** at the input of a letter. -/
lemma unary_mem_Tsp {g : (GrOperadIdeal.span K r).Quot (Fin 1)} {b : Bool}
    (hg : GrOperad.par (R := K) b g = g) (β : V →ₗ[K] V) (hβ : ∀ x, EndGr.sv (φ.app _ g) ![x] = β x) (a : ℕ) :
    β (w a) ∈ Tsp φ w {a} := by
  let e : Fin 1 ≃ ({a} : Finset ℕ) :=
    ⟨fun _ => ⟨a, Finset.mem_singleton_self a⟩, fun _ => 0, fun i => Subsingleton.elim _ _,
      fun x => Subtype.ext (Finset.mem_singleton.1 x.2).symm⟩
  have hq : GrOperad.par (R := K) b (GrOperad.map (R := K) e g) = GrOperad.map (R := K) e g := by
    rw [← GrOperad.map_par, hg]
  have h := val_mem_Tsp (φ := φ) (w := w) hq (LinOrd.map e (LinOrd.std 1))
  rw [GrOperadHom.app_map, map_fam_apply] at h
  rw [← hβ]
  convert h using 2
  funext i
  fin_cases i
  rfl

omit hw in
/-- **The input of a letter is a value**: of the unit. -/
lemma input_mem_Tsp (a : ℕ) : w a ∈ Tsp φ w {a} := by
  let e : Unit ≃ ({a} : Finset ℕ) :=
    ⟨fun _ => ⟨a, Finset.mem_singleton_self a⟩, fun _ => (), fun _ => rfl,
      fun x => Subtype.ext (Finset.mem_singleton.1 x.2).symm⟩
  have hq : GrOperad.par (R := K) false (GrOperad.map (R := K) e (GrOperad.one (R := K)))
      = (GrOperad.map (R := K) e (GrOperad.one (R := K)) :
          (GrOperadIdeal.span K r).Quot ↥({a} : Finset ℕ)) := by
    rw [← GrOperad.map_par, GrOperad.par_one]
  have h := val_mem_Tsp (φ := φ) (w := w) hq (dord _)
  rwa [GrOperadHom.app_map, GrOperadHom.app_one] at h

/-- **The values are closed under a binary operation**, on disjoint letters. -/
theorem binop_mem_Tsp {g : (GrOperadIdeal.span K r).Quot (Fin 2)} {b₀ : Bool}
    (hg : GrOperad.par (R := K) b₀ g = g) (β : V →ₗ[K] V →ₗ[K] V) (hβ : ∀ y z, EndGr.sv (φ.app _ g) ![y, z] = β y z)
    {s t : Finset ℕ} (h : Disjoint s t) {y z : V} (hy : y ∈ Tsp φ w s) (hz : z ∈ Tsp φ w t) :
    β y z ∈ Tsp φ w (s ∪ t) := by
  have hm := Submodule.apply_mem_map₂ β hy hz
  rw [Tsp, Tsp, Submodule.map₂_span_span] at hm
  refine (Submodule.span_le.2 ?_) hm
  rintro _ ⟨_, ⟨q₁, b₁, L₁, hq₁, rfl⟩, _, ⟨q₂, b₂, L₂, hq₂, rfl⟩, rfl⟩
  have hq₁' : GrOperad.par (R := K) b₁ (φ.app _ q₁) = φ.app _ q₁ := by
    rw [← GrOperadHom.app_par, hq₁]
  have hq₂' : GrOperad.par (R := K) b₂ (φ.app _ q₂) = φ.app _ q₂ := by
    rw [← GrOperadHom.app_par, hq₂]
  have hQ : GrOperad.par (R := K) (xor (xor b₀ b₁) b₂)
      (GrOperad.map (R := K) (Equiv.Finset.union s t h) (gbin K g q₁ q₂))
      = GrOperad.map (R := K) (Equiv.Finset.union s t h) (gbin K g q₁ q₂) := by
    rw [← GrOperad.map_par, gbin_par hg hq₁ hq₂]
  obtain ⟨c, hc, hv⟩ := gbin_fam_apply (φ.app _ g) hq₁' hq₂' L₁ L₂
    (isHom_w hw fun a : ↥s ⊕ ↥t => (Equiv.Finset.union s t h a).1)
  have hval := val_mem_Tsp (φ := φ) (w := w) hQ (LinOrd.map (Equiv.Finset.union s t h)
    (LinOrd.map (binEquiv _ _)
      (LinOrd.comp (Sum.inl slotOne) (LinOrd.comp 0 (LinOrd.std 2) L₁) L₂)))
  rw [GrOperadHom.app_map, app_gbin, map_fam_apply] at hval
  rw [hv] at hval
  have := Submodule.smul_mem _ c hval
  rw [smul_smul, hc, one_smul] at this
  convert this using 1
  exact (hβ _ _).symm

end AlgVal

end Operad
