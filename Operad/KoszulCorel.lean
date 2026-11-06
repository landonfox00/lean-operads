/-
# The corelations of quadratic data

For quadratic data `(E, r)`, the corelations `s²R ⊆ T^c(sE)^{(2)}` are the trees with two
vertices whose image under the convolution square `κ_T ⋆ κ_T` of the desuspension map is a
relation (`Koszul.coRel`). This file identifies them with the relations and places them in the
Koszul dual cooperad `P^¡`, over a field of characteristic zero.

* **`κ_T ⋆ κ_T` is a bijection between the trees with two vertices**
  `T^c(sE)^{(2)} ≃ T(E)^{(2)}` (`Koszul.starEquiv`, `Koszul.bijOn_starKap`), when there are no
  generators without inputs. The comparison goes through the cobar construction `ΩT^c(sE)`: the
  morphism `T(E) → ΩT^c(sE)`, `v ↦ s⁻¹(sv)` (`Koszul.lamHom`), has the retraction
  `ΩT^c(sE) → T(E)`, `s⁻¹ c̄ ↦ κ_T(c)` (`Koszul.kapHom`, `Koszul.kapHom_lamHom`), which sends
  `ι ⋆ ι` to `κ_T ⋆ κ_T` (`Koszul.kapHom_ιι`); on the trees with two vertices the convolution
  square of `T^c(sE) → T(E) → ΩT^c(sE)` is `ι ⋆ ι` (`Koszul.star_lamKap`, from
  `FreeGrL.star_eq_of_wtEqL_two`). **Injectivity** (`Koszul.eq_zero_of_starKap_eq_zero`): then
  `ι ⋆ ι = -d ∘ ι` kills the element, which vanishes by the contraction identity of the cobar
  construction (`Cobar.eq_zero_of_d_ιL`). **Surjectivity** (`Koszul.exists_starKap`): the image of
  a tree with two vertices of `T(E)` in `ΩT^c(sE)` is a cycle, hence the boundary of its
  contraction (`Koszul.lamHom_eq_d_hM`, by `Cobar.dh_hd`), hence the boundary `d(ι c) = -(ι ⋆ ι)(c)`
  of a generator, the cobar differential raising the number of vertices by one
  (`Cobar.exists_eq_d_ιL`); the retraction sends it to `-(κ_T ⋆ κ_T)(c)`.
* **`s²R` is the image of `R`**: `(κ_T ⋆ κ_T)(s²R) = R` (`Koszul.map_coRel`), and
  `κ_T ⋆ κ_T` restricts to an isomorphism `s²R ≃ R` (`Koszul.coRelEquiv`), for quadratic relators
  without generators without inputs.
* **`s²R ⊆ P^¡`** (`Koszul.coRel_le_dual`): the trees with at most one vertex and the corelations
  form a subcooperad (`Koszul.coRelSub`), since the parts of the decomposition of a corelation with
  a unit on one side are a unit tensored with a relabelled corelation, by the counit laws
  (`GrCooperad.exists_lid_counit_decomp`, `GrCooperad.exists_rid_counit_decomp`). With
  `Koszul.dual_inf_wtEqL_le`, **the trees with two vertices of `P^¡` are exactly the corelations**:
  `P^¡ ∩ T^c(sE)^{(2)} = s²R` (`Koszul.dual_inf_wtEqL`), for quadratic relators.

The hypothesis that `E` has no elements without inputs is needed for the bijection: the
convolution product sums over the decompositions whose inner operation has at least one input
(`GrOperad.Inv.star`), so it does not see the cut below a generator without inputs at the top of
a tree with two vertices, and `κ_T ⋆ κ_T` vanishes on such a tree. The inclusion `s²R ⊆ P^¡` holds
without it.
-/
import Operad.KoszulQuadratic
import Operad.CobarQIso
import Operad.CutCofree

universe u v w

namespace Operad

open Sym GerBV
open scoped TensorProduct

/-! ## Weights and the convolution square -/

section Weights

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {A : Type} [Fintype A] [DecidableEq A]

namespace FreeGrL

/-- **The trees with `n` vertices are the eigenspace of the vertex count for `n`**, over a
`ℚ`-algebra. -/
theorem wtEqL_eq_vx [Algebra ℚ R] (n : ℕ) : wtEqL R V n A = vx R V n A := by
  refine le_antisymm (wtEqL_le_vx n) fun x hx => ?_
  have hx' : x ∈ wtEqL R V n A ⊔ ⨆ (m : ℕ) (_ : m ≠ n), wtEqL R V m A := by
    rw [← iSup_split_single (fun m => wtEqL R V m A) n, iSup_wtEqL]
    exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
  have hz' : z ∈ ⨆ (m : ℕ) (_ : m ≠ n), vx R V m A :=
    (iSup₂_mono fun m _ => wtEqL_le_vx m) hz
  have hz2 : z ∈ vx R V n A := by
    simpa using sub_mem hx (wtEqL_le_vx n hy)
  rw [Submodule.disjoint_def.1
    (iSupIndep_eigenspace_nat ((derSp (GrSpEnd.id R V)).app A) n) z hz2 hz', add_zero]
  exact hy

variable {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]

/-- **The convolution square of `f` and `g` vanishes on the trees with `n` vertices** when for
every splitting `n = a + b`, `f` vanishes on the trees with `a` vertices or `g` on those with `b`
vertices. -/
theorem star_eq_zero_of_wtEqL {f g : GrOperad.Inv R (ConvOp R (FreeGrL R V) Q)} {n : ℕ}
    (h : ∀ a b : ℕ, a + b = n →
      (∀ (A : Type) [Fintype A] [DecidableEq A] (x : FreeGrL R V A), x ∈ wtEqL R V a A →
        ConvOp.toLin (f.1 A) x = 0) ∨
      (∀ (B : Type) [Fintype B] [DecidableEq B] (x : FreeGrL R V B), x ∈ wtEqL R V b B →
        ConvOp.toLin (g.1 B) x = 0))
    {x : FreeGrL R V A} (hx : x ∈ wtEqL R V n A) :
    ConvOp.toLin ((GrOperad.Inv.star R _ f g).1 A) x = 0 := by
  rw [GrOperad.Inv.star_apply, ConvOp.toLin_sum, LinearMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun S _ => ?_
  show ConvOp.toLin (ConvOp.mapC (splitEquiv S)
    (ConvOp.compC none (f.1 (SOut S)) (g.1 (SIn S)))) x = 0
  rw [ConvOp.mapC_apply, ConvOp.toLin_compC, LinearMap.comp_apply, LinearMap.comp_apply]
  have hx' : SymSpecies.map (R := R) (splitEquiv S).symm x ∈ wtEqL R V n _ := by
    rw [symMap_eq]
    exact map_mem_wtEqL _ hx
  have hk := decomp_mem_wtEqL (none : SOut S) hx'
  have hle : (⨆ (a : ℕ) (b : ℕ) (_ : a + b = n), LinearMap.range (TensorProduct.map
      (wtEqL R V a (SOut S)).subtype (wtEqL R V b (SIn S)).subtype))
      ≤ LinearMap.ker (ConvOp.kap (f.1 (SOut S)) (g.1 (SIn S))) := by
    refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
    rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul p q =>
      rw [LinearMap.mem_ker, TensorProduct.map_tmul]
      simp only [ConvOp.kap, LinearMap.coe_sum, Finset.sum_apply, TensorProduct.map_tmul]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [Submodule.subtype_apply, Submodule.subtype_apply, LinearMap.comp_apply]
      rcases h a b hab with hf | hg
      · have hp : GrSpecies.tw (R := R) c p.1 ∈ wtEqL R V a (SOut S) := by
          rw [GrSpecies.tw_apply]
          exact add_mem (par_mem_wtEqL false p.2) (Submodule.smul_mem _ _ (par_mem_wtEqL true p.2))
        rw [hf _ _ hp, TensorProduct.zero_tmul]
      · have hq : ∀ c' : Bool, ConvOp.toLin (g.1 (SIn S)) (GrSpecies.par (R := R) c' q.1) = 0 :=
          fun c' => hg _ _ (par_mem_wtEqL (V := V) c' q.2)
        rw [ConvOp.parC_apply, Finset.sum_eq_zero fun c' _ => by rw [hq c', map_zero],
          TensorProduct.tmul_zero]
    | add t t' ht ht' =>
      rw [LinearMap.mem_ker, map_add, map_add]
      rw [LinearMap.mem_ker] at ht ht'
      rw [ht, ht', add_zero]
  rw [LinearMap.mem_ker.1 (hle hk), map_zero, map_zero]

/-- **Convolution squares only see the trees with one vertex, on the trees with two vertices**:
for families vanishing on the trees without vertices and agreeing on the trees with one vertex,
the convolution squares agree on the trees with two vertices. -/
theorem star_eq_of_wtEqL_two {f f' : GrOperad.Inv R (ConvOp R (FreeGrL R V) Q)}
    (h0 : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : FreeGrL R V A), x ∈ wtEqL R V 0 A →
      ConvOp.toLin (f.1 A) x = 0)
    (h0' : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : FreeGrL R V A), x ∈ wtEqL R V 0 A →
      ConvOp.toLin (f'.1 A) x = 0)
    (h1 : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : FreeGrL R V A), x ∈ wtEqL R V 1 A →
      ConvOp.toLin (f.1 A) x = ConvOp.toLin (f'.1 A) x)
    {x : FreeGrL R V A} (hx : x ∈ wtEqL R V 2 A) :
    ConvOp.toLin ((GrOperad.Inv.star R _ f f).1 A) x
      = ConvOp.toLin ((GrOperad.Inv.star R _ f' f').1 A) x := by
  have hδ : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : FreeGrL R V A),
      ConvOp.toLin ((f - f').1 A) x = ConvOp.toLin (f.1 A) x - ConvOp.toLin (f'.1 A) x :=
    fun _ _ _ _ => rfl
  have hδ0 : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : FreeGrL R V A), x ∈ wtEqL R V 0 A →
      ConvOp.toLin ((f - f').1 A) x = 0 := fun _ _ _ _ hx => by
    rw [hδ, h0 _ _ hx, h0' _ _ hx, sub_zero]
  have hδ1 : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : FreeGrL R V A), x ∈ wtEqL R V 1 A →
      ConvOp.toLin ((f - f').1 A) x = 0 := fun _ _ _ _ hx => by
    rw [hδ, h1 _ _ hx, sub_self]
  have e1 : ConvOp.toLin ((GrOperad.Inv.star R _ (f - f') f).1 A) x = 0 :=
    star_eq_zero_of_wtEqL (fun a b hab => by
      rcases a with _ | _ | a
      · exact Or.inl hδ0
      · exact Or.inl hδ1
      · have hb : b = 0 := by omega
        subst hb
        exact Or.inr h0) hx
  have e2 : ConvOp.toLin ((GrOperad.Inv.star R _ f' (f - f')).1 A) x = 0 :=
    star_eq_zero_of_wtEqL (fun a b hab => by
      rcases b with _ | _ | b
      · exact Or.inr hδ0
      · exact Or.inr hδ1
      · have ha : a = 0 := by omega
        subst ha
        exact Or.inl h0') hx
  have k1 : ConvOp.toLin ((GrOperad.Inv.star R _ (f - f') f).1 A) x
      = ConvOp.toLin ((GrOperad.Inv.star R _ f f).1 A) x
        - ConvOp.toLin ((GrOperad.Inv.star R _ f' f).1 A) x := by
    rw [LinearMap.map_sub₂]
    rfl
  have k2 : ConvOp.toLin ((GrOperad.Inv.star R _ f' (f - f')).1 A) x
      = ConvOp.toLin ((GrOperad.Inv.star R _ f' f).1 A) x
        - ConvOp.toLin ((GrOperad.Inv.star R _ f' f').1 A) x := by
    rw [map_sub]
    rfl
  rw [k1] at e1
  rw [k2] at e2
  exact (sub_eq_zero.1 e1).trans (sub_eq_zero.1 e2)

end FreeGrL

/-! ### Boundaries with two vertices in the cobar construction -/

namespace Cobar

open FreeGrL

local notation "𝒞" => FreeGrL R V

/-- **The elements of the cobar construction with one vertex are the generators**, over a
`ℚ`-algebra. -/
lemma exists_eq_ιL [Algebra ℚ R] {W : CobarGr R 𝒞 A} (hW : W ∈ vx R (CobarGen R 𝒞) 1 A) :
    ∃ c : 𝒞 A, W = Cobar.ιL R 𝒞 A c := by
  obtain ⟨c, hc⟩ := GrCooperad.Red.proj_surjective (R := R) (C := 𝒞) A
    ((GrSpecies.Shift.of (R := R) (V := GrCooperad.Red R 𝒞) A).symm
      (genCoef R (CobarGen R 𝒞) A W))
  have hc' : GrSpecies.Shift.of (R := R) (V := GrCooperad.Red R 𝒞) A (GrCooperad.Red.proj R 𝒞 A c)
      = genCoef R (CobarGen R 𝒞) A W :=
    (congrArg _ hc).trans (LinearEquiv.apply_symm_apply _ _)
  exact ⟨c, (eq_ι_genCoef hW).trans
    ((congrArg ((FreeGrL.ι R (CobarGen R 𝒞)).app A) hc'.symm).trans (Cobar.ιL_apply R 𝒞 c).symm)⟩

/-- Every element of the cobar construction is its part with one vertex plus the others. -/
lemma mem_vx_one_sup (W : CobarGr R 𝒞 A) :
    W ∈ vx R (CobarGen R 𝒞) 1 A ⊔ ⨆ (m : ℕ) (_ : m ≠ 1), vx R (CobarGen R 𝒞) m A := by
  have htop : (⨆ m, vx R (CobarGen R 𝒞) m A) = ⊤ := iSup_vx A
  exact ((htop.symm.trans (iSup_split_single (fun m => vx R (CobarGen R 𝒞) m A) 1)).le :
    (⊤ : Submodule R (CobarGr R 𝒞 A)) ≤ _) Submodule.mem_top

/-- The cobar differential sends the parts with other than one vertex to the parts with other than
two vertices. -/
lemma d_mem_iSup_ne {W : CobarGr R 𝒞 A}
    (hW : W ∈ ⨆ (m : ℕ) (_ : m ≠ 1), vx R (CobarGen R 𝒞) m A) :
    (Cobar.d R 𝒞).app A W ∈ ⨆ (j : ℕ) (_ : j ≠ 2), vx R (CobarGen R 𝒞) j A :=
  (iSup₂_le fun m hm w hw => Submodule.mem_iSup_of_mem (m + 1)
      (Submodule.mem_iSup_of_mem (by omega) (CobarMap.d_mem_vx R 𝒞 m hw)) :
    (⨆ (m : ℕ) (_ : m ≠ 1), vx R (CobarGen R 𝒞) m A)
      ≤ (⨆ (j : ℕ) (_ : j ≠ 2), vx R (CobarGen R 𝒞) j A).comap ((Cobar.d R 𝒞).app A)) hW

/-- **A boundary with two vertices is the boundary of a generator** in the cobar construction of
the cut cooperad, over a `ℚ`-algebra: the cobar differential raises the number of vertices by
one. -/
theorem exists_eq_d_ιL [Algebra ℚ R] {Y W : CobarGr R 𝒞 A} (hY : Y ∈ vx R (CobarGen R 𝒞) 2 A)
    (hW : Y = (Cobar.d R 𝒞).app A W) :
    ∃ c : 𝒞 A, Y = (Cobar.d R 𝒞).app A (Cobar.ιL R 𝒞 A c) := by
  obtain ⟨W₁, hW₁, W', hW', hWe⟩ := Submodule.mem_sup.1 (mem_vx_one_sup W)
  have hY' : Y = (Cobar.d R 𝒞).app A W₁ + (Cobar.d R 𝒞).app A W' :=
    hW.trans ((congrArg _ hWe.symm).trans (map_add _ _ _))
  have e : (Cobar.d R 𝒞).app A W' = Y - (Cobar.d R 𝒞).app A W₁ :=
    (add_sub_cancel_left _ _).symm.trans (congrArg (· - _) hY'.symm)
  have h0 : (Cobar.d R 𝒞).app A W' = 0 :=
    Submodule.disjoint_def.1
      (iSupIndep_eigenspace_nat ((derSp (GrSpEnd.id R (CobarGen R 𝒞))).app A) 2) _
      ((congrArg (fun t => t ∈ vx R (CobarGen R 𝒞) 2 A) e).mpr
        (sub_mem hY (CobarMap.d_mem_vx R 𝒞 1 hW₁))) (d_mem_iSup_ne hW')
  obtain ⟨c, e1⟩ := exists_eq_ιL hW₁
  exact ⟨c, hY'.trans ((congrArg₂ (· + ·) (congrArg ((Cobar.d R 𝒞).app A) e1) h0).trans
    (add_zero _))⟩

end Cobar

end Weights

/-! ## Tensors with a factor on a line, and the counit laws -/

section CounitLaws

variable {R : Type u} [CommRing R]

section Tensor

variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A tensor with first factors on the line of `u` is `u ⊗ y`, for `y` read off by a functional
taking the value `1` on `u`. -/
lemma eq_tmul_of_mem_range_left {u : M} {ε : M →ₗ[R] R} (hu : ε u = 1) {P : Submodule R M}
    (hP : P ≤ R ∙ u) {Q : Submodule R N} {s : M ⊗[R] N}
    (hs : s ∈ LinearMap.range (TensorProduct.map P.subtype Q.subtype)) :
    TensorProduct.lid R N (LinearMap.rTensor N ε s) ∈ Q ∧
      s = u ⊗ₜ TensorProduct.lid R N (LinearMap.rTensor N ε s) := by
  obtain ⟨t, rfl⟩ := hs
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul p q =>
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hP p.2)
    simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
      Submodule.subtype_apply, ← hc, map_smul, hu, smul_eq_mul, mul_one]
    exact ⟨Q.smul_mem c q.2, TensorProduct.smul_tmul c u q.1⟩
  | add t t' ht ht' =>
    simp only [map_add]
    exact ⟨add_mem ht.1 ht'.1, by rw [TensorProduct.tmul_add]; exact congrArg₂ (· + ·) ht.2 ht'.2⟩

/-- A tensor with second factors on the line of `u` is `y ⊗ u`, for `y` read off by a functional
taking the value `1` on `u`. -/
lemma eq_tmul_of_mem_range_right {u : N} {ε : N →ₗ[R] R} (hu : ε u = 1) {Q : Submodule R N}
    (hQ : Q ≤ R ∙ u) {P : Submodule R M} {s : M ⊗[R] N}
    (hs : s ∈ LinearMap.range (TensorProduct.map P.subtype Q.subtype)) :
    TensorProduct.rid R M (LinearMap.lTensor M ε s) ∈ P ∧
      s = TensorProduct.rid R M (LinearMap.lTensor M ε s) ⊗ₜ u := by
  obtain ⟨t, rfl⟩ := hs
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul p q =>
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hQ q.2)
    simp only [TensorProduct.map_tmul, LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
      Submodule.subtype_apply, ← hc, map_smul, hu, smul_eq_mul, mul_one]
    exact ⟨P.smul_mem c p.2, (TensorProduct.smul_tmul c p.1 u).symm⟩
  | add t t' ht ht' =>
    simp only [map_add]
    exact ⟨add_mem ht.1 ht'.1, by rw [TensorProduct.add_tmul]; exact congrArg₂ (· + ·) ht.2 ht'.2⟩

lemma rTensor_eq_zero_of_le_ker {ε : M →ₗ[R] R} {P : Submodule R M} (hP : P ≤ LinearMap.ker ε)
    {Q : Submodule R N} {s : M ⊗[R] N}
    (hs : s ∈ LinearMap.range (TensorProduct.map P.subtype Q.subtype)) :
    LinearMap.rTensor N ε s = 0 := by
  obtain ⟨t, rfl⟩ := hs
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul p q =>
    rw [TensorProduct.map_tmul, LinearMap.rTensor_tmul, Submodule.subtype_apply,
      LinearMap.mem_ker.1 (hP p.2), TensorProduct.zero_tmul]
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', add_zero]

lemma lTensor_eq_zero_of_le_ker {ε : N →ₗ[R] R} {Q : Submodule R N} (hQ : Q ≤ LinearMap.ker ε)
    {P : Submodule R M} {s : M ⊗[R] N}
    (hs : s ∈ LinearMap.range (TensorProduct.map P.subtype Q.subtype)) :
    LinearMap.lTensor M ε s = 0 := by
  obtain ⟨t, rfl⟩ := hs
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul p q =>
    rw [TensorProduct.map_tmul, LinearMap.lTensor_tmul, Submodule.subtype_apply,
      Submodule.subtype_apply, LinearMap.mem_ker.1 (hQ q.2), TensorProduct.tmul_zero]
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', add_zero]

lemma eq_zero_of_mem_range_bot_left {P : Submodule R M} (hP : P = ⊥) {Q : Submodule R N}
    {s : M ⊗[R] N} (hs : s ∈ LinearMap.range (TensorProduct.map P.subtype Q.subtype)) : s = 0 := by
  obtain ⟨t, rfl⟩ := hs
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul p q =>
    have hp : (p : M) = 0 := (Submodule.mem_bot R).1 (hP ▸ p.2)
    rw [TensorProduct.map_tmul, Submodule.subtype_apply, hp, TensorProduct.zero_tmul]
  | add t t' ht ht' => rw [map_add, ht, ht', add_zero]

lemma eq_zero_of_mem_range_bot_right {Q : Submodule R N} (hQ : Q = ⊥) {P : Submodule R M}
    {s : M ⊗[R] N} (hs : s ∈ LinearMap.range (TensorProduct.map P.subtype Q.subtype)) : s = 0 := by
  obtain ⟨t, rfl⟩ := hs
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul p q =>
    have hq : (q : N) = 0 := (Submodule.mem_bot R).1 (hQ ▸ q.2)
    rw [TensorProduct.map_tmul, Submodule.subtype_apply (p := Q), hq, TensorProduct.tmul_zero]
  | add t t' ht ht' => rw [map_add, ht, ht', add_zero]

end Tensor

/-- The bijection of `Unit` onto a type all of whose elements are `i`. -/
def unitEquivOf {A : Type} (i : A) (hA : ∀ a : A, a = i) : Unit ≃ A where
  toFun _ := i
  invFun _ := ()
  left_inv _ := rfl
  right_inv a := (hA a).symm

variable {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

namespace GrCooperad

/-- **The left counit law at an input set with one element `i`**: the counit applied to the outer
factor of a decomposition at `i` gives back the cooperation, relabelled. -/
lemma exists_lid_counit_decomp (i : A) (hA : ∀ a : A, a = i) (x : C (Without A i ⊕ B)) :
    ∃ τ : Without A i ⊕ B ≃ B, TensorProduct.lid R (C B) (LinearMap.rTensor (C B)
      (GrCooperad.counit (R := R) (C := C) ∘ₗ SymSpecies.map (R := R) (unitEquivOf i hA).symm)
      (GrCooperad.decomp (R := R) (C := C) i x)) = SymSpecies.map (R := R) τ x := by
  set e := unitEquivOf i hA
  set σ := compEquiv e (Equiv.refl B) ()
  refine ⟨σ.symm.trans (leftUnitEquiv B), ?_⟩
  have hnat : GrCooperad.decomp (R := R) (C := C) i x
      = TensorProduct.map (SymSpecies.map (R := R) e) (SymSpecies.map (R := R) (Equiv.refl B))
        (GrCooperad.decomp (R := R) (C := C) () (SymSpecies.map (R := R) σ.symm x)) := by
    have h := LinearMap.congr_fun (GrCooperad.decomp_map (R := R) (C := C) e (Equiv.refl B) ())
      (SymSpecies.map (R := R) σ.symm x)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, SymSpecies.map_map_symm] at h
    exact h
  have hcl := LinearMap.congr_fun (GrCooperad.counit_left (R := R) (C := C) (B := B))
    (SymSpecies.map (R := R) (leftUnitEquiv B) (SymSpecies.map (R := R) σ.symm x))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, SymSpecies.map_symm_map,
    LinearMap.id_apply] at hcl
  refine Eq.trans ?_ ((SymSpecies.map_trans (R := R) σ.symm (leftUnitEquiv B) x).trans
    hcl.symm).symm
  rw [hnat]
  generalize GrCooperad.decomp (R := R) (C := C) () (SymSpecies.map (R := R) σ.symm x) = s
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.comp_apply,
      TensorProduct.lid_tmul, SymSpecies.map_symm_map, SymSpecies.map_refl]
  | add s s' hs hs' => simp only [map_add, hs, hs']

/-- **The right counit law at an inner input set with one element `j`**: the counit applied to
the inner factor of a decomposition gives back the cooperation, relabelled. -/
lemma exists_rid_counit_decomp (i : A) (j : B) (hB : ∀ b : B, b = j)
    (x : C (Without A i ⊕ B)) :
    ∃ τ : Without A i ⊕ B ≃ A, TensorProduct.rid R (C A) (LinearMap.lTensor (C A)
      (GrCooperad.counit (R := R) (C := C) ∘ₗ SymSpecies.map (R := R) (unitEquivOf j hB).symm)
      (GrCooperad.decomp (R := R) (C := C) i x)) = SymSpecies.map (R := R) τ x := by
  set e := unitEquivOf j hB
  set σ := compEquiv (Equiv.refl A) e i
  refine ⟨σ.symm.trans (rightUnitEquiv i), ?_⟩
  have hnat : GrCooperad.decomp (R := R) (C := C) i x
      = TensorProduct.map (SymSpecies.map (R := R) (Equiv.refl A)) (SymSpecies.map (R := R) e)
        (GrCooperad.decomp (R := R) (C := C) i (SymSpecies.map (R := R) σ.symm x)) := by
    have h := LinearMap.congr_fun (GrCooperad.decomp_map (R := R) (C := C) (Equiv.refl A) e i)
      (SymSpecies.map (R := R) σ.symm x)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, SymSpecies.map_map_symm] at h
    exact h
  have hcl := LinearMap.congr_fun (GrCooperad.counit_right (R := R) (C := C) i)
    (SymSpecies.map (R := R) (rightUnitEquiv i) (SymSpecies.map (R := R) σ.symm x))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, SymSpecies.map_symm_map,
    LinearMap.id_apply] at hcl
  refine Eq.trans ?_ ((SymSpecies.map_trans (R := R) σ.symm (rightUnitEquiv i) x).trans
    hcl.symm).symm
  rw [hnat]
  generalize GrCooperad.decomp (R := R) (C := C) i (SymSpecies.map (R := R) σ.symm x) = s
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.comp_apply,
      TensorProduct.rid_tmul, SymSpecies.map_symm_map, SymSpecies.map_refl]
  | add s s' hs hs' => simp only [map_add, hs, hs']

end GrCooperad

end CounitLaws

/-! ## The units and the trees without vertices of the cut cooperad -/

section CutUnits

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **An invariant family of the convolution operad commutes with relabellings.** -/
lemma GrOperad.Inv.toLin_map {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
    {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
    (q : GrOperad.Inv R (ConvOp R C P)) (e : A ≃ B) (y : C A) :
    ConvOp.toLin (q.1 B) (SymSpecies.map (R := R) e y)
      = GrOperad.map (R := R) e (ConvOp.toLin (q.1 A) y) := by
  rw [← GrOperad.Inv.map_apply q e]
  show GrOperad.map (R := R) e (ConvOp.toLin (q.1 A)
    (SymSpecies.map (R := R) e.symm (SymSpecies.map (R := R) e y))) = _
  rw [SymSpecies.map_symm_map]

namespace FreeGrL

local notation "𝒥" => GrOperadIdeal.span R (grLinRel R V)

lemma wtEqL_le_wtOneL {n : ℕ} (hn : n ≤ 1) : wtEqL R V n A ≤ wtOneL R V A :=
  Submodule.map_mono (Submodule.span_mono fun _ ⟨x, hx, h⟩ => ⟨x, by omega, h⟩)

/-- **The trees with vertices have no unit component.** -/
lemma unitCoeffL_wtEqL {n : ℕ} (hn : n ≠ 0) {x : FreeGrL R V A} (hx : x ∈ wtEqL R V n A) :
    unitCoeffL R V A x = 0 := by
  obtain ⟨z, hz, rfl⟩ := hx
  refine Submodule.span_induction (p := fun z _ => unitCoeffL R V A ((𝒥).proj A z) = 0)
    ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨y, hy, rfl⟩
    refine unitCoeffL_proj_bas (Bool.eq_false_iff.2 fun h => hn ?_)
    have hw : FreeGr.vtx y = (FreeGr.treeOf y).weight := Tree.cnt_one _
    rw [← hy, hw, Tree.eq_leaf_of_isLeaf h, Tree.weight_leaf]
  · simp
  · intro a b _ _ ha hb
    rw [map_add, map_add, ha, hb, add_zero]
  · intro c a _ ha
    rw [map_smul, map_smul, ha, smul_zero]

/-- **The counit of the cut cooperad kills the relabelled trees with vertices.** -/
lemma counit_map_wtEqL {n : ℕ} (hn : n ≠ 0) (e : Unit ≃ A) {x : FreeGrL R V A}
    (hx : x ∈ wtEqL R V n A) :
    GrCooperad.counit (R := R) (C := FreeGrL R V) (SymSpecies.map (R := R) e.symm x) = 0 := by
  rw [counit_eq_unitCoeffL, symMap_eq, unitCoeffL_map]
  exact unitCoeffL_wtEqL hn hx

lemma counit_map_map_one (e : Unit ≃ A) :
    GrCooperad.counit (R := R) (C := FreeGrL R V) (SymSpecies.map (R := R) e.symm
      (SymSpecies.map (R := R) e (GrCooperad.Coaug.one (R := R) (C := FreeGrL R V)))) = 1 := by
  rw [SymSpecies.map_symm_map]
  exact GrCooperad.Coaug.counit_one

/-- **On a set with one element `i`, the trees without vertices are the multiples of the relabelled
unit.** -/
lemma wtEqL_zero_le_span (i : A) (hA : ∀ a : A, a = i) :
    wtEqL R V 0 A ≤ R ∙ SymSpecies.map (R := R) (unitEquivOf i hA)
      (GrCooperad.Coaug.one (R := R) (C := FreeGrL R V)) := by
  refine wtEqL_zero_le_unitSpan.trans ?_
  rw [GrCooperad.unitSpan, GrCooperad.unitSpanOf, Submodule.span_le]
  rintro _ ⟨e, rfl⟩
  have he : e = unitEquivOf i hA := Equiv.ext fun u => hA (e u)
  rw [he]
  exact Submodule.mem_span_singleton_self _

/-- **There are no trees without vertices on a set not in bijection with `Unit`.** -/
lemma wtEqL_zero_eq_bot (h : IsEmpty (Unit ≃ A)) : wtEqL R V 0 A = ⊥ := by
  refine eq_bot_iff.2 (wtEqL_zero_le_unitSpan.trans ?_)
  rw [GrCooperad.unitSpan, GrCooperad.unitSpanOf, Submodule.span_le]
  rintro _ ⟨e, rfl⟩
  exact h.elim e

/-- The decomposition of a tree with two vertices splits into parts with `0 + 2`, `1 + 1` and
`2 + 0` vertices. -/
lemma exists_split_two {t : FreeGrL R V A ⊗[R] FreeGrL R V B}
    (ht : t ∈ ⨆ (a : ℕ) (b : ℕ) (_ : a + b = 2),
      LinearMap.range (TensorProduct.map (wtEqL R V a A).subtype (wtEqL R V b B).subtype)) :
    ∃ t₀ ∈ LinearMap.range (TensorProduct.map (wtEqL R V 0 A).subtype (wtEqL R V 2 B).subtype),
    ∃ t₁ ∈ LinearMap.range (TensorProduct.map (wtEqL R V 1 A).subtype (wtEqL R V 1 B).subtype),
    ∃ t₂ ∈ LinearMap.range (TensorProduct.map (wtEqL R V 2 A).subtype (wtEqL R V 0 B).subtype),
      t = t₀ + t₁ + t₂ := by
  have hle : (⨆ (a : ℕ) (b : ℕ) (_ : a + b = 2),
      LinearMap.range (TensorProduct.map (wtEqL R V a A).subtype (wtEqL R V b B).subtype))
      ≤ LinearMap.range (TensorProduct.map (wtEqL R V 0 A).subtype (wtEqL R V 2 B).subtype)
        ⊔ LinearMap.range (TensorProduct.map (wtEqL R V 1 A).subtype (wtEqL R V 1 B).subtype)
        ⊔ LinearMap.range (TensorProduct.map (wtEqL R V 2 A).subtype (wtEqL R V 0 B).subtype) := by
    refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
    rcases a with _ | _ | _ | a
    · have hb : b = 2 := by omega
      subst hb
      exact le_sup_left.trans le_sup_left
    · have hb : b = 1 := by omega
      subst hb
      exact le_sup_right.trans le_sup_left
    · have hb : b = 0 := by omega
      subst hb
      exact le_sup_right
    · omega
  obtain ⟨t', ht', t₂, ht₂, rfl⟩ := Submodule.mem_sup.1 (hle ht)
  obtain ⟨t₀, ht₀, t₁, ht₁, rfl⟩ := Submodule.mem_sup.1 ht'
  exact ⟨t₀, ht₀, t₁, ht₁, t₂, ht₂, rfl⟩

end FreeGrL

end CutUnits

/-! ## The comparison with the cobar construction -/

section Koszul

variable {R : Type u} [Field R] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (E A)] [GrSpecies R E]
  {A : Type} [Fintype A] [DecidableEq A]

namespace Koszul

open FreeGrL

local notation "𝒱" => GrSpecies.Shift E R
local notation "𝒞" => Cut R E

variable (R E) in
/-- **The convolution square `κ_T ⋆ κ_T`** in arity `A`. -/
noncomputable abbrev starKap (A : Type) [Fintype A] [DecidableEq A] :
    Cut R E A →ₗ[R] FreeGrL R E A :=
  ConvOp.toLin ((GrOperad.Inv.star R _ (kapT R E) (kapT R E)).1 A)

variable (R E) in
/-- The generators `v ↦ s⁻¹(sv)`, from `E` to the generators of `ΩT^c(sE)`. -/
noncomputable def lamGen : GrSpeciesHom R E (CobarGen R 𝒞) where
  app A _ _ := GrCooperad.Red.proj R 𝒞 A ∘ₗ (FreeGrL.ι R 𝒱).app A ∘ₗ
    (GrSpecies.Shift.of (R := R) (V := E) A).toLinearMap
  app_map {A B} _ _ _ _ σ' v :=
    congrArg (GrCooperad.Red.proj R 𝒞 B) ((FreeGrL.ι R 𝒱).app_map σ' (GrSpecies.Shift.of A v))
  app_par {A} _ _ b v := by
    show GrCooperad.Red.proj R 𝒞 A ((FreeGrL.ι R 𝒱).app A
        (GrSpecies.Shift.of A (GrSpecies.par (R := R) b v)))
      = GrCooperad.Red.proj R 𝒞 A (GrSpecies.par (R := R) (!b)
        ((FreeGrL.ι R 𝒱).app A (GrSpecies.Shift.of A v)))
    rw [← (FreeGrL.ι R 𝒱).app_par, GrSpecies.Shift.par_of, Bool.not_not]

variable (R E) in
/-- **The morphism `T(E) → ΩT^c(sE)`** sending a generator `v` to the generator `s⁻¹(sv)`. -/
noncomputable def lamHom : GrOperadHom R (FreeGrL R E) (CobarGr R 𝒞) := mapSp (lamGen R E)

lemma lamHom_ι (v : E A) :
    (lamHom R E).app A ((FreeGrL.ι R E).app A v)
      = Cobar.ιL R 𝒞 A ((FreeGrL.ι R 𝒱).app A (GrSpecies.Shift.of A v)) := by
  rw [lamHom, mapSp_ι]
  rfl

lemma kapL_unitSpan {x : Cut R E A} (hx : x ∈ GrCooperad.unitSpan R 𝒞 A) : kapL R E A x = 0 := by
  have h := killsUnit_kapT (R := R) (E := E) A x hx
  rwa [kapT_apply, ConvOp.toLin_of] at h

variable (R E) in
/-- The generators `s⁻¹ c̄ ↦ κ_T(c)` of `ΩT^c(sE)`, into `T(E)`. -/
noncomputable def kapGen : GrSpeciesHom R (CobarGen R 𝒞) (FreeGrL R E) where
  app A _ _ := (GrCooperad.unitSpan R 𝒞 A).liftQ (kapL R E A) fun _ hx => kapL_unitSpan hx
  app_map {A B} _ _ _ _ σ' v := by
    obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := 𝒞) A v
    exact kapL_map σ' x
  app_par {A} _ _ b v := by
    obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := 𝒞) A v
    show kapL R E A (GrSpecies.par (R := R) (!b) x) = GrOperad.par (R := R) b (kapL R E A x)
    exact (kapL_par (!b) x).trans (by rw [Bool.not_not])

variable (R E) in
/-- **The morphism `ΩT^c(sE) → T(E)`** sending a generator `s⁻¹ c̄` to `κ_T(c)`. -/
noncomputable def kapHom : GrOperadHom R (CobarGr R 𝒞) (FreeGrL R E) :=
  FreeGrL.homEquiv.symm (kapGen R E)

lemma kapHom_ιL (x : Cut R E A) : (kapHom R E).app A (Cobar.ιL R 𝒞 A x) = kapL R E A x :=
  FreeGrL.homEquiv_symm_ι (kapGen R E) _

/-- **`T(E)` is a retract of `ΩT^c(sE)`**: `ΩT^c(sE) → T(E)` undoes `T(E) → ΩT^c(sE)`. -/
lemma kapHom_lamHom (z : FreeGrL R E A) : (kapHom R E).app A ((lamHom R E).app A z) = z := by
  have h : (kapHom R E).comp (lamHom R E) = GrOperadHom.id R (FreeGrL R E) :=
    hom_ext fun A _ _ v => by
      rw [GrOperadHom.comp_app, lamHom_ι, kapHom_ιL, kapL_ι]
      rfl
  exact congrArg (fun g : GrOperadHom R (FreeGrL R E) (FreeGrL R E) => g.app A z) h

/-- `κ_T ⋆ κ_T` is the image of `ι ⋆ ι` under `ΩT^c(sE) → T(E)`. -/
lemma kapHom_ιι (x : Cut R E A) :
    (kapHom R E).app A (ConvOp.toLin ((Cobar.ιι R 𝒞).1 A) x) = starKap R E A x := by
  have e2 := GrOperad.Inv.appHom_star (ConvOp.postHom (C := 𝒞) (kapHom R E))
    (Cobar.ι R 𝒞) (Cobar.ι R 𝒞)
  have e3 : GrOperad.Inv.appHom (ConvOp.postHom (C := 𝒞) (kapHom R E)) (Cobar.ι R 𝒞)
      = kapT R E :=
    Subtype.ext (funext fun A => funext fun _ => funext fun _ =>
      ConvOp.ext fun x => kapHom_ιL x)
  have e := congrArg (fun q : GrOperad.Inv R (ConvOp R 𝒞 (FreeGrL R E)) =>
    ConvOp.toLin (q.1 A) x) (e2.trans (congrArg₂ (fun a b =>
      GrOperad.Inv.star R (ConvOp R 𝒞 (FreeGrL R E)) a b) e3 e3))
  simp only [GrOperad.Inv.appHom_apply, ConvOp.postHom_app, LinearMap.comp_apply] at e
  exact e

variable (R E) in
/-- `T^c(sE) → T(E) → ΩT^c(sE)`, the desuspension followed by the comparison. -/
noncomputable abbrev lamKap : GrOperad.Inv R (ConvOp R 𝒞 (CobarGr R 𝒞)) :=
  GrOperad.Inv.appHom (ConvOp.postHom (C := 𝒞) (lamHom R E)) (kapT R E)

lemma lamKap_apply (x : Cut R E A) :
    ConvOp.toLin ((lamKap R E).1 A) x = (lamHom R E).app A (kapL R E A x) := rfl

/-- `T(E) → ΩT^c(sE)` sends `κ_T ⋆ κ_T` to the convolution square of `lamKap`. -/
lemma lamHom_starKap (x : Cut R E A) :
    (lamHom R E).app A (starKap R E A x)
      = ConvOp.toLin ((GrOperad.Inv.star R _ (lamKap R E) (lamKap R E)).1 A) x := by
  have e := congrArg (fun q : GrOperad.Inv R (ConvOp R 𝒞 (CobarGr R 𝒞)) =>
    ConvOp.toLin (q.1 A) x) (GrOperad.Inv.appHom_star
      (ConvOp.postHom (C := 𝒞) (lamHom R E)) (kapT R E) (kapT R E))
  simp only [GrOperad.Inv.appHom_apply, ConvOp.postHom_app, LinearMap.comp_apply] at e
  exact e

/-! ### Agreement with the universal twisting morphism on two vertices -/

lemma lamKap_wtEqL_zero {x : Cut R E A} (hx : x ∈ wtEqL R 𝒱 0 A) :
    ConvOp.toLin ((lamKap R E).1 A) x = 0 := by
  rw [lamKap_apply, kapL_unitSpan (wtEqL_zero_le_unitSpan hx), map_zero]

lemma ι_wtEqL_zero {x : Cut R E A} (hx : x ∈ wtEqL R 𝒱 0 A) :
    ConvOp.toLin ((Cobar.ι R 𝒞).1 A) x = 0 :=
  Cobar.ιL_unitSpan R 𝒞 (wtEqL_zero_le_unitSpan hx)

/-- **On the trees with one vertex, `T^c(sE) → T(E) → ΩT^c(sE)` is the universal twisting
morphism.** -/
lemma lamKap_wtEqL_one [CharZero R] {y : Cut R E A} (hy : y ∈ wtEqL R 𝒱 1 A) :
    ConvOp.toLin ((lamKap R E).1 A) y = ConvOp.toLin ((Cobar.ι R 𝒞).1 A) y := by
  have hy' : y = (FreeGrL.ι R 𝒱).app A (GrSpecies.Shift.of A
      ((GrSpecies.Shift.of (R := R) (V := E) A).symm (genCoef R 𝒱 A y))) := by
    rw [LinearEquiv.apply_symm_apply]
    exact eq_ι_genCoef (wtEqL_le_vx 1 hy)
  show (lamHom R E).app A (kapL R E A y) = Cobar.ιL R 𝒞 A y
  rw [hy', kapL_ι, lamHom_ι]

/-- **`ι ⋆ ι` vanishes on the trees with one vertex.** -/
lemma ιι_ι [CharZero R] (w : 𝒱 A) :
    ConvOp.toLin ((Cobar.ιι R 𝒞).1 A) ((FreeGrL.ι R 𝒱).app A w) = 0 :=
  star_eq_zero_of_wtEqL (f := Cobar.ι R 𝒞) (g := Cobar.ι R 𝒞) (n := 1) (fun a b hab => by
    rcases a with _ | a
    · refine Or.inl ?_
      intro B _ _ x hx
      exact ι_wtEqL_zero hx
    · have hb : b = 0 := by omega
      subst hb
      refine Or.inr ?_
      intro B _ _ x hx
      exact ι_wtEqL_zero hx)
    ((wtEqL_eq_vx 1).ge (ι_mem_vx w))

/-- **On the trees with two vertices, the convolution square of `T^c(sE) → T(E) → ΩT^c(sE)` is
`ι ⋆ ι`.** -/
lemma star_lamKap [CharZero R] {y : Cut R E A} (hy : y ∈ wtEqL R 𝒱 2 A) :
    ConvOp.toLin ((GrOperad.Inv.star R _ (lamKap R E) (lamKap R E)).1 A) y
      = ConvOp.toLin ((Cobar.ιι R 𝒞).1 A) y :=
  star_eq_of_wtEqL_two (f := lamKap R E) (f' := Cobar.ι R 𝒞)
    (fun _ _ _ _ hx => lamKap_wtEqL_zero hx) (fun _ _ _ _ hx => ι_wtEqL_zero hx)
    (fun _ _ _ _ hx => lamKap_wtEqL_one hx) hy

/-! ### `κ_T ⋆ κ_T` is a bijection on the trees with two vertices -/

/-- **`κ_T ⋆ κ_T` is injective on the trees with two vertices**, over a field of characteristic
zero, when there are no generators without inputs. -/
theorem eq_zero_of_starKap_eq_zero [CharZero R] (hE0 : ∀ v : E (Fin 0), v = 0) {y : Cut R E A}
    (hy : y ∈ wtEqL R 𝒱 2 A) (h0 : starKap R E A y = 0) : y = 0 := by
  have hV0 : ∀ v : 𝒱 (Fin 0), v = 0 := hE0
  have hι : ConvOp.toLin ((Cobar.ιι R 𝒞).1 A) y = 0 := by
    rw [← star_lamKap hy, ← lamHom_starKap, h0, map_zero]
  have hd : (Cobar.d R 𝒞).app A (Cobar.ιL R 𝒞 A y) = 0 := by
    rw [Cobar.d_ιL, hι, neg_zero]
  exact Cobar.eq_zero_of_ιL (by norm_num) (wtEqL_le_vx 2 hy)
    (Cobar.eq_zero_of_d_ιL hV0 le_rfl (wtEqL_le_vx 2 hy) hd)

/-- **`T(E) → ΩT^c(sE)` preserves the number of vertices.** -/
lemma lamHom_mem_vx {n : ℕ} {z : FreeGrL R E A} (hz : z ∈ vx R E n A) :
    (lamHom R E).app A z ∈ vx R (CobarGen R 𝒞) n A := by
  refine mem_eig.2 ?_
  have e := derSp_mapSp (a := GrSpEnd.id R E) (b := GrSpEnd.id R (CobarGen R 𝒞))
    (φ := lamGen R E) (fun _ _ _ v => rfl) z
  exact e.trans ((congrArg ((mapSp (lamGen R E)).app A) (mem_eig.1 hz)).trans (map_smul _ _ _))

/-- **The image of `T(E)` in `ΩT^c(sE)` consists of cycles.** -/
lemma d_lamHom [CharZero R] (z : FreeGrL R E A) :
    (Cobar.d R 𝒞).app A ((lamHom R E).app A z) = 0 := by
  have h : (Cobar.d R 𝒞).compHom (lamHom R E) = GrDer.zero (lamHom R E) true :=
    der_eq_zero fun A _ _ v => by
      rw [GrDer.compHom_app, lamHom_ι, Cobar.d_ιL, ιι_ι, neg_zero]
  exact congrArg (fun D : GrDer (lamHom R E) true => D.app A z) h

/-- **`T(E) → ΩT^c(sE)` intertwines the vertex count with the weight of the cobar
construction.** -/
lemma wtΩ_lamHom (z : FreeGrL R E A) :
    (Cobar.wtΩ R 𝒱).app A ((lamHom R E).app A z)
      = (lamHom R E).app A ((FreeGrL.wtD R E).app A z) := by
  have h : (Cobar.wtΩ R 𝒱).compHom (lamHom R E)
      = GrDer.homComp (lamHom R E) (FreeGrL.wtD R E) :=
    der_ext fun A _ _ v => by
      show (Cobar.wtΩ R 𝒱).app A ((lamHom R E).app A ((FreeGrL.ι R E).app A v))
        = (lamHom R E).app A ((FreeGrL.wtD R E).app A ((FreeGrL.ι R E).app A v))
      have e1 := FreeGrL.wtD_ι (R := R) (V := E) v
      have e2 := lamHom_ι (R := R) (E := E) v
      have e3 := Cobar.wtΩ_ιL (R := R) (V := 𝒱) ((FreeGrL.ι R 𝒱).app A (GrSpecies.Shift.of A v))
      have e4 := FreeGrL.wtD_ι (R := R) (V := 𝒱) (GrSpecies.Shift.of A v)
      exact (congrArg _ e2).trans (e3.trans ((congrArg _ e4).trans
        (e2.symm.trans (congrArg _ e1.symm))))
  exact congrArg (fun D : GrDer (lamHom R E) false => D.app A z) h

/-- **The image of a combination of trees with two vertices of `T(E)` in `ΩT^c(sE)` is the boundary
of its contraction**, by the contraction identity, when there are no generators without inputs. -/
lemma lamHom_eq_d_hM [CharZero R] (hE0 : ∀ v : E (Fin 0), v = 0) {z : FreeGrL R E A}
    (hz : z ∈ vx R E 2 A) :
    (lamHom R E).app A z = (Cobar.d R 𝒞).app A (Cobar.hM R 𝒱 A ((lamHom R E).app A z)) := by
  have hV0 : ∀ v : 𝒱 (Fin 0), v = 0 := hE0
  have hc := Cobar.dh_hd hV0 ((lamHom R E).app A z)
  have h0 : Cobar.hM R 𝒱 A ((Cobar.d R 𝒞).app A ((lamHom R E).app A z)) = 0 :=
    (congrArg (Cobar.hM R 𝒱 A) (d_lamHom z)).trans (map_zero _)
  have h1 := (add_zero _).symm.trans
    ((congrArg (fun t => (Cobar.d R 𝒞).app A (Cobar.hM R 𝒱 A ((lamHom R E).app A z)) + t)
      h0).symm.trans hc)
  have hw : (Cobar.wtΩ R 𝒱).app A ((lamHom R E).app A z) = (2 : R) • (lamHom R E).app A z :=
    (wtΩ_lamHom z).trans ((congrArg ((lamHom R E).app A)
      ((congrArg (fun D : GrDer (GrOperadHom.id R (FreeGrL R E)) false => D.app A z)
        Cobar.wtD_eq_derSp).trans ((mem_eig.1 hz).trans (by norm_num)))).trans (map_smul _ _ _))
  have hu0 : (0 : R) = 2 * FreeGrL.unitCoeffL R (CobarGen R 𝒞) A ((lamHom R E).app A z) :=
    calc (0 : R) = FreeGrL.unitCoeffL R (CobarGen R 𝒞) A
          ((Cobar.d R 𝒞).app A (Cobar.hM R 𝒱 A ((lamHom R E).app A z))) :=
          (Cobar.unitCoeffL_d hV0 _).symm
      _ = _ := congrArg _ h1
      _ = _ := map_sub _ _ _
      _ = FreeGrL.unitCoeffL R (CobarGen R 𝒞) A ((2 : R) • (lamHom R E).app A z) - 0 :=
          congrArg₂ (· - ·) (congrArg _ hw) (FreeGrL.unitCoeffL_secC _)
      _ = _ := (sub_zero _).trans ((map_smul _ _ _).trans (smul_eq_mul _ _))
  have hu : FreeGrL.unitCoeffL R (CobarGen R 𝒞) A ((lamHom R E).app A z) = 0 :=
    (mul_eq_zero.1 hu0.symm).resolve_left two_ne_zero
  have hS := FreeGrL.secC_of_unitCoeff hu
  linear_combination (norm := module) -h1 - hw + hS

/-- **`κ_T ⋆ κ_T` only sees the part with two vertices.** -/
lemma exists_wtEqL_two_starKap [CharZero R] (c : Cut R E A) :
    ∃ c₂ ∈ wtEqL R 𝒱 2 A, starKap R E A c₂ = starKap R E A c := by
  have htop : (⨆ n, wtEqL R 𝒱 n A) = ⊤ := iSup_wtEqL A
  have hc2 := ((htop.symm.trans (iSup_split_single (fun n => wtEqL R 𝒱 n A) 2)).le :
    (⊤ : Submodule R (Cut R E A)) ≤ _) (Submodule.mem_top (x := c))
  obtain ⟨c₂, hc₂, c', hc', hce⟩ := Submodule.mem_sup.1 hc2
  have hk : starKap R E A c' = 0 :=
    (iSup₂_le fun n hn w hw => LinearMap.mem_ker.2 (star_wtEqL hn hw) :
      (⨆ (n : ℕ) (_ : n ≠ 2), wtEqL R 𝒱 n A) ≤ LinearMap.ker (starKap R E A)) hc'
  exact ⟨c₂, hc₂, ((add_zero _).symm.trans (congrArg (_ + ·) hk.symm)).trans
    ((map_add _ _ _).symm.trans (congrArg _ hce))⟩

/-- **Every combination of trees with two vertices of `T(E)` is a value of `κ_T ⋆ κ_T` on the
trees with two vertices of `T^c(sE)`**, over a field of characteristic zero, when there are no
generators without inputs. -/
theorem exists_starKap [CharZero R] (hE0 : ∀ v : E (Fin 0), v = 0) {z : FreeGrL R E A}
    (hz : z ∈ vx R E 2 A) : ∃ y ∈ wtEqL R 𝒱 2 A, starKap R E A y = z := by
  obtain ⟨c, hc⟩ := Cobar.exists_eq_d_ιL (lamHom_mem_vx hz) (lamHom_eq_d_hM hE0 hz)
  obtain ⟨c₂, hc₂, he⟩ := exists_wtEqL_two_starKap (-c)
  refine ⟨c₂, hc₂, he.trans ?_⟩
  calc starKap R E A (-c) = -starKap R E A c := map_neg _ _
    _ = -(kapHom R E).app A (ConvOp.toLin ((Cobar.ιι R 𝒞).1 A) c) :=
        congrArg Neg.neg (kapHom_ιι c).symm
    _ = (kapHom R E).app A (-ConvOp.toLin ((Cobar.ιι R 𝒞).1 A) c) := (map_neg _ _).symm
    _ = (kapHom R E).app A ((Cobar.d R 𝒞).app A (Cobar.ιL R 𝒞 A c)) :=
        congrArg _ (Cobar.d_ιL R 𝒞 c).symm
    _ = (kapHom R E).app A ((lamHom R E).app A z) := congrArg _ hc.symm
    _ = z := kapHom_lamHom z

lemma starKap_mem_wtEqL [CharZero R] (x : Cut R E A) : starKap R E A x ∈ wtEqL R E 2 A :=
  (wtEqL_eq_vx 2).ge (star_mem_vx x)

variable (R E) in
/-- **`κ_T ⋆ κ_T` is a linear equivalence `T^c(sE)^{(2)} ≃ T(E)^{(2)}`** between the trees with
two vertices, over a field of characteristic zero, when there are no generators without inputs:
a generator without inputs at the top of a tree with two vertices has no inputs above it, so the
convolution square, which sums over the decompositions with an inner operation with inputs, does
not see that cut. -/
noncomputable def starEquiv [CharZero R] (hE0 : ∀ v : E (Fin 0), v = 0) (A : Type) [Fintype A]
    [DecidableEq A] : wtEqL R 𝒱 2 A ≃ₗ[R] wtEqL R E 2 A :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict (wtEqL R E 2 A) (starKap R E A ∘ₗ (wtEqL R 𝒱 2 A).subtype)
      fun y => starKap_mem_wtEqL y.1)
    ⟨fun y y' h => Subtype.ext (sub_eq_zero.1 (eq_zero_of_starKap_eq_zero hE0 (sub_mem y.2 y'.2)
        ((map_sub _ _ _).trans (sub_eq_zero.2 (congrArg Subtype.val h))))),
     fun z => by
      obtain ⟨y, hy, he⟩ := exists_starKap hE0 (wtEqL_le_vx 2 z.2)
      exact ⟨⟨y, hy⟩, Subtype.ext he⟩⟩

lemma starEquiv_apply [CharZero R] (hE0 : ∀ v : E (Fin 0), v = 0)
    (y : wtEqL R 𝒱 2 A) : (starEquiv R E hE0 A y : FreeGrL R E A) = starKap R E A y := rfl

/-- **`κ_T ⋆ κ_T` is a bijection from the trees with two vertices of `T^c(sE)` onto those of
`T(E)`**, over a field of characteristic zero, when there are no generators without inputs. -/
theorem bijOn_starKap [CharZero R] (hE0 : ∀ v : E (Fin 0), v = 0) :
    Set.BijOn (starKap R E A) (wtEqL R 𝒱 2 A) (wtEqL R E 2 A) :=
  ⟨fun y _ => starKap_mem_wtEqL y,
   fun y hy y' hy' h => sub_eq_zero.1 (eq_zero_of_starKap_eq_zero hE0 (sub_mem hy hy')
     ((map_sub _ _ _).trans (sub_eq_zero.2 h))),
   fun z hz => by
    obtain ⟨y, hy, he⟩ := exists_starKap hE0 (wtEqL_le_vx 2 hz)
    exact ⟨y, hy, he⟩⟩

/-! ### The corelations are the image of the relations -/

variable (r : ∀ n : ℕ, Set (FreeGrL R E (Fin n)))

/-- **`κ_T ⋆ κ_T` maps the corelations onto the relations**: `(κ_T ⋆ κ_T)(s²R) = R`, for quadratic
relators over a field of characteristic zero, when there are no generators without inputs. -/
theorem map_coRel [CharZero R] (hq : IsQuadratic R E r) (hE0 : ∀ v : E (Fin 0), v = 0) :
    (coRel R E r A).map (starKap R E A) = relSp R E r A := by
  refine le_antisymm ?_ fun ρ hρ => ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  · obtain ⟨y, hy, he⟩ := exists_starKap hE0 (relSp_le_vx hq hρ)
    refine ⟨y, ⟨hy, ?_⟩, he⟩
    show starKap R E A y ∈ relSp R E r A
    rw [he]
    exact hρ

variable (R E) in
/-- **The corelations are isomorphic to the relations** by `κ_T ⋆ κ_T`: `s²R ≅ R`, for quadratic
relators over a field of characteristic zero, when there are no generators without inputs. So
`s²R` is the image of `R` under the inverse of `starEquiv`. -/
noncomputable def coRelEquiv [CharZero R] (hq : IsQuadratic R E r)
    (hE0 : ∀ v : E (Fin 0), v = 0) (A : Type) [Fintype A] [DecidableEq A] :
    coRel R E r A ≃ₗ[R] relSp R E r A :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict (relSp R E r A) (starKap R E A ∘ₗ (coRel R E r A).subtype)
      fun y => y.2.2)
    ⟨fun y y' h => Subtype.ext (sub_eq_zero.1 (eq_zero_of_starKap_eq_zero hE0 (sub_mem y.2.1 y'.2.1)
        ((map_sub _ _ _).trans (sub_eq_zero.2 (congrArg Subtype.val h))))),
     fun ρ => by
      obtain ⟨y, hy, he⟩ := (map_coRel r hq hE0).ge ρ.2
      exact ⟨⟨y, hy⟩, Subtype.ext he⟩⟩

lemma coRelEquiv_apply [CharZero R] (hq : IsQuadratic R E r)
    (hE0 : ∀ v : E (Fin 0), v = 0) (y : coRel R E r A) :
    (coRelEquiv R E r hq hE0 A y : FreeGrL R E A) = starKap R E A y := rfl

/-! ### The corelations lie in the Koszul dual cooperad -/

/-- **`κ_T ⋆ κ_T` is even.** -/
lemma starKap_par (b : Bool) (x : Cut R E A) :
    starKap R E A (GrSpecies.par (R := R) b x) = GrOperad.par (R := R) b (starKap R E A x) := by
  have h := ConvOp.parC_eq_self_iff.1 (GrOperad.Inv.isPar_star (isPar_kapT (R := R) (E := E))
    (isPar_kapT (R := R) (E := E)) A) b x
  exact h.trans (by cases b <;> rfl)

lemma par_mem_coRel (b : Bool) {x : Cut R E A} (hx : x ∈ coRel R E r A) :
    GrSpecies.par (R := R) b x ∈ coRel R E r A :=
  ⟨par_mem_wtEqL b hx.1, show starKap R E A (GrSpecies.par (R := R) b x) ∈ relSp R E r A by
    rw [starKap_par]
    exact par_mem_relSp b hx.2⟩

lemma map_mem_coRel {B : Type} [Fintype B] [DecidableEq B] (σ' : A ≃ B) {x : Cut R E A}
    (hx : x ∈ coRel R E r A) : SymSpecies.map (R := R) σ' x ∈ coRel R E r B :=
  ⟨by rw [symMap_eq]; exact map_mem_wtEqL σ' hx.1,
   show starKap R E B (SymSpecies.map (R := R) σ' x) ∈ relSp R E r B by
    rw [starKap, GrOperad.Inv.toLin_map]
    exact map_mem_relSp σ' hx.2⟩

/-- The part `1 ⊗ s²R` of the decomposition of a corelation. -/
lemma decomp_left_mem [CharZero R] {B : Type} [Fintype B] [DecidableEq B] (i : A)
    {x : Cut R E (Without A i ⊕ B)} (hx : x ∈ coRel R E r _)
    {t₀ t₁ t₂ : Cut R E A ⊗[R] Cut R E B}
    (h₀ : t₀ ∈ LinearMap.range (TensorProduct.map (wtEqL R 𝒱 0 A).subtype
      (wtEqL R 𝒱 2 B).subtype))
    (h₁ : t₁ ∈ LinearMap.range (TensorProduct.map (wtEqL R 𝒱 1 A).subtype
      (wtEqL R 𝒱 1 B).subtype))
    (h₂ : t₂ ∈ LinearMap.range (TensorProduct.map (wtEqL R 𝒱 2 A).subtype
      (wtEqL R 𝒱 0 B).subtype))
    (ht : GrCooperad.decomp (R := R) (C := 𝒞) i x = t₀ + t₁ + t₂) :
    t₀ ∈ LinearMap.range (TensorProduct.map (wtOneL R 𝒱 A ⊔ coRel R E r A).subtype
      (wtOneL R 𝒱 B ⊔ coRel R E r B).subtype) := by
  by_cases hA : ∀ a : A, a = i
  · obtain ⟨τ, hτ⟩ := GrCooperad.exists_lid_counit_decomp (R := R) (C := 𝒞) i hA x
    set u := SymSpecies.map (R := R) (unitEquivOf i hA)
      (GrCooperad.Coaug.one (R := R) (C := 𝒞))
    set ε := GrCooperad.counit (R := R) (C := 𝒞) ∘ₗ
      SymSpecies.map (R := R) (unitEquivOf i hA).symm
    have hu : ε u = 1 := counit_map_map_one _
    obtain ⟨hy, hte⟩ := eq_tmul_of_mem_range_left hu (wtEqL_zero_le_span i hA) h₀
    have k₁ : LinearMap.rTensor _ ε t₁ = 0 := rTensor_eq_zero_of_le_ker (ε := ε)
      (fun p hp => LinearMap.mem_ker.2 (counit_map_wtEqL one_ne_zero _ hp)) h₁
    have k₂ : LinearMap.rTensor _ ε t₂ = 0 := rTensor_eq_zero_of_le_ker (ε := ε)
      (fun p hp => LinearMap.mem_ker.2 (counit_map_wtEqL two_ne_zero _ hp)) h₂
    have hy' : TensorProduct.lid R _ (LinearMap.rTensor _ ε t₀) ∈ coRel R E r B := by
      have e : TensorProduct.lid R _ (LinearMap.rTensor _ ε t₀) = SymSpecies.map (R := R) τ x := by
        rw [← hτ, ht]
        simp only [map_add, k₁, k₂, add_zero]
      rw [e]
      exact map_mem_coRel r τ hx
    have hu' : u ∈ wtOneL R 𝒱 A ⊔ coRel R E r A :=
      Submodule.mem_sup_left (wtEqL_le_wtOneL (n := 0) zero_le_one
        ((wtEqL_eq_vx 0).ge (Cobar.unitSpan_le_vx (GrCooperad.map_one_mem _))))
    rw [hte]
    exact ⟨⟨u, hu'⟩ ⊗ₜ ⟨_, Submodule.mem_sup_right hy'⟩, rfl⟩
  · have hE : IsEmpty (Unit ≃ A) := ⟨fun e => hA fun a =>
      e.symm.injective (Subsingleton.elim _ _)⟩
    rw [eq_zero_of_mem_range_bot_left (wtEqL_zero_eq_bot hE) h₀]
    exact zero_mem _

/-- The part `s²R ⊗ 1` of the decomposition of a corelation. -/
lemma decomp_right_mem [CharZero R] {B : Type} [Fintype B] [DecidableEq B] (i : A)
    {x : Cut R E (Without A i ⊕ B)} (hx : x ∈ coRel R E r _)
    {t₀ t₁ t₂ : Cut R E A ⊗[R] Cut R E B}
    (h₀ : t₀ ∈ LinearMap.range (TensorProduct.map (wtEqL R 𝒱 0 A).subtype
      (wtEqL R 𝒱 2 B).subtype))
    (h₁ : t₁ ∈ LinearMap.range (TensorProduct.map (wtEqL R 𝒱 1 A).subtype
      (wtEqL R 𝒱 1 B).subtype))
    (h₂ : t₂ ∈ LinearMap.range (TensorProduct.map (wtEqL R 𝒱 2 A).subtype
      (wtEqL R 𝒱 0 B).subtype))
    (ht : GrCooperad.decomp (R := R) (C := 𝒞) i x = t₀ + t₁ + t₂) :
    t₂ ∈ LinearMap.range (TensorProduct.map (wtOneL R 𝒱 A ⊔ coRel R E r A).subtype
      (wtOneL R 𝒱 B ⊔ coRel R E r B).subtype) := by
  by_cases hB : Nonempty (Unit ≃ B)
  · obtain ⟨e₀⟩ := hB
    have hB' : ∀ b : B, b = e₀ () := fun b => e₀.symm.injective (Subsingleton.elim _ _)
    obtain ⟨τ, hτ⟩ := GrCooperad.exists_rid_counit_decomp (R := R) (C := 𝒞) i (e₀ ()) hB' x
    set u := SymSpecies.map (R := R) (unitEquivOf (e₀ ()) hB')
      (GrCooperad.Coaug.one (R := R) (C := 𝒞))
    set ε := GrCooperad.counit (R := R) (C := 𝒞) ∘ₗ
      SymSpecies.map (R := R) (unitEquivOf (e₀ ()) hB').symm
    have hu : ε u = 1 := counit_map_map_one _
    obtain ⟨hy, hte⟩ := eq_tmul_of_mem_range_right hu (wtEqL_zero_le_span (e₀ ()) hB') h₂
    have k₀ : LinearMap.lTensor _ ε t₀ = 0 := lTensor_eq_zero_of_le_ker (ε := ε)
      (fun p hp => LinearMap.mem_ker.2 (counit_map_wtEqL two_ne_zero _ hp)) h₀
    have k₁ : LinearMap.lTensor _ ε t₁ = 0 := lTensor_eq_zero_of_le_ker (ε := ε)
      (fun p hp => LinearMap.mem_ker.2 (counit_map_wtEqL one_ne_zero _ hp)) h₁
    have hy' : TensorProduct.rid R _ (LinearMap.lTensor _ ε t₂) ∈ coRel R E r A := by
      have e : TensorProduct.rid R _ (LinearMap.lTensor _ ε t₂) = SymSpecies.map (R := R) τ x := by
        rw [← hτ, ht]
        simp only [map_add, k₀, k₁, zero_add]
      rw [e]
      exact map_mem_coRel r τ hx
    have hu' : u ∈ wtOneL R 𝒱 B ⊔ coRel R E r B :=
      Submodule.mem_sup_left (wtEqL_le_wtOneL (n := 0) zero_le_one
        ((wtEqL_eq_vx 0).ge (Cobar.unitSpan_le_vx (GrCooperad.map_one_mem _))))
    rw [hte]
    exact ⟨⟨_, Submodule.mem_sup_right hy'⟩ ⊗ₜ ⟨u, hu'⟩, rfl⟩
  · rw [eq_zero_of_mem_range_bot_right (wtEqL_zero_eq_bot (not_nonempty_iff.1 hB)) h₂]
    exact zero_mem _

/-- **The decomposition of a corelation** lies in `(T^c(sE)^{(≤1)} + s²R)^{⊗2}`: its parts with one
vertex on each side have at most one vertex, and its parts with a unit on one side are a unit
tensored with a relabelled corelation, by the counit laws. -/
lemma decomp_mem_coRel [CharZero R] {B : Type} [Fintype B] [DecidableEq B] (i : A)
    {x : Cut R E (Without A i ⊕ B)} (hx : x ∈ coRel R E r _) :
    GrCooperad.decomp (R := R) (C := 𝒞) i x
      ∈ LinearMap.range (TensorProduct.map (wtOneL R 𝒱 A ⊔ coRel R E r A).subtype
        (wtOneL R 𝒱 B ⊔ coRel R E r B).subtype) := by
  obtain ⟨t₀, h₀, t₁, h₁, t₂, h₂, ht⟩ := exists_split_two (decomp_mem_wtEqL i hx.1)
  rw [ht]
  refine add_mem (add_mem (decomp_left_mem r i hx h₀ h₁ h₂ ht) ?_)
    (decomp_right_mem r i hx h₀ h₁ h₂ ht)
  exact GrSubCooperad.range_map_subtype_mono (C := 𝒞)
    ((wtEqL_le_wtOneL le_rfl).trans le_sup_left) ((wtEqL_le_wtOneL le_rfl).trans le_sup_left) h₁

variable (R E) in
/-- **The trees with at most one vertex and the corelations form a subcooperad** of `T^c(sE)`,
over a field of characteristic zero. -/
noncomputable def coRelSub [CharZero R] : GrSubCooperad R 𝒞 where
  sub A _ _ := wtOneL R 𝒱 A ⊔ coRel R E r A
  par_mem := by
    intro A _ _ b x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact add_mem (Submodule.mem_sup_left ((wtOneSub R 𝒱).par_mem b hy))
      (Submodule.mem_sup_right (par_mem_coRel r b hz))
  map_mem := by
    intro A B _ _ _ _ e x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact add_mem (Submodule.mem_sup_left ((wtOneSub R 𝒱).map_mem e hy))
      (Submodule.mem_sup_right (map_mem_coRel r e hz))
  decomp_mem := by
    intro A B _ _ _ _ i x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact add_mem (GrSubCooperad.range_map_subtype_mono (C := 𝒞) le_sup_left le_sup_left
      ((wtOneSub R 𝒱).decomp_mem i hy)) (decomp_mem_coRel r i hz)

/-- **The corelations lie in the Koszul dual cooperad**: `s²R ⊆ P^¡`, over a field of
characteristic zero. -/
theorem coRel_le_dual [CharZero R] : coRel R E r A ≤ (dualSub R E r).sub A :=
  le_sup_right.trans (le_dualSub r (K := coRelSub R E r) (fun A _ _ x hx => by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    show starKap R E A (y + z) ∈ (GrOperadIdeal.span R r).sub A
    rw [map_add]
    exact add_mem ((star_wtOne hy).symm ▸ zero_mem _) (relSp_le_ideal hz.2)) A)

/-- **The trees with two vertices of the Koszul dual cooperad are the corelations**:
`P^¡ ∩ T^c(sE)^{(2)} = s²R`, for quadratic relators over a field of characteristic zero. -/
theorem dual_inf_wtEqL [CharZero R] (hq : IsQuadratic R E r) :
    (dualSub R E r).sub A ⊓ wtEqL R 𝒱 2 A = coRel R E r A :=
  le_antisymm (dual_inf_wtEqL_le hq) (le_inf (coRel_le_dual r) inf_le_left)


end Koszul

end Koszul

end Operad
