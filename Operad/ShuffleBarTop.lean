/-
# The comparison morphism onto the top cycles

Step (2c) of the bridge between symmetric and shuffle operads (Dotsenko–Khoroshkin), third part.
For `E` with an even basis `c k` indexed by `BinGen G k`, relators `r` with at least three inputs,
`P = Koszul.Pres K E r` and its ideal `Ī_P` of the operations with at least two inputs, **the
comparison morphism `P^¡(n) → B(P, Ī_P)(Fin n)` maps onto the cycles with `n - 1` vertices**, over a
field of characteristic zero (`ShuffleBarSym.toBar_surj_top`). This is the hypothesis `htop` of
`ShuffleBarSym.isKoszul_iff_shuffle_of`.

* **Linear algebra over a field** (`TensorProduct.mem_range_map_ker`,
  `TensorProduct.mem_range_of_coderiv`): an element of `M ⊗ N` killed by `g ⊗ 1` and `1 ⊗ h`
  lies in `ker g ⊗ ker h`, by flatness; and the two terms `(d f ⊗ f)(t)`, `(τ f ⊗ d f)(t)` of a
  coderivation vanish separately when they are eigenvectors of the vertex count for `a - 2` and
  `a - 1`.
* **The cycles along a morphism of cooperads into the top degree** (`Bar.cycSub`): for an
  injective morphism of graded cooperads `f : C → B(P, I)` landing in the trees with `|A| - 1`
  vertices, the elements `y` with `d (f y) = 0` form a subcooperad (`Bar.decomp_mem_cyc`, by the
  coderivation rule `Δ d = (d ⊗ 1 + τ ⊗ d) Δ`). On them `π ⋆ π` vanishes
  (`Bar.toLin_star_pi_of_d`, the Maurer–Cartan equation of `π`), so for
  `f = T^c(sE) → B(P, I)` (`Koszul.cutBar`, with `π ∘ f = κ_T` projected, `Koszul.pi_cutBar`)
  **`κ_T ⋆ κ_T` lands in the ideal of the relators** (`Koszul.star_mem_of_d`).
* **Trees with only binary vertices** (`FreeGrL.mapSp_trunc_of_top`, `FreeGrL.mapSp_eq_of_top`):
  on a species vanishing in arities at most one, the trees of `T(V)(A)` with `|A| - 1` vertices
  are fixed by the truncation to the arities at most two, so morphisms agreeing on the generators
  with at most two inputs agree on them.
* **The binary case** (`ShuffleBarSym.cutCyc`, `ShuffleBarSym.cutCyc_le`): `T^c(sE) → B(P, Ī_P)`
  is injective and lands in the top degree, so its cycles are a subcooperad inside `P^¡`
  (`Koszul.le_dualSub`); a top cycle `z` of `B(P, Ī_P)` has only binary vertices, on which
  `sĪ_P → sE → sĪ_P` is the identity (`ShuffleBarSym.barGen_barRet`), so `z` is the image of a
  cycle of `T^c(sE)`, hence of an element of `P^¡`.

Consequently **`P` is Koszul iff the homology of `B(T, Ī)(Fin n)` modulo `Krel` vanishes below the
top degree for every `n ≥ 2`** (`ShuffleBarSym.isKoszul_iff_free_lower`), and **`P` is Koszul iff
`ShuffleBar.IsKoszul K R`, given only `ΦL (Krel) = ShuffleBar.J K R ⊓ supported (barSet G n)`**
(`ShuffleBarSym.isKoszul_iff_shuffle_of_J`). That identification for the shuffle relators
`ShuffleBarSym.Rsh`, for relators of arity three stable under the permutations of `Fin 3`, is
proved in `Operad/ShuffleBarJ.lean` (`ShuffleBarSym.map_ΦL_Krel`), which gives the bridge
`ShuffleBarSym.isKoszul_iff_shuffle`.
-/
import Operad.ShuffleBarProj

universe u v

open scoped TensorProduct

/-- **Over a field, an element of `M ⊗ N` killed by `g ⊗ 1` and by `1 ⊗ h` lies in
`ker g ⊗ ker h`.** -/
theorem TensorProduct.mem_range_map_ker {K : Type*} [Field K] {M N M' N' : Type*}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] [AddCommGroup M'] [Module K M']
    [AddCommGroup N'] [Module K N'] (g : M →ₗ[K] M') (h : N →ₗ[K] N') {t : M ⊗[K] N}
    (h1 : LinearMap.rTensor N g t = 0) (h2 : LinearMap.lTensor M h t = 0) :
    t ∈ LinearMap.range
      (TensorProduct.map (LinearMap.ker g).subtype (LinearMap.ker h).subtype) := by
  obtain ⟨u, rfl⟩ := ((Module.Flat.rTensor_exact N g.exact_subtype_ker_map).linearMap_ker_eq ▸
    (LinearMap.mem_ker.2 h1) : t ∈ LinearMap.range _)
  have hu : LinearMap.lTensor (LinearMap.ker g) h u = 0 := by
    refine Module.Flat.rTensor_preserves_injective_linearMap (M := N') _
      (LinearMap.ker g).injective_subtype ?_
    rw [map_zero, ← h2, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
      LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  obtain ⟨v, rfl⟩ := ((Module.Flat.lTensor_exact (LinearMap.ker g)
    h.exact_subtype_ker_map).linearMap_ker_eq ▸ (LinearMap.mem_ker.2 hu) : u ∈ LinearMap.range _)
  refine ⟨v, ?_⟩
  rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor]

/-- **The kernel of a coderivation-type sum, over a field**: for injective `f_A`, `f_B`, if
`W` is `a - 2` on `d_A f_A` and `a - 1` on `f_A`, and `τ f_A = f_A τ'` with `τ'` an involution,
then `(d_A ⊗ 1 + τ ⊗ d_B)(f_A ⊗ f_B)(t) = 0` forces `t ∈ ker (d_A f_A) ⊗ ker (d_B f_B)`. -/
theorem TensorProduct.mem_range_of_coderiv {K : Type*} [Field K] {M N M' N' : Type*}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] [AddCommGroup M'] [Module K M']
    [AddCommGroup N'] [Module K N'] (fA : M →ₗ[K] M') (fB : N →ₗ[K] N') (dA W τ : M' →ₗ[K] M')
    (dB : N' →ₗ[K] N') (τ' : M →ₗ[K] M) (a : K) (hfA : Function.Injective fA)
    (hfB : Function.Injective fB) (hτ' : ∀ y, τ' (τ' y) = y) (hτ : ∀ y, τ (fA y) = fA (τ' y))
    (hW1 : ∀ y, W (dA (fA y)) = (a - 2) • dA (fA y)) (hW2 : ∀ y, W (fA y) = (a - 1) • fA y)
    {t : M ⊗[K] N}
    (h0 : TensorProduct.map dA LinearMap.id (TensorProduct.map fA fB t)
      + TensorProduct.map τ dB (TensorProduct.map fA fB t) = 0) :
    t ∈ LinearMap.range (TensorProduct.map (LinearMap.ker (dA ∘ₗ fA)).subtype
      (LinearMap.ker (dB ∘ₗ fB)).subtype) := by
  have hk : τ ∘ₗ fA = fA ∘ₗ τ' := LinearMap.ext hτ
  rw [← LinearMap.comp_apply (TensorProduct.map dA _),
    ← LinearMap.comp_apply (TensorProduct.map τ _), ← TensorProduct.map_comp,
    ← TensorProduct.map_comp, hk, LinearMap.id_comp] at h0
  have hW1' : W ∘ₗ (dA ∘ₗ fA) = (a - 2) • (dA ∘ₗ fA) := LinearMap.ext hW1
  have hW2' : W ∘ₗ (fA ∘ₗ τ') = (a - 1) • (fA ∘ₗ τ') := LinearMap.ext fun y => hW2 (τ' y)
  have h3 := congrArg (LinearMap.rTensor N' W) h0
  rw [map_add, map_zero, ← LinearMap.comp_apply (LinearMap.rTensor _ _),
    ← LinearMap.comp_apply (LinearMap.rTensor _ _), LinearMap.rTensor_comp_map,
    LinearMap.rTensor_comp_map, hW1', hW2', TensorProduct.map_smul_left,
    TensorProduct.map_smul_left, LinearMap.smul_apply, LinearMap.smul_apply,
    eq_neg_of_add_eq_zero_right h0, smul_neg, ← sub_eq_add_neg, ← sub_smul,
    show (a - 2) - (a - 1) = -1 by ring, neg_one_smul, neg_eq_zero] at h3
  have hV := eq_neg_of_add_eq_zero_right h0
  rw [h3, neg_zero] at hV
  have hinj : Function.Injective (fA ∘ₗ τ') := fun y y' h => by
    have := congrArg τ' (hfA h)
    rwa [hτ', hτ'] at this
  refine TensorProduct.mem_range_map_ker _ _ ?_ ?_
  · refine Module.Flat.lTensor_preserves_injective_linearMap (M := M') _ hfB ?_
    rw [map_zero, ← h3, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor]
  · refine Module.Flat.rTensor_preserves_injective_linearMap (M := N') _ hinj ?_
    rw [map_zero, ← hV, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor]

namespace Operad

open Sym GerBV

namespace FreeGrL

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V] [Algebra ℚ R]
  (hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ v : V B, v = 0)
include hred

/-- **The truncation to the arities at most two is the identity on the trees with `|A| - 1`
vertices**, the trees whose vertices all have two inputs. -/
theorem mapSp_trunc_of_top {A : Type} [Fintype A] [DecidableEq A] (hA : 1 ≤ Fintype.card A)
    {x : FreeGrL R V A} (hx : x ∈ vx R V (Fintype.card A - 1) A) :
    (mapSp (GrSpEnd.trunc R V 2).toHom).app A x = x := by
  set τ := GrSpEnd.trunc R V 2
  have hτ : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : V A), τ.app A (τ.app A x) = τ.app A x :=
    GrSpEnd.trunc_trunc 2
  have hBN : ∀ y, (derSp (GrSpEnd.compl R V τ)).app A ((derSp (GrSpEnd.id R V)).app A y)
      = (derSp (GrSpEnd.id R V)).app A ((derSp (GrSpEnd.compl R V τ)).app A y) := fun y => by
    have := derSp_comm (a := GrSpEnd.compl R V τ) (b := GrSpEnd.id R V)
      (fun A _ _ v => by simp only [GrSpEnd.id_app, Bool.false_and, σ_false, one_smul]) y
    rwa [Bool.false_and, σ_false, one_smul] at this
  have htopB := iSup_eig_eq_top (a := GrSpEnd.compl R V τ) (fun A _ _ v => mem_iSup_compl τ hτ v) A
  have hy : (derSp (GrSpEnd.id R V)).app A (x - (mapSp τ.toHom).app A x)
      = ((Fintype.card A - 1 : ℕ) : R) • (x - (mapSp τ.toHom).app A x) := by
    rw [map_sub, mapSp_derSp_comm (a := GrSpEnd.id R V) (φ := τ) (fun A _ _ v => rfl), mem_eig.1 hx,
      map_smul, smul_sub]
  obtain ⟨f, hf, hfN, hfs⟩ := exists_finsupp_eig_inf _ _ hBN htopB _ hy
  have hf0 : ∀ j, j ≠ 0 → f j = 0 := fun j hj => by
    have htopQ := iSup_eig_scalar hred
      (fun n => ((n : R) - 2) - (1 - if n ≤ 2 then 1 else 0))
      (fun n hn => by
        by_cases h : n ≤ 2
        · exact ⟨n - 2, by
            beta_reduce
            rw [if_pos h, Nat.cast_sub hn]
            ring⟩
        · exact ⟨n - 3, by
            beta_reduce
            rw [if_neg h, Nat.cast_sub (by omega)]
            push_cast
            ring⟩) A
    refine eq_zero_of_eigen_neg R _ htopQ (m := j) hj ?_
    rw [derSp_lin (GrSpEnd.scalar R V fun n => (n : R) - 2) (GrSpEnd.compl R V τ) _ 1 (-1)
      (fun A _ _ v => by
        simp only [GrSpEnd.scalar_app, GrSpEnd.compl_app, τ, GrSpEnd.trunc_app]
        module) (f j),
      derSp_lin (GrSpEnd.scalar R V fun n => (n : R) - 1) (GrSpEnd.id R V) _ 1 (-1)
        (fun A _ _ v => by simp only [GrSpEnd.scalar_app, GrSpEnd.id_app]; module) (f j),
      derSp_excess, hfN j, Module.End.mem_eigenspace_iff.1 (hf j), Nat.cast_sub hA]
    push_cast
    module
  have hyf : x - (mapSp τ.toHom).app A x = f 0 := by
    rw [← hfs]
    exact Finsupp.sum_eq_single 0 (fun j _ hj => hf0 j hj) (fun _ => rfl)
  have h0 : x - (mapSp τ.toHom).app A x
      ∈ Module.End.eigenspace ((derSp (GrSpEnd.compl R V τ)).app A) ((0 : ℕ) : R) :=
    hyf ▸ hf 0
  have h1 : x - (mapSp τ.toHom).app A x
      ∈ ⨆ (j : ℕ) (_ : j ≠ 0), eig R V (GrSpEnd.compl R V τ) j A :=
    (iSup_le fun j => le_iSup₂_of_le (f := fun (i : ℕ) (_ : i ≠ 0) =>
      eig R V (GrSpEnd.compl R V τ) i A) (j + 1) (by omega) le_rfl) (sub_mapSp_mem τ hτ x)
  have := Submodule.disjoint_def.1 (iSupIndep_eigenspace_nat _ 0) _ h0 h1
  exact (sub_eq_zero.1 this).symm

/-- **Morphisms agreeing on the generators with at most two inputs agree on the trees with
`|A| - 1` vertices.** -/
theorem mapSp_eq_of_top {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)] [GrSpecies R W]
    {g g' : GrSpeciesHom R V W}
    (hg : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 2 →
      ∀ v : V B, g.app B v = g'.app B v)
    {A : Type} [Fintype A] [DecidableEq A] (hA : 1 ≤ Fintype.card A)
    {x : FreeGrL R V A} (hx : x ∈ vx R V (Fintype.card A - 1) A) :
    (mapSp g).app A x = (mapSp g').app A x := by
  rw [← mapSp_trunc_of_top hred hA hx, mapSp_comp, mapSp_comp]
  refine mapSp_congr (fun B _ _ v => ?_) _
  rw [GrSpeciesHom.comp_app, GrSpeciesHom.comp_app, GrSpEnd.toHom_app, GrSpEnd.trunc_app]
  rcases le_or_gt (Fintype.card B) 2 with h | h
  · rw [if_pos h, one_smul, hg B h]
  · rw [if_neg (by omega), zero_smul, map_zero, map_zero]

end FreeGrL

namespace Bar

variable {R : Type u} [Field R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  (I : GrOperadIdeal R P) {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  (f : GrCooperadHom R C (FreeGrL R (BarGen I)))
  (hf : ∀ (A : Type) [Fintype A] [DecidableEq A], Function.Injective (f.app A))
  (hdeg : ∀ (A : Type) [Fintype A] [DecidableEq A], 1 ≤ Fintype.card A → ∀ y : C A,
    f.app A y ∈ FreeGrL.vx R (BarGen I) (Fintype.card A - 1) A)

local notation "𝒞" => FreeGrL R (BarGen I)

include hdeg in
/-- On the image of a morphism into the trees with `|A| - 1` vertices, the vertex count of a
boundary is `|A| - 2`. -/
lemma wtD_d_app {A : Type} [Fintype A] [DecidableEq A] (hA : 1 ≤ Fintype.card A) (y : C A) :
    (FreeGrL.wtD R (BarGen I)).app A (d I A (f.app A y))
      = ((Fintype.card A : R) - 2) • d I A (f.app A y) := by
  have h := FreeGrL.mem_eig.1 (hdeg A hA y)
  rw [wtD_d, Cobar.wtD_eq_derSp, h, map_smul, Nat.cast_sub hA, Nat.cast_one]
  module

/-- A morphism of graded cooperads commutes with the sign twist. -/
lemma app_tw {A : Type} [Fintype A] [DecidableEq A] (y : C A) :
    f.app A (GrSpecies.tw (R := R) true y)
      = ((GrSpecies.par (R := R) (V := FreeGrL R (BarGen I)) (A := A) false
        - GrSpecies.par (R := R) (V := FreeGrL R (BarGen I)) (A := A) true :
          FreeGrL R (BarGen I) A →ₗ[R] FreeGrL R (BarGen I) A) (f.app A y)) := by
  rw [GrSpecies.tw_apply, σ_true, neg_one_smul, map_add, map_neg, f.app_par, f.app_par,
    LinearMap.sub_apply, sub_eq_add_neg]

include hf hdeg in
/-- **The cycles along an injective morphism into the trees with `|A| - 1` vertices are closed
under the decompositions**: by the coderivation rule, `d ⊗ 1` and `1 ⊗ d` kill the
decomposition of a cycle separately, their values having different vertex counts. -/
theorem decomp_mem_cyc {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (i : A) {x : C (Without A i ⊕ B)} (hx : d I _ (f.app _ x) = 0) :
    GrCooperad.decomp (R := R) i x ∈ LinearMap.range (TensorProduct.map
      (LinearMap.ker (d I A ∘ₗ f.app A)).subtype (LinearMap.ker (d I B ∘ₗ f.app B)).subtype) := by
  have hA : 1 ≤ Fintype.card A := Fintype.card_pos_iff.2 ⟨i⟩
  have e : GrCooperad.decomp (R := R) (C := 𝒞) i (d I _ (f.app _ x))
      = TensorProduct.map (d I A) LinearMap.id (GrCooperad.decomp (R := R) (C := 𝒞) i (f.app _ x))
        + TensorProduct.map (GrSpecies.par (R := R) (V := 𝒞) false
          - GrSpecies.par (R := R) (V := 𝒞) true) (d I B)
            (GrCooperad.decomp (R := R) (C := 𝒞) i (f.app _ x)) :=
    (instDGCooperad I).decomp_d i (f.app _ x)
  have e2 := LinearMap.congr_fun (f.decomp_app i) x
  simp only [LinearMap.comp_apply] at e2
  refine TensorProduct.mem_range_of_coderiv (f.app A) (f.app B) (d I A)
    ((FreeGrL.wtD R (BarGen I)).app A) (GrSpecies.par (R := R) (V := 𝒞) false
      - GrSpecies.par (R := R) (V := 𝒞) true) (d I B) (GrSpecies.tw (R := R) (V := C) true)
    (Fintype.card A : R) (hf A) (hf B) (fun y => ?_) (fun y => (app_tw I f y).symm)
    (wtD_d_app I f hdeg hA) (fun y => ?_) ?_
  · rw [GrSpecies.tw_tw, Bool.xor_self, GrSpecies.tw_false]
  · rw [Cobar.wtD_eq_derSp, FreeGrL.mem_eig.1 (hdeg A hA _), Nat.cast_sub hA, Nat.cast_one]
  · rw [← e2, ← e, hx, map_zero]

/-- **The cycles along an injective morphism of graded cooperads into the trees with `|A| - 1`
vertices of the bar construction**: the elements `y` with `d (f y) = 0`, a subcooperad. -/
noncomputable def cycSub : GrSubCooperad R C where
  sub A _ _ := LinearMap.ker (d I A ∘ₗ f.app A)
  par_mem {A} _ _ b x hx := by
    rw [LinearMap.mem_ker, LinearMap.comp_apply] at hx ⊢
    rw [f.app_par]
    exact ((instDGCooperad I).d_par b (f.app A x)).trans (by
      show GrSpecies.par (R := R) (V := 𝒞) (!b) (d I A (f.app A x)) = 0
      rw [hx, map_zero])
  map_mem {A B} _ _ _ _ e x hx := by
    rw [LinearMap.mem_ker, LinearMap.comp_apply] at hx ⊢
    rw [f.app_map]
    exact ((instDGCooperad I).map_d e (f.app A x)).symm.trans (by
      show SymSpecies.map (R := R) (V := 𝒞) e (d I A (f.app A x)) = 0
      rw [hx, map_zero])
  decomp_mem {A B} _ _ _ _ i x hx := decomp_mem_cyc I f hf hdeg i hx

/-- **The convolution square of `π` kills the cycles of the bar construction**, by the
Maurer–Cartan equation of `π`. -/
lemma toLin_star_pi_of_d (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0) {A : Type} [Fintype A]
    [DecidableEq A] (z : 𝒞 A) (hz : d I A z = 0) :
    ConvOp.toLin ((GrOperad.Inv.star R _ (pi I) (pi I)).1 A) z = 0 := by
  have hmc := congrArg (fun q : GrOperad.Inv R (ConvOp R (BarCoop I) (ZeroDG R P)) =>
    ConvOp.toLin (q.1 A) z) (mc_pi I hI0)
  have hz' : DGCooperad.d (R := R) (C := BarCoop I) z = 0 := hz
  have key : (0 : ZeroDG R P A) - ConvOp.toLin (GrOperad.tw (R := R) true ((pi I).1 A))
      (DGCooperad.d (R := R) (C := BarCoop I) z)
      + ConvOp.toLin ((GrOperad.Inv.star R _ (pi I) (pi I)).1 A) z = 0 := hmc
  rw [hz', map_zero, sub_zero, zero_add] at key
  exact key

end Bar

namespace Koszul

variable {R : Type u} [Field R] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (E A)] [GrSpecies R E]
  {r : ∀ n : ℕ, Set (FreeGrL R E (Fin n))} (I : GrOperadIdeal R (Pres R E r))
  (hE : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : E A),
    (GrOperadIdeal.span R r).proj A ((FreeGrL.ι R E).app A v) ∈ I.sub A)

local notation "𝒥" => GrOperadIdeal.span R r

/-- **The morphism of cut cooperads `T^c(sE) → B(P, I)`** induced by `sE → sI`. -/
noncomputable def cutBar : GrCooperadHom R (Cut R E) (BarCoop I) :=
  FreeGrL.mapCoop (barGen I hE)

/-- The morphism `T^c(sE) → B(P, I)`, arity by arity. -/
lemma cutBar_app {A : Type} [Fintype A] [DecidableEq A] (y : Cut R E A) :
    (cutBar I hE).app A y = (FreeGrL.mapSp (barGen I hE)).app A y := rfl

/-- **`π ∘ (T^c(sE) → B(P, I))` is `κ_T` followed by the projection.** -/
lemma pi_cutBar :
    GrOperad.Inv.appHom (ConvOp.preHom (P := ZeroDG R (Pres R E r)) (cutBar I hE)) (Bar.pi I)
      = GrOperad.Inv.appHom (ConvOp.postHom (C := Cut R E)
        (GrOperadHom.toZeroDG (𝒥).projHom)) (kapT R E) :=
  Subtype.ext (funext fun A => funext fun _ => funext fun _ => by
    rw [GrOperad.Inv.appHom_apply, GrOperad.Inv.appHom_apply]
    ext x
    exact piL_mapSp I hE x)

/-- **`κ_T ⋆ κ_T` lands in the ideal of the relators on the cycles along `T^c(sE) → B(P, I)`**:
`π ∘ (T^c(sE) → B(P, I))` is `κ_T` followed by the projection, and `π ⋆ π` kills the cycles. -/
theorem star_mem_of_d (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0) {A : Type} [Fintype A] [DecidableEq A]
    (y : Cut R E A) (hy : Bar.d I A ((FreeGrL.mapSp (barGen I hE)).app A y) = 0) :
    ConvOp.toLin ((GrOperad.Inv.star R _ (kapT R E) (kapT R E)).1 A) y ∈ (𝒥).sub A := by
  rw [← GrOperadIdeal.proj_eq_zero_iff]
  have h : ConvOp.toLin ((GrOperad.Inv.star R _ (Bar.pi I) (Bar.pi I)).1 A)
      ((cutBar I hE).app A y) = 0 := Bar.toLin_star_pi_of_d I hI0 _ hy
  have e1 := GrOperad.Inv.appHom_star (ConvOp.preHom (P := ZeroDG R (Pres R E r))
    (cutBar I hE)) (Bar.pi I) (Bar.pi I)
  have e2 := GrOperad.Inv.appHom_star (ConvOp.postHom (C := Cut R E)
    (GrOperadHom.toZeroDG (𝒥).projHom)) (kapT R E) (kapT R E)
  have e3 := e1.trans ((congrArg₂ (fun a b : GrOperad.Inv R
    (ConvOp R (Cut R E) (ZeroDG R (Pres R E r))) => GrOperad.Inv.star R _ a b) (pi_cutBar I hE)
    (pi_cutBar I hE)).trans e2.symm)
  have h2 := congrArg (fun q : GrOperad.Inv R (ConvOp R (Cut R E) (ZeroDG R (Pres R E r))) =>
    ConvOp.toLin (q.1 A) y) e3
  have hl : ConvOp.toLin ((GrOperad.Inv.appHom (ConvOp.preHom (P := ZeroDG R (Pres R E r))
      (cutBar I hE)) (GrOperad.Inv.star R _ (Bar.pi I) (Bar.pi I))).1 A) y
      = ConvOp.toLin ((GrOperad.Inv.star R _ (Bar.pi I) (Bar.pi I)).1 A)
        ((cutBar I hE).app A y) := rfl
  have hr : ConvOp.toLin ((GrOperad.Inv.appHom (ConvOp.postHom (C := Cut R E)
      (GrOperadHom.toZeroDG (𝒥).projHom)) (GrOperad.Inv.star R _ (kapT R E) (kapT R E))).1 A) y
      = (𝒥).proj A (ConvOp.toLin ((GrOperad.Inv.star R _ (kapT R E) (kapT R E)).1 A) y) := rfl
  exact hr.symm.trans (h2.symm.trans (hl.trans h))

end Koszul

namespace ShuffleBarSym

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {G : Type} [Fintype G] [DecidableEq G]
  (c : ∀ k, Module.Basis (BinGen G k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen G k), GrSpecies.par (R := K) false (c k β) = c k β)
  (r : ∀ n : ℕ, Set (FreeGrL K E (Fin n)))
  (hr2 : ∀ n, n < 3 → r n = ∅)

local notation "𝒥" => GrOperadIdeal.span K r
local notation "𝒱P" => FreeGrL.vx K (BarGen (Ipres K E c hc r))

/-- **The morphism of cut cooperads `T^c(sE) → B(P, Ī_P)`** induced by `sE → sĪ_P`. -/
noncomputable abbrev cutBarP :
    GrCooperadHom K (Koszul.Cut K E) (FreeGrL K (BarGen (Ipres K E c hc r))) :=
  FreeGrL.mapCoop (Koszul.barGen (Ipres K E c hc r) (hE_pres c hc r))

include hr2 in
/-- **`T^c(sE) → B(P, Ī_P)` is injective**, for relators with at least three inputs: the
coefficient of the generators is a retraction of `sE → sĪ_P`. -/
lemma cutBarP_injective (A : Type) [Fintype A] [DecidableEq A] :
    Function.Injective ((cutBarP c hc r).app A) := fun x y hxy => by
  have hid : ∀ z : Koszul.Cut K E A, (FreeGrL.mapSp (barRet c hc r hr2)).app A
      ((FreeGrL.mapSp (Koszul.barGen (Ipres K E c hc r) (hE_pres c hc r))).app A z) = z :=
    fun z => (FreeGrL.mapSp_comp _ _ z).trans ((FreeGrL.mapSp_congr
      (ψ := (GrSpEnd.id K (GrSpecies.Shift E K)).toHom)
      (fun B _ _ v => barRet_barGen c hc r hr2 v) z).trans (FreeGrL.mapSp_id z))
  exact ((hid x).symm.trans (congrArg _ hxy)).trans (hid y)

/-- **`T^c(sE) → B(P, Ī_P)` lands in the trees with `|A| - 1` vertices**, the generators being
binary. -/
lemma cutBarP_mem_vx {A : Type} [Fintype A] [DecidableEq A] (hA : 1 ≤ Fintype.card A)
    (y : Koszul.Cut K E A) : (cutBarP c hc r).app A y ∈ 𝒱P (Fintype.card A - 1) A :=
  FreeGrL.mapSp_mem_vx (FreeGrL.mem_vx_of_binary (R := K) (V := GrSpecies.Shift E K)
    (fun _ _ _ hB v => gen_eq_zero c hB v) hA y)

variable (K E) in
include hr2 in
/-- **The cycles of `B(P, Ī_P)` on `T^c(sE)`**: the elements `y` of the cut cooperad with
`d (i y) = 0`, `i : T^c(sE) → B(P, Ī_P)`, a subcooperad. -/
noncomputable def cutCyc : GrSubCooperad K (Koszul.Cut K E) :=
  Bar.cycSub (Ipres K E c hc r) (cutBarP c hc r) (cutBarP_injective c hc r hr2)
    (fun _ _ _ hA y => cutBarP_mem_vx c hc r hA y)

/-- **The cycles lie in the Koszul dual cooperad**: on them `κ_T ⋆ κ_T` lands in the ideal of
the relators (`Koszul.star_mem_of_d`). -/
theorem cutCyc_le : cutCyc K E c hc r hr2 ≤ Koszul.dualSub K E r :=
  Koszul.le_dualSub r fun _ _ _ x hx => Koszul.star_mem_of_d _ (hE_pres c hc r)
    (GrOperadIdeal.atLeastTwo_hI1 (pres_zero c hc r) (Fin 0) (by simp)) x hx

/-- No suspended operations of `Ī_P` with at most one input. -/
lemma barGen_red (B : Type) [Fintype B] [DecidableEq B] (hB : Fintype.card B ≤ 1)
    (v : BarGen (Ipres K E c hc r) B) : v = 0 :=
  IdealSp.ext _ (GrOperadIdeal.atLeastTwo_hI1 (pres_zero c hc r) B hB _ (IdealSp.mem _ v))

variable [CharZero K]
include hr2

/-- **`sĪ_P → sE → sĪ_P` is the identity with at most two inputs**: the binary operations of `P`
are its generators, for relators with at least three inputs. -/
lemma barGen_barRet {B : Type} [Fintype B] [DecidableEq B] (hB : Fintype.card B ≤ 2)
    (v : BarGen (Ipres K E c hc r) B) :
    (Koszul.barGen (Ipres K E c hc r) (hE_pres c hc r)).app B ((barRet c hc r hr2).app B v)
      = v := by
  rcases Nat.lt_or_ge (Fintype.card B) 2 with h | h
  · rw [barGen_red c hc r B (by omega) v, map_zero, map_zero]
  · refine IdealSp.ext _ ?_
    obtain ⟨y, hy⟩ := (𝒥).proj_surjective B (IdealSp.val _ v)
    have hy1 : y ∈ FreeGrL.vx K E 1 B := by
      have := FreeGrL.mem_vx_of_binary (R := K) (V := E) (fun B _ _ hB v => gen_eq_zero c hB v)
        (by omega) y
      rwa [show Fintype.card B - 1 = 1 by omega] at this
    show (𝒥).proj B ((FreeGrL.ι K E).app B (presCoef c hc r hr2 B (IdealSp.val _ v)))
      = IdealSp.val _ v
    rw [← hy, presCoef_proj, ← FreeGrL.eq_ι_genCoef hy1]

/-- **`P^¡(n)` maps onto the cycles of `B(P, Ī_P)(Fin n)` with `n - 1` vertices**, for relators
with at least three inputs, over a field of characteristic zero: such a cycle has only binary
vertices, so it is the image of `y ∈ T^c(sE)(Fin n)`, and `y` lies in the subcooperad of the
cycles, hence in `P^¡` (`cutCyc_le`). -/
theorem toBar_surj_top {n : ℕ} (hn : 1 ≤ n) {z : FreeGrL K (BarGen (Ipres K E c hc r)) (Fin n)}
    (hz : z ∈ 𝒱P (n - 1) (Fin n)) (hdz : Bar.d (Ipres K E c hc r) (Fin n) z = 0) :
    ∃ x, (Koszul.toBar (Ipres K E c hc r) (hE_pres c hc r)).app (Fin n) x = z := by
  have hzy : (FreeGrL.mapSp (Koszul.barGen (Ipres K E c hc r) (hE_pres c hc r))).app (Fin n)
      ((FreeGrL.mapSp (barRet c hc r hr2)).app (Fin n) z) = z := by
    rw [FreeGrL.mapSp_comp]
    refine (FreeGrL.mapSp_eq_of_top (barGen_red c hc r)
      (g' := (GrSpEnd.id K (BarGen (Ipres K E c hc r))).toHom) (fun B _ _ hB v => ?_)
      (by rw [Fintype.card_fin]; exact hn) (by rw [Fintype.card_fin]; exact hz)).trans
      (FreeGrL.mapSp_id z)
    exact barGen_barRet c hc r hr2 hB v
  have hy : (FreeGrL.mapSp (barRet c hc r hr2)).app (Fin n) z
      ∈ (cutCyc K E c hc r hr2).sub (Fin n) :=
    LinearMap.mem_ker.2 ((congrArg (Bar.d (Ipres K E c hc r) (Fin n)) hzy).trans hdz)
  have hx : (FreeGrL.mapSp (barRet c hc r hr2)).app (Fin n) z
      ∈ (Koszul.dualSub K E r).sub (Fin n) := cutCyc_le c hc r hr2 (Fin n) hy
  exact ⟨⟨_, hx⟩, hzy⟩

end ShuffleBarSym

namespace ShuffleBarSym

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {G : Type} [Fintype G] [DecidableEq G]
  (c : ∀ k, Module.Basis (BinGen G k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen G k), GrSpecies.par (R := K) false (c k β) = c k β)
  {r : ∀ n : ℕ, Set (FreeGrL K E (Fin n))} [CharZero K]

local notation "𝒱T" => FreeGrL.vx K (BarGen (Ibar K E c hc))

/-- **The Koszul criterion for binary quadratic data, below the top degree**: for relators with
at least three inputs, over a field of characteristic zero, `P` is Koszul iff for every `n ≥ 2`,
in `B(T, Ī)(Fin n)` modulo the relator ideal `Krel`, every cycle with `s + 1 < n` vertices is the
boundary of one with `s + 1`; the clause on the top cycles of `isKoszul_iff_free` always holds
(`toBar_surj_top`). -/
theorem isKoszul_iff_free_lower (hr2 : ∀ n, n < 3 → r n = ∅) :
    Koszul.IsKoszul K E r ↔ ∀ n, 2 ≤ n → ∀ s, s + 1 < n → ∀ x ∈ 𝒱T s (Fin n),
        Bar.d (Ibar K E c hc) (Fin n) x ∈ (Krel K E c hc r).sub (Fin n) →
        ∃ y ∈ 𝒱T (s + 1) (Fin n),
          x - Bar.d (Ibar K E c hc) (Fin n) y ∈ (Krel K E c hc r).sub (Fin n) :=
  (isKoszul_iff_free c hc hr2).trans (forall_congr' fun _ => imp_congr_right fun hn =>
    and_iff_right fun _ hz hdz => toBar_surj_top c hc r hr2 (by omega) hz hdz)

/-- **The bridge, given the relator ideal**: for relators with at least three inputs, over a
field of characteristic zero, if `ΦL` maps the relator ideal `Krel` onto
`ShuffleBar.J K R ⊓ supported (barSet G n)` in every arity `n ≥ 2`, then `P` is Koszul iff the
shuffle operad presented by `R` is (`ShuffleBar.IsKoszul`). -/
theorem isKoszul_iff_shuffle_of_J (hr2 : ∀ n, n < 3 → r n = ∅)
    (R : Submodule K (LTree.Mono G 3 → K))
    (hJ : ∀ n, 2 ≤ n → Submodule.map (ΦL c hc n) ((Krel K E c hc r).sub (Fin n))
      = ShuffleBar.J K R ⊓ Finsupp.supported K K (barSet G n)) :
    Koszul.IsKoszul K E r ↔ ShuffleBar.IsKoszul K R :=
  isKoszul_iff_shuffle_of c hc hr2 R hJ fun _ hn _ hz hdz =>
    toBar_surj_top c hc r hr2 (by omega) hz hdz

end ShuffleBarSym

end Operad
