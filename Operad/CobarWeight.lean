/-
# Weights on the cobar construction of a cut cooperad

**An acyclicity criterion by weights** (`exists_eq_D_of_weights`): let `M` be the direct sum of
the eigenspaces `W j` of an endomorphism `E` for the natural numbers `j`, over a `ℚ`-algebra, and
`D = d - δ` a differential, `d` preserving the weights and `δ` lowering them by one, with a
homotopy `h` such that `d h + h d = E - S`, `S` the identity up to weight zero. Then a `D`-cycle
killed by a map `c` with `c ∘ D = 0` is a `D`-boundary, as soon as `c` is injective on the parts
of weight at most one: on the part of top weight `n ≥ 2`, `d h + h d = n - 1` is invertible, so
the top part is a `d`-boundary of an element of weight `n`, which lowers the top weight. The
eigenspaces for the natural numbers are independent over a `ℚ`-algebra
(`iSupIndep_eigenspace_nat`).

For the cobar construction `ΩC` of the cut cooperad `C = FreeGrL R V`, with the weight derivation
`E` counting the vertices of the trees decorating the generators:

* **`E` commutes with the cobar differential** (`Cobar.d_wtΩ`), by the contraction identity, when
  there are no generators without inputs;
* **`ΩC` is the direct sum of the weight spaces** over a `ℚ`-algebra (`Cobar.isInternal_wt`): a tree
  with vertices is a generator of a corolla or has weight at least two (`Cobar.mem_units_sup`), and
  the weights zero and one are the units and the generators of the corollas
  (`Cobar.mem_unitsΩ_of_mem_wt`, `Cobar.mem_corGen_of_mem_wt`);
* an odd derivation `δ` extending `s⁻¹ c̄ ↦ s⁻¹ (ϑ c)‾`, `ϑ` lowering the number of vertices by one,
  **lowers the weight by one** (`Cobar.wtΩ_δ`), so that **a cycle of `d - δ` killed by a map
  injective on the units and the generators of the corollas is a boundary** (`Cobar.exists_sub_eq`).
-/
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Operad.CobarContraction

universe u v

namespace Operad

open Sym GerBV TreeOfArity FreeGr DirectSum

/-! ## Eigenspace decompositions and an acyclicity criterion -/

section WeightArg

variable {R : Type u} [CommRing R] {M Q : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup Q] [Module R Q]

/-- The nonzero natural numbers are units of a `ℚ`-algebra. -/
lemma isUnit_natCast_of_ne_zero [Algebra ℚ R] {n : ℕ} (hn : n ≠ 0) : IsUnit (n : R) := by
  have h := (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hn : (n : ℚ) ≠ 0)).map (algebraMap ℚ R)
  rwa [map_natCast] at h

/-- The differences of distinct natural numbers are units of a `ℚ`-algebra. -/
lemma isUnit_natCast_sub [Algebra ℚ R] {i j : ℕ} (h : i ≠ j) : IsUnit ((i : R) - j) := by
  have h' := (isUnit_iff_ne_zero.2 (sub_ne_zero.2 (Nat.cast_injective.ne h) :
    (i : ℚ) - j ≠ 0)).map (algebraMap ℚ R)
  rwa [map_sub, map_natCast, map_natCast] at h'

/-- **The eigenspaces of an endomorphism for the natural numbers are independent**, over a
`ℚ`-algebra. -/
theorem iSupIndep_eigenspace_nat [Algebra ℚ R] (E : M →ₗ[R] M) :
    iSupIndep fun j : ℕ => Module.End.eigenspace E (j : R) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s
  induction s using Finset.induction_on with
  | empty => intro v _ _ i hi; exact absurd hi (Finset.notMem_empty i)
  | insert a s ha ih =>
    intro v hv hsum i hi
    have hE : ∀ j ∈ insert a s, E (v j) = (j : R) • v j := fun j hj =>
      Module.End.mem_eigenspace_iff.1 (hv j hj)
    have h0 : ∑ j ∈ insert a s, ((j : R) - a) • v j = 0 := by
      have e : ∀ j ∈ insert a s, ((j : R) - a) • v j = E (v j) - (a : R) • v j :=
        fun j hj => by rw [hE j hj, sub_smul]
      rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← map_sum, ← Finset.smul_sum, hsum,
        map_zero, smul_zero, sub_zero]
    rw [Finset.sum_insert ha, sub_self, zero_smul, zero_add] at h0
    have h1 := ih (fun j => ((j : R) - a) • v j)
      (fun j hj => (Module.End.eigenspace E (j : R)).smul_mem _
        (hv j (Finset.mem_insert_of_mem hj))) h0
    have h2 : ∀ j ∈ s, v j = 0 := fun j hj =>
      (isUnit_natCast_sub (fun h : j = a => ha (h ▸ hj))).smul_left_cancel.1
        ((h1 j hj).trans (smul_zero _).symm)
    rcases Finset.mem_insert.1 hi with rfl | hi
    · rw [Finset.sum_insert ha, Finset.sum_eq_zero h2, add_zero] at hsum
      exact hsum
    · exact h2 i hi

variable (W : ℕ → Submodule R M) [Decomposition W]

private lemma pr_add (j : ℕ) (y z : M) :
    (decompose W (y + z) j : M) = (decompose W y j : M) + (decompose W z j : M) := by
  rw [decompose_add, DirectSum.add_apply, Submodule.coe_add]

private lemma pr_sub (j : ℕ) (y z : M) :
    (decompose W (y - z) j : M) = (decompose W y j : M) - (decompose W z j : M) := by
  rw [decompose_sub, DirectSum.sub_apply, Submodule.coe_sub]

private lemma pr_smul (j : ℕ) (c : R) (y : M) :
    (decompose W (c • y) j : M) = c • (decompose W y j : M) := by
  rw [decompose_smul, DirectSum.smul_apply, Submodule.coe_smul]

private lemma pr_zero (j : ℕ) : (decompose W (0 : M) j : M) = 0 := by
  rw [decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]

private lemma pr_of_mem {i : ℕ} {y : M} (hy : y ∈ W i) (j : ℕ) :
    (decompose W y j : M) = if i = j then y else 0 := by
  split_ifs with h
  · subst h
    exact decompose_of_mem_same W hy
  · exact decompose_of_mem_ne W hy h

/-- The maps preserving the weights commute with the components. -/
private lemma pr_comm (φ : M →ₗ[R] M) (hφ : ∀ i, ∀ y ∈ W i, φ y ∈ W i) (j : ℕ) (y : M) :
    (decompose W (φ y) j : M) = φ (decompose W y j) := by
  refine Decomposition.inductionOn W (motive := fun y =>
    (decompose W (φ y) j : M) = φ (decompose W y j)) ?_ ?_ ?_ y
  · beta_reduce
    rw [map_zero, pr_zero, map_zero]
  · intro i m
    beta_reduce
    rw [pr_of_mem W (hφ i _ m.2), pr_of_mem W m.2]
    split_ifs
    · rfl
    · rw [map_zero]
  · intro m m' hm hm'
    beta_reduce at hm hm' ⊢
    rw [map_add, pr_add, pr_add, hm, hm', map_add]

/-- The maps lowering the weights by one shift the components. -/
private lemma pr_shift (φ : M →ₗ[R] M) (hφ : ∀ i, ∀ y ∈ W (i + 1), φ y ∈ W i)
    (hφ0 : ∀ y ∈ W 0, φ y = 0) (j : ℕ) (y : M) :
    (decompose W (φ y) j : M) = φ (decompose W y (j + 1)) := by
  refine Decomposition.inductionOn W (motive := fun y =>
    (decompose W (φ y) j : M) = φ (decompose W y (j + 1))) ?_ ?_ ?_ y
  · beta_reduce
    rw [map_zero, pr_zero, pr_zero, map_zero]
  · intro i m
    beta_reduce
    cases i with
    | zero =>
      rw [hφ0 _ m.2, pr_zero, pr_of_mem W m.2, if_neg (Nat.succ_ne_zero j).symm, map_zero]
    | succ i =>
      rw [pr_of_mem W (hφ i _ m.2), pr_of_mem W m.2]
      by_cases h : i = j
      · rw [if_pos h, if_pos (congrArg (· + 1) h)]
      · rw [if_neg h, if_neg (fun h' => h (Nat.succ.inj h')), map_zero]
  · intro m m' hm hm'
    beta_reduce at hm hm' ⊢
    rw [map_add, pr_add, pr_add, hm, hm', map_add]

private lemma exists_top (y : M) : ∃ N : ℕ, ∀ j, N < j → (decompose W y j : M) = 0 := by
  classical
  refine ⟨(decompose W y).support.sup id, fun j hj => ?_⟩
  have h : j ∉ (decompose W y).support := fun h =>
    absurd (Finset.le_sup (f := id) h) (not_le.2 hj)
  rw [DFinsupp.notMem_support_iff.1 h, ZeroMemClass.coe_zero]

private lemma eq_low (y : M) (h : ∀ j, 2 ≤ j → (decompose W y j : M) = 0) :
    y = (decompose W y 0 : M) + (decompose W y 1 : M) := by
  classical
  conv_lhs => rw [← sum_support_decompose W y]
  rw [← Finset.sum_pair (f := fun i => (decompose W y i : M)) zero_ne_one]
  refine Finset.sum_subset (fun i hi => ?_) (fun i _ hi => ?_)
  · by_contra hni
    have h2 : 2 ≤ i := by
      rw [Finset.mem_insert, Finset.mem_singleton] at hni
      omega
    exact DFinsupp.mem_support_iff.1 hi ((Submodule.coe_eq_zero).1 (h i h2))
  · rw [DFinsupp.notMem_support_iff.1 hi, ZeroMemClass.coe_zero]

/-- **An acyclicity criterion by weights**: for a differential `D = d - δ` on a direct sum of
eigenspaces `W j` of `E`, `d` preserving the weights and `δ` lowering them by one, with
`d h + h d = E - S`, `S` the identity up to weight zero, a `D`-cycle killed by a map `c` with
`c ∘ D = 0` is a `D`-boundary, as soon as `c` is injective on the parts of weight at most one. -/
theorem exists_eq_D_of_weights [Algebra ℚ R] (E d h δ S : M →ₗ[R] M) (c : M →ₗ[R] Q)
    (hE : ∀ j, ∀ y ∈ W j, E y = (j : R) • y) (hd : ∀ j, ∀ y ∈ W j, d y ∈ W j)
    (hδ : ∀ j, ∀ y ∈ W (j + 1), δ y ∈ W j) (hδ0 : ∀ y ∈ W 0, δ y = 0)
    (hDD : ∀ y, d (d y - δ y) - δ (d y - δ y) = 0)
    (hK : ∀ y, d (h y) + h (d y) = E y - S y) (hS : ∀ y, S y - y ∈ W 0)
    (hc : ∀ y, c (d y - δ y) = 0)
    (hbase : ∀ y₀ ∈ W 0, ∀ y₁ ∈ W 1, c (y₀ + y₁) = 0 → y₀ + y₁ = 0)
    (y : M) (hy : d y - δ y = 0) (hcy : c y = 0) : ∃ z, d z - δ z = y := by
  suffices key : ∀ N : ℕ, ∀ y : M, (∀ j, N + 1 < j → (decompose W y j : M) = 0) →
      d y - δ y = 0 → c y = 0 → ∃ z, d z - δ z = y by
    obtain ⟨N, hN⟩ := exists_top W y
    exact key N y (fun j hj => hN j (by omega)) hy hcy
  intro N
  induction N with
  | zero =>
    intro y hN _ hcy
    have hy := eq_low W y fun j hj => hN j (by omega)
    have hc' : c ((decompose W y 0 : M) + (decompose W y 1 : M)) = 0 := by
      rw [← hy]
      exact hcy
    refine ⟨0, ?_⟩
    rw [map_zero, map_zero, sub_zero, hy]
    exact (hbase _ (Submodule.coe_mem _) _ (Submodule.coe_mem _) hc').symm
  | succ N ih =>
    intro y hN hy hcy
    have hYn : (decompose W y (N + 2) : M) ∈ W (N + 2) := Submodule.coe_mem _
    -- the top part is a `d`-cycle
    have h1 : d (decompose W y (N + 2) : M) = 0 := by
      have e := congrArg (fun z => (decompose W z (N + 2) : M)) hy
      simp only at e
      rw [pr_sub, pr_comm W d hd, pr_shift W δ hδ hδ0, hN (N + 2 + 1) (by omega), map_zero,
        sub_zero, pr_zero] at e
      exact e
    -- the top part is the `d`-boundary of the weight-`(N + 2)` part of its homotopy
    have h2 : d (decompose W (h (decompose W y (N + 2))) (N + 2) : M)
        = ((N + 1 : ℕ) : R) • (decompose W y (N + 2) : M) := by
      rw [← pr_comm W d hd]
      have e : d (h (decompose W y (N + 2))) = E (decompose W y (N + 2))
          - S (decompose W y (N + 2)) := by
        have := hK (decompose W y (N + 2))
        rw [h1, map_zero, add_zero] at this
        exact this
      have e2 : (decompose W (S (decompose W y (N + 2))) (N + 2) : M)
          = (decompose W y (N + 2) : M) := by
        have := pr_add W (N + 2) (decompose W y (N + 2) : M)
          (S (decompose W y (N + 2)) - decompose W y (N + 2))
        rw [add_sub_cancel, pr_of_mem W hYn, if_pos rfl,
          pr_of_mem W (hS _), if_neg (by omega), add_zero] at this
        exact this
      rw [e, pr_sub, hE _ _ hYn, pr_smul, pr_of_mem W hYn, if_pos rfl, e2,
        show ((N + 2 : ℕ) : R) = ((N + 1 : ℕ) : R) + 1 by push_cast; ring, add_smul, one_smul,
        add_sub_cancel_right]
    obtain ⟨u, hu⟩ := isUnit_natCast_of_ne_zero (R := R) (Nat.succ_ne_zero N)
    have hc1 : ((u⁻¹ : Rˣ) : R) * ((N + 1 : ℕ) : R) = 1 := by rw [← hu, Units.inv_mul]
    set Z := ((u⁻¹ : Rˣ) : R) • (decompose W (h (decompose W y (N + 2))) (N + 2) : M) with hZdef
    have hZ : Z ∈ W (N + 2) := (W (N + 2)).smul_mem _ (Submodule.coe_mem _)
    have hdZ : d Z = (decompose W y (N + 2) : M) := by
      rw [hZdef, map_smul, h2, smul_smul, hc1, one_smul]
    -- lower the top weight
    have htop : ∀ j, N + 1 < j → (decompose W (y - (d Z - δ Z)) j : M) = 0 := by
      intro j hj
      rw [pr_sub, pr_sub, pr_comm W d hd, pr_shift W δ hδ hδ0, pr_of_mem W hZ, pr_of_mem W hZ,
        if_neg (show N + 2 ≠ j + 1 by omega), map_zero, sub_zero]
      by_cases hj2 : N + 2 = j
      · subst hj2
        rw [if_pos rfl, hdZ, sub_self]
      · rw [if_neg hj2, map_zero, sub_zero, hN j (by omega)]
    obtain ⟨z', hz'⟩ := ih (y - (d Z - δ Z)) htop
      (by rw [map_sub d, map_sub δ, sub_sub_sub_comm, hy, hDD, sub_zero])
      (by rw [map_sub, hcy, hc, sub_zero])
    refine ⟨Z + z', ?_⟩
    rw [map_add, map_add, add_sub_add_comm, hz']
    abel

end WeightArg

/-! ## The weights of the cobar construction of a cut cooperad -/

section Weights

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

local notation "𝒞" => FreeGrL R V
local notation "𝒥" => GrOperadIdeal.span R (grLinRel R V)
local notation "𝒥Ω" => GrOperadIdeal.span R (grLinRel R (CobarGen R 𝒞))
local notation "𝔟" => SgnLin.bas (treeSgn (grGenPar R V)) R
local notation "𝔅" => SgnLin.bas (treeSgn (grGenPar R (CobarGen R 𝒞))) R

namespace Cobar

/-! ### The weight derivation commutes with the cobar differential -/

omit [GrSpecies R V] in
/-- The algebra of the commutation of the weight derivation with the cobar differential. -/
private lemma alg_comm {M : Type*} [AddCommGroup M] [Module R M] (d h E S : M →ₗ[R] M) (y : M)
    (h1 : d (h y) + h (d y) = E y - S y) (h2 : d (h (d y)) + h (d (d y)) = E (d y) - S (d y))
    (hdd : ∀ z, d (d z) = 0) (hs1 : d (S y) = d y) (hs2 : S (d y) = d y) :
    d (E y) = E (d y) := by
  have e1 : E y = d (h y) + h (d y) + S y := by rw [h1]; abel
  have e2 : E (d y) = d (h (d y)) + h (d (d y)) + S (d y) := by rw [h2]; abel
  rw [e1, e2, map_add, map_add, hdd, hdd, map_zero, hs1, hs2]
  abel

/-- The cobar differential kills the unit. -/
lemma d_unitL : (Cobar.d R 𝒞).app A (FreeGrL.unitL R (CobarGen R 𝒞) A) = 0 :=
  (map_sum _ _ _).trans (Finset.sum_eq_zero fun e _ => d_unit e)

/-- **The weight derivation commutes with the cobar differential**, when there are no generators
without inputs: by the contraction identity, `d² = 0` and `d` killing the unit components. -/
theorem d_wtΩ (hV0 : ∀ v : V (Fin 0), v = 0) (Y : CobarGr R 𝒞 A) :
    (Cobar.d R 𝒞).app A ((wtΩ R V).app A Y) = (wtΩ R V).app A ((Cobar.d R 𝒞).app A Y) := by
  have h1 := dh_hd hV0 Y
  have h2 := dh_hd hV0 ((Cobar.d R 𝒞).app A Y)
  have hz : (Cobar.d R 𝒞).app A (FreeGrL.unitCoeffL R (CobarGen R 𝒞) A Y
      • FreeGrL.unitL R (CobarGen R 𝒞) A) = 0 :=
    (map_smul _ _ _).trans ((congrArg _ d_unitL).trans (smul_zero _))
  have hs1 : (Cobar.d R 𝒞).app A (FreeGrL.secC R (CobarGen R 𝒞) A Y)
      = (Cobar.d R 𝒞).app A Y :=
    (congrArg ((Cobar.d R 𝒞).app A) (FreeGrL.secC_apply Y)).trans
      ((map_sub _ _ _).trans ((congrArg _ hz).trans (sub_zero _)))
  have hs2 := FreeGrL.secC_of_unitCoeff (unitCoeffL_d hV0 Y)
  have hdd : ∀ z : CobarGr R 𝒞 A, (Cobar.d R 𝒞).app A ((Cobar.d R 𝒞).app A z) = 0 :=
    fun z => Cobar.d_d R 𝒞 z
  exact alg_comm _ _ _ _ Y h1 h2 hdd hs1 hs2

/-! ### The weight spaces -/

variable (R V) in
/-- **The weight-`j` part of the cobar construction**: the eigenspace of the weight derivation for
`j`. -/
noncomputable abbrev wt (j : ℕ) (A : Type) [Fintype A] [DecidableEq A] :
    Submodule R (CobarGr R 𝒞 A) :=
  Module.End.eigenspace ((wtΩ R V).app A) (j : R)

lemma mem_wt {j : ℕ} {Y : CobarGr R 𝒞 A} :
    Y ∈ wt R V j A ↔ (wtΩ R V).app A Y = (j : R) • Y :=
  Module.End.mem_eigenspace_iff

/-- **The weight derivation is an even derivation.** -/
lemma wtΩ_comp (r : A) (P : CobarGr R 𝒞 A) (Q : CobarGr R 𝒞 B) :
    (wtΩ R V).app _ (GrOperad.comp (R := R) r P Q)
      = GrOperad.comp (R := R) r ((wtΩ R V).app A P) Q
        + GrOperad.comp (R := R) r P ((wtΩ R V).app B Q) :=
  ((wtΩ R V).app_comp r P Q).trans (congrArg (fun z => GrOperad.comp (R := R) r
    ((wtΩ R V).app A P) Q + GrOperad.comp (R := R) r z ((wtΩ R V).app B Q))
      (GrOperad.tw_false P))

lemma wtΩ_tw (X : CobarGr R 𝒞 A) :
    (wtΩ R V).app A (GrOperad.tw (R := R) true X)
      = GrOperad.tw (R := R) true ((wtΩ R V).app A X) :=
  ((wtΩ R V).app_tw true X).trans (one_smul R _)

lemma unit_mem_wt (e : Unit ≃ A) :
    GrOperad.map (R := R) e (GrOperad.one (R := R) (P := CobarGr R 𝒞)) ∈ wt R V 0 A := by
  rw [mem_wt, Nat.cast_zero, zero_smul]
  exact ((wtΩ R V).app_map e _).trans ((congrArg _ (wtΩ R V).app_one).trans (map_zero _))

lemma map_mem_wt {A' : Type} [Fintype A'] [DecidableEq A'] (e : A ≃ A') {j : ℕ}
    {Y : CobarGr R 𝒞 A} (hY : Y ∈ wt R V j A) : GrOperad.map (R := R) e Y ∈ wt R V j A' :=
  mem_wt.2 (((wtΩ R V).app_map e Y).trans ((congrArg _ (mem_wt.1 hY)).trans (map_smul _ _ _)))

/-- **The weights add under composition.** -/
lemma comp_mem_wt (r : A) {i j : ℕ} {P : CobarGr R 𝒞 A} {Q : CobarGr R 𝒞 B}
    (hP : P ∈ wt R V i A) (hQ : Q ∈ wt R V j B) :
    GrOperad.comp (R := R) r P Q ∈ wt R V (i + j) _ := by
  refine mem_wt.2 (((wtΩ R V).app_comp r P Q).trans ?_)
  have h1 : GrOperad.comp (R := R) r ((wtΩ R V).app A P) Q
      = (i : R) • GrOperad.comp (R := R) r P Q :=
    (congrArg (fun z => GrOperad.comp (R := R) r z Q) (mem_wt.1 hP)).trans
      (LinearMap.map_smul₂ _ _ _ _)
  have h2 : GrOperad.comp (R := R) r (GrOperad.tw (R := R) false P) ((wtΩ R V).app B Q)
      = (j : R) • GrOperad.comp (R := R) r P Q :=
    (congrArg₂ (fun a b => GrOperad.comp (R := R) r a b) (GrOperad.tw_false P)
      (mem_wt.1 hQ)).trans (map_smul _ _ _)
  refine (congrArg₂ (· + ·) h1 h2).trans ((add_smul _ _ _).symm.trans ?_)
  rw [Nat.cast_add]

/-- The generator of a tree with `w` vertices has weight `w`. -/
lemma ιL_bas_mem_wt (t : Reg (TreeOfArity (GrGen R V)) A) :
    Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t)) ∈ wt R V (treeOf t).weight A :=
  mem_wt.2 ((wtΩ_ιL _).trans ((congrArg (Cobar.ιL R 𝒞 A) (FreeGrL.wtD_proj_bas t)).trans
    (map_smul _ _ _)))

/-- **The cobar differential preserves the weights.** -/
lemma d_mem_wt (hV0 : ∀ v : V (Fin 0), v = 0) {j : ℕ} {Y : CobarGr R 𝒞 A}
    (hY : Y ∈ wt R V j A) : (Cobar.d R 𝒞).app A Y ∈ wt R V j A :=
  mem_wt.2 ((d_wtΩ hV0 Y).symm.trans ((congrArg _ (mem_wt.1 hY)).trans (map_smul _ _ _)))

lemma unitL_mem_wt : FreeGrL.unitL R (CobarGen R 𝒞) A ∈ wt R V 0 A :=
  Submodule.sum_mem _ fun e _ => unit_mem_wt e

/-- Removing the unit component changes an element by an element of weight zero. -/
lemma secC_sub_mem_wt (Y : CobarGr R 𝒞 A) :
    FreeGrL.secC R (CobarGen R 𝒞) A Y - Y ∈ wt R V 0 A := by
  rw [FreeGrL.secC_apply, sub_sub_cancel_left]
  exact Submodule.neg_mem _ (Submodule.smul_mem _ _ unitL_mem_wt)

/-! ### The units, the generators of the corollas, and the parts of weight at least two -/

variable (R V) in
/-- The span of the units. -/
noncomputable abbrev unitsΩ (A : Type) [Fintype A] [DecidableEq A] :
    Submodule R (CobarGr R 𝒞 A) :=
  Submodule.span R (Set.range fun e : Unit ≃ A =>
    GrOperad.map (R := R) e (GrOperad.one (R := R) (P := CobarGr R 𝒞)))

variable (R V) in
/-- The generators of the corollas. -/
noncomputable abbrev corGen (A : Type) [Fintype A] [DecidableEq A] :
    Submodule R (CobarGr R 𝒞 A) :=
  LinearMap.range ((Cobar.ιL R 𝒞 A).comp ((FreeGrL.ι R V).app A))

variable (R V) in
/-- The parts of weight at least two. -/
noncomputable abbrev wtTwo (A : Type) [Fintype A] [DecidableEq A] :
    Submodule R (CobarGr R 𝒞 A) :=
  ⨆ j : ℕ, wt R V (j + 2) A

lemma unitsΩ_le : unitsΩ R V A ≤ wt R V 0 A :=
  Submodule.span_le.2 (by rintro _ ⟨e, rfl⟩; exact unit_mem_wt e)

lemma corGen_le : corGen R V A ≤ wt R V 1 A := by
  rintro _ ⟨v, rfl⟩
  refine mem_wt.2 (((wtΩ_ιL ((FreeGrL.ι R V).app A v)).trans
    (congrArg (Cobar.ιL R 𝒞 A) (FreeGrL.wtD_ι v))).trans ?_)
  rw [Nat.cast_one, one_smul]
  rfl

private lemma low_le_ne0 : corGen R V A ⊔ wtTwo R V A ≤ ⨆ (j : ℕ) (_ : j ≠ 0), wt R V j A :=
  sup_le (corGen_le.trans (le_iSup₂_of_le 1 one_ne_zero le_rfl))
    (iSup_le fun j => le_iSup₂_of_le (j + 2) (by omega) le_rfl)

private lemma wtTwo_le_ne1 : wtTwo R V A ≤ ⨆ (j : ℕ) (_ : j ≠ 1), wt R V j A :=
  iSup_le fun j => le_iSup₂_of_le (j + 2) (by omega) le_rfl

private lemma unitsΩ_le_ne1 : unitsΩ R V A ≤ ⨆ (j : ℕ) (_ : j ≠ 1), wt R V j A :=
  unitsΩ_le.trans (le_iSup₂_of_le 0 zero_ne_one le_rfl)

lemma map_mem_corGen {A' : Type} [Fintype A'] [DecidableEq A'] (e : A ≃ A')
    {Y : CobarGr R 𝒞 A} (hY : Y ∈ corGen R V A) : GrOperad.map (R := R) e Y ∈ corGen R V A' := by
  obtain ⟨v, rfl⟩ := hY
  refine ⟨SymSpecies.map (R := R) e v, ?_⟩
  show Cobar.ιL R 𝒞 A' ((FreeGrL.ι R V).app A' (SymSpecies.map (R := R) e v))
    = GrOperad.map (R := R) e (Cobar.ιL R 𝒞 A ((FreeGrL.ι R V).app A v))
  rw [(FreeGrL.ι R V).app_map, FreeGrL.symMap_eq, ιL_map']

lemma map_mem_wtTwo {A' : Type} [Fintype A'] [DecidableEq A'] (e : A ≃ A')
    {Y : CobarGr R 𝒞 A} (hY : Y ∈ wtTwo R V A) : GrOperad.map (R := R) e Y ∈ wtTwo R V A' :=
  Submodule.iSup_induction _ (motive := fun Y => GrOperad.map (R := R) e Y ∈ wtTwo R V A') hY
    (fun j Y hY => Submodule.mem_iSup_of_mem j (map_mem_wt e hY))
    (by beta_reduce; rw [map_zero (GrOperad.map (R := R) (P := CobarGr R 𝒞) e)]; exact zero_mem _)
    (fun Y Y' hY hY' => by beta_reduce at hY hY' ⊢; rw [map_add]; exact add_mem hY hY')

lemma map_mem_low {A' : Type} [Fintype A'] [DecidableEq A'] (e : A ≃ A')
    {Y : CobarGr R 𝒞 A} (hY : Y ∈ corGen R V A ⊔ wtTwo R V A) :
    GrOperad.map (R := R) e Y ∈ corGen R V A' ⊔ wtTwo R V A' := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hY
  rw [map_add]
  exact Submodule.add_mem_sup (map_mem_corGen e hy) (map_mem_wtTwo e hz)

/-- **The composites of parts of weight at least one have weight at least two.** -/
lemma comp_mem_wtTwo (r : A) {P : CobarGr R 𝒞 A} {Q : CobarGr R 𝒞 B}
    (hP : P ∈ ⨆ i : ℕ, wt R V (i + 1) A) (hQ : Q ∈ ⨆ j : ℕ, wt R V (j + 1) B) :
    GrOperad.comp (R := R) r P Q ∈ wtTwo R V _ := by
  refine Submodule.iSup_induction _
    (motive := fun P => GrOperad.comp (R := R) r P Q ∈ wtTwo R V _) hP (fun i P hP => ?_) ?_ ?_
  · refine Submodule.iSup_induction _
      (motive := fun Q => GrOperad.comp (R := R) r P Q ∈ wtTwo R V _) hQ (fun j Q hQ => ?_) ?_ ?_
    · have h := comp_mem_wt r hP hQ
      rw [show i + 1 + (j + 1) = i + j + 2 by omega] at h
      exact Submodule.mem_iSup_of_mem (i + j) h
    · beta_reduce
      rw [map_zero (GrOperad.comp (R := R) (P := CobarGr R 𝒞) r P)]
      exact zero_mem _
    · intro Q Q' hQ hQ'
      beta_reduce at hQ hQ' ⊢
      rw [map_add]
      exact add_mem hQ hQ'
  · beta_reduce
    rw [LinearMap.map_zero₂ (GrOperad.comp (R := R) (P := CobarGr R 𝒞) r) Q]
    exact zero_mem _
  · intro P P' hP hP'
    beta_reduce at hP hP' ⊢
    rw [map_add, LinearMap.add_apply]
    exact add_mem hP hP'

lemma low_le_pos : corGen R V A ⊔ wtTwo R V A ≤ ⨆ i : ℕ, wt R V (i + 1) A :=
  sup_le (corGen_le.trans (le_iSup (fun i : ℕ => wt R V (i + 1) A) 0))
    (iSup_le fun j => le_iSup (fun i : ℕ => wt R V (i + 1) A) (j + 1))

/-! ### The decomposition by the weights -/

omit [GrSpecies R V] in
private lemma mem_of_single {α : Type*} {M : Type*} [AddCommGroup M] [Module R M]
    {S : Submodule R M} (f : (α →₀ R) →ₗ[R] M) (h : ∀ a, f (Finsupp.single a 1) ∈ S)
    (x : α →₀ R) : f x ∈ S := by
  induction x using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact S.zero_mem
  | add x y hx hy => rw [map_add]; exact S.add_mem hx hy
  | single a b =>
    rw [← Finsupp.smul_single_one, map_smul]
    exact S.smul_mem b (h a)

/-- The generator of a tree is zero, a generator of a corolla, or of weight at least two. -/
private lemma ιL_bas_mem_low (t : Reg (TreeOfArity (GrGen R V)) B) :
    Cobar.ιL R 𝒞 B ((𝒥).proj B (𝔟 t)) ∈ corGen R V B ⊔ wtTwo R V B := by
  by_cases hl : (treeOf t).isLeaf = true
  · exact (ιL_bas_leaf hl).symm ▸ zero_mem _
  have hw := Tree.one_le_weight (by simpa using hl : (treeOf t).isLeaf = false)
  rcases Nat.lt_or_ge (treeOf t).weight 2 with h2 | h2
  · obtain ⟨k, g, hg⟩ := eq_corolla_of_nVert (x := t) (by rw [nVert_eq]; omega)
    obtain ⟨e, he⟩ := exists_map_eq (x := Reg.std (corolla g)) (y := t) hg.symm
    have ht : (𝒥).proj B (𝔟 t) = (FreeGrL.ι R V).app B (SymSpecies.map (R := R) e g.1.1) := by
      rw [← he, FreeGrL.proj_bas_map, FreeGrL.proj_bas_corolla, (FreeGrL.ι R V).app_map,
        FreeGrL.symMap_eq]
    rw [ht]
    exact Submodule.mem_sup_left ⟨_, rfl⟩
  · refine Submodule.mem_sup_right (Submodule.mem_iSup_of_mem ((treeOf t).weight - 2) ?_)
    rw [Nat.sub_add_cancel h2]
    exact ιL_bas_mem_wt t

private lemma ιL_mem_low (y : FreeGr R (grGenPar R V) B) :
    Cobar.ιL R 𝒞 B ((𝒥).proj B y) ∈ corGen R V B ⊔ wtTwo R V B :=
  mem_of_single ((Cobar.ιL R 𝒞 B).comp ((𝒥).proj B)) (fun t => ιL_bas_mem_low t) y

private lemma bas_mem_corolla {k : ℕ} (g : GrGen R (CobarGen R 𝒞) k) (e : Fin k ≃ A) :
    (𝒥Ω).proj A (𝔅 (SetOperad.map e (Reg.std (corolla g)))) ∈ corGen R V A ⊔ wtTwo R V A := by
  obtain ⟨y, hy⟩ := exists_ιL_eq (R := R) (V := V) g.1.1
  have hZ : (𝒥Ω).proj A (𝔅 (SetOperad.map e (Reg.std (corolla g))))
      = GrOperad.map (R := R) e (Cobar.ιL R 𝒞 (Fin k) ((𝒥).proj (Fin k) y)) :=
    (FreeGrL.proj_bas_map e _).trans (congrArg (GrOperad.map (R := R) e)
      ((FreeGrL.proj_bas_corolla g).trans hy.symm))
  rw [hZ]
  exact map_mem_low e (ιL_mem_low y)

private lemma bas_mem_comp {A₁ B₁ : Type} [Fintype A₁] [DecidableEq A₁] [Fintype B₁]
    [DecidableEq B₁] (r : A₁) (p : Reg (TreeOfArity (GrGen R (CobarGen R 𝒞))) A₁)
    (q : Reg (TreeOfArity (GrGen R (CobarGen R 𝒞))) B₁) (e : Without A₁ r ⊕ B₁ ≃ A)
    (hp : (𝒥Ω).proj A₁ (𝔅 p) ∈ corGen R V A₁ ⊔ wtTwo R V A₁)
    (hq : (𝒥Ω).proj B₁ (𝔅 q) ∈ corGen R V B₁ ⊔ wtTwo R V B₁) :
    (𝒥Ω).proj A (𝔅 (SetOperad.map e (SetOperad.comp r p q))) ∈ corGen R V A ⊔ wtTwo R V A := by
  have hX : (𝒥Ω).proj A (𝔅 (SetOperad.map e (SetOperad.comp r p q)))
      = GrOperad.map (R := R) e (σ R (cSgn (grGenPar R (CobarGen R 𝒞)) r p q) •
          GrOperad.comp (R := R) r ((𝒥Ω).proj A₁ (𝔅 p)) ((𝒥Ω).proj B₁ (𝔅 q))) :=
    (FreeGrL.proj_bas_map e _).trans (congrArg (GrOperad.map (R := R) e)
      (FreeGrL.proj_bas_comp r p q))
  rw [hX]
  exact Submodule.mem_sup_right (map_mem_wtTwo e (Submodule.smul_mem _ _
    (comp_mem_wtTwo r (low_le_pos hp) (low_le_pos hq))))

/-- **A tree with vertices of the cobar construction has weight at least one**: its class lies in
the span of the generators of the corollas and of the parts of weight at least two. -/
private theorem bas_mem_low (x : Reg (TreeOfArity (GrGen R (CobarGen R 𝒞))) A) :
    (treeOf x).isLeaf = false → (𝒥Ω).proj A (𝔅 x) ∈ corGen R V A ⊔ wtTwo R V A :=
  tree_induction (motive := fun A _ _ x => (treeOf x).isLeaf = false →
      (𝒥Ω).proj A (𝔅 x) ∈ corGen R V A ⊔ wtTwo R V A)
    (fun _ _ _ _ hl hl' => absurd (hl.symm.trans hl') (by decide))
    (fun _ _ _ _ g e _ => bas_mem_corolla g e)
    (fun _ _ _ _ _ _ _ _ _ r p q e hpl hql hp hq _ => bas_mem_comp r p q e (hp hpl) (hq hql)) A x

/-- **The cobar construction is spanned by the units, the generators of the corollas, and the
parts of weight at least two.** -/
theorem mem_units_sup (Y : CobarGr R 𝒞 A) :
    Y ∈ unitsΩ R V A ⊔ (corGen R V A ⊔ wtTwo R V A) := by
  have h := Function.surjInv_eq ((𝒥Ω).proj_surjective A) Y
  rw [← h]
  refine mem_of_single ((𝒥Ω).proj A) (fun x => ?_) _
  by_cases hl : (treeOf x).isLeaf = true
  · obtain ⟨e, he⟩ := FreeGrL.proj_bas_leaf hl
    exact (congrArg (fun z => z ∈ unitsΩ R V A ⊔ (corGen R V A ⊔ wtTwo R V A)) he).mpr
      (Submodule.mem_sup_left (Submodule.subset_span ⟨e, rfl⟩))
  · exact Submodule.mem_sup_right (bas_mem_low x (by simpa using hl))

/-- **The cobar construction is the sum of its weight spaces.** -/
theorem iSup_wt_eq_top : ⨆ j : ℕ, wt R V j A = ⊤ :=
  eq_top_iff.2 fun Y _ => (sup_le (unitsΩ_le.trans (le_iSup (fun j : ℕ => wt R V j A) 0))
    (sup_le (corGen_le.trans (le_iSup (fun j : ℕ => wt R V j A) 1))
      (iSup_le fun j => le_iSup (fun j : ℕ => wt R V j A) (j + 2)))) (mem_units_sup Y)

/-- **The cobar construction is the direct sum of its weight spaces**, over a `ℚ`-algebra. -/
theorem isInternal_wt [Algebra ℚ R] : DirectSum.IsInternal fun j : ℕ => wt R V j A :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_eigenspace_nat ((wtΩ R V).app A)) iSup_wt_eq_top

/-- **The weight-zero part is spanned by the units**, over a `ℚ`-algebra. -/
theorem mem_unitsΩ_of_mem_wt [Algebra ℚ R] {Y : CobarGr R 𝒞 A} (hY : Y ∈ wt R V 0 A) :
    Y ∈ unitsΩ R V A := by
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.1 (mem_units_sup Y)
  have hz0 : z ∈ wt R V 0 A := by
    have := Submodule.sub_mem _ hY (unitsΩ_le hu)
    rwa [add_sub_cancel_left] at this
  have h0 : z = 0 := Submodule.disjoint_def.1
    (iSupIndep_eigenspace_nat ((wtΩ R V).app A) 0) z hz0 (low_le_ne0 hz)
  have e : u + z = u := (congrArg (u + ·) h0).trans (add_zero u)
  exact e.symm ▸ hu

/-- **The weight-one part consists of the generators of the corollas**, over a `ℚ`-algebra. -/
theorem mem_corGen_of_mem_wt [Algebra ℚ R] {Y : CobarGr R 𝒞 A} (hY : Y ∈ wt R V 1 A) :
    Y ∈ corGen R V A := by
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 (mem_units_sup Y)
  obtain ⟨c, hc, z, hz, rfl⟩ := Submodule.mem_sup.1 hw
  have h1 : u + z ∈ wt R V 1 A := by
    have := Submodule.sub_mem _ hY (corGen_le hc)
    rwa [add_left_comm, add_sub_cancel_left] at this
  have h0 : u + z = 0 := Submodule.disjoint_def.1
    (iSupIndep_eigenspace_nat ((wtΩ R V).app A) 1) _ h1
    (Submodule.add_mem _ (unitsΩ_le_ne1 hu) (wtTwo_le_ne1 hz))
  have e : u + (c + z) = c :=
    (add_left_comm u c z).trans ((congrArg (c + ·) h0).trans (add_zero c))
  exact e.symm ▸ hc

end Cobar

end Weights

/-! ## Inner differentials and the acyclicity of the cobar construction -/

section Inner

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

local notation "𝒞" => FreeGrL R V
local notation "𝒥" => GrOperadIdeal.span R (grLinRel R V)
local notation "𝒥Ω" => GrOperadIdeal.span R (grLinRel R (CobarGen R 𝒞))
local notation "𝔟" => SgnLin.bas (treeSgn (grGenPar R V)) R
local notation "𝔅" => SgnLin.bas (treeSgn (grGenPar R (CobarGen R 𝒞))) R

section Helpers

variable {M N Q : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup Q] [Module R Q]

omit [GrSpecies R V] in
private lemma alg_Eδ (c : M →ₗ[R] N →ₗ[R] Q) (EM δM tM : M →ₗ[R] M) (EN δN : N →ₗ[R] N)
    (EQ δQ : Q →ₗ[R] Q) (hδc : ∀ x y, δQ (c x y) = c (δM x) y + c (tM x) (δN y))
    (hEc : ∀ x y, EQ (c x y) = c (EM x) y + c x (EN y)) (hEt : ∀ x, EM (tM x) = tM (EM x))
    (x : M) (y : N) (hx : EM (δM x) = δM (EM x) - δM x) (hy : EN (δN y) = δN (EN y) - δN y) :
    EQ (δQ (c x y)) = δQ (EQ (c x y)) - δQ (c x y) := by
  simp only [hδc, hEc, map_add, map_sub, LinearMap.sub_apply, hx, hy, hEt]
  abel

omit [Module R M] [GrSpecies R V] in
private lemma alg_of_dft {a b c : M} (h : a - b + c = 0) : a = b - c := by
  rw [← sub_eq_zero, ← h]
  abel

omit [Module R M] [GrSpecies R V] in
private lemma alg_to_dft {a b c : M} (h : a = b - c) : a - b + c = 0 := by
  rw [h]
  abel

omit [GrSpecies R V] in
private lemma alg_succ (j : ℕ) (z : M) : ((j + 1 : ℕ) : R) • z - z = (j : R) • z := by
  rw [Nat.cast_succ, add_smul, one_smul, add_sub_cancel_right]

end Helpers

namespace Cobar

variable (δ : GrDer (GrOperadHom.id R (CobarGr R (FreeGrL R V))) true)
  (ϑ : ∀ (A : Type) [Fintype A] [DecidableEq A], FreeGrL R V A →ₗ[R] FreeGrL R V A)

/-! ### An inner differential lowers the weight by one -/

/-- The defect `E δ - δ E + δ`. -/
private noncomputable def dft (A : Type) [Fintype A] [DecidableEq A] :
    CobarGr R 𝒞 A →ₗ[R] CobarGr R 𝒞 A :=
  (wtΩ R V).app A ∘ₗ δ.app A - δ.app A ∘ₗ (wtΩ R V).app A + δ.app A

private lemma dft_apply (Y : CobarGr R 𝒞 A) :
    dft δ A Y = (wtΩ R V).app A (δ.app A Y) - δ.app A ((wtΩ R V).app A Y) + δ.app A Y := rfl

private lemma dft_map {A' : Type} [Fintype A'] [DecidableEq A'] (e : A ≃ A')
    (Y : CobarGr R 𝒞 A) :
    dft δ A' (GrOperad.map (R := R) e Y) = GrOperad.map (R := R) e (dft δ A Y) := by
  have h1 : (wtΩ R V).app A' (δ.app A' (GrOperad.map (R := R) e Y))
      = GrOperad.map (R := R) e ((wtΩ R V).app A (δ.app A Y)) :=
    (congrArg _ (δ.app_map e Y)).trans ((wtΩ R V).app_map e _)
  have h2 : δ.app A' ((wtΩ R V).app A' (GrOperad.map (R := R) e Y))
      = GrOperad.map (R := R) e (δ.app A ((wtΩ R V).app A Y)) :=
    (congrArg _ ((wtΩ R V).app_map e Y)).trans (δ.app_map e _)
  exact (dft_apply δ _).trans ((congrArg₂ (· + ·) (congrArg₂ (· - ·) h1 h2) (δ.app_map e Y)).trans
    (((congrArg₂ (· + ·) (map_sub (GrOperad.map (R := R) e) _ _).symm rfl).trans
      (map_add (GrOperad.map (R := R) e) _ _).symm).trans
        (congrArg (GrOperad.map (R := R) e) (dft_apply δ Y)).symm))

private lemma dft_ιL (hδ : ∀ (A : Type) [Fintype A] [DecidableEq A] (c : 𝒞 A),
      δ.app A (Cobar.ιL R 𝒞 A c) = Cobar.ιL R 𝒞 A (ϑ A c))
    (hϑ : ∀ (A : Type) [Fintype A] [DecidableEq A] (c : 𝒞 A),
      (FreeGrL.wtD R V).app A (ϑ A c) = ϑ A ((FreeGrL.wtD R V).app A c) - ϑ A c)
    (c : 𝒞 A) : dft δ A (Cobar.ιL R 𝒞 A c) = 0 := by
  have h1 : (wtΩ R V).app A (δ.app A (Cobar.ιL R 𝒞 A c))
      = Cobar.ιL R 𝒞 A ((FreeGrL.wtD R V).app A (ϑ A c)) :=
    (congrArg _ (hδ A c)).trans (wtΩ_ιL _)
  have h2 : δ.app A ((wtΩ R V).app A (Cobar.ιL R 𝒞 A c))
      = Cobar.ιL R 𝒞 A (ϑ A ((FreeGrL.wtD R V).app A c)) :=
    (congrArg _ (wtΩ_ιL c)).trans (hδ A _)
  have h4 : (FreeGrL.wtD R V).app A (ϑ A c) - ϑ A ((FreeGrL.wtD R V).app A c) + ϑ A c = 0 :=
    alg_to_dft (hϑ A c)
  exact (dft_apply δ _).trans ((congrArg₂ (· + ·) (congrArg₂ (· - ·) h1 h2) (hδ A c)).trans
    ((congrArg₂ (· + ·) (map_sub (Cobar.ιL R 𝒞 A) _ _).symm rfl).trans
      ((map_add (Cobar.ιL R 𝒞 A) _ _).symm.trans ((congrArg _ h4).trans (map_zero _)))))

private lemma dft_unit (e : Unit ≃ A) :
    dft δ A (GrOperad.map (R := R) e (GrOperad.one (R := R) (P := CobarGr R 𝒞))) = 0 := by
  have hE : (wtΩ R V).app A
      (GrOperad.map (R := R) e (GrOperad.one (R := R) (P := CobarGr R 𝒞))) = 0 :=
    ((wtΩ R V).app_map e _).trans ((congrArg _ (wtΩ R V).app_one).trans (map_zero _))
  have hδ : δ.app A (GrOperad.map (R := R) e (GrOperad.one (R := R) (P := CobarGr R 𝒞))) = 0 :=
    (δ.app_map e _).trans ((congrArg _ δ.app_one).trans (map_zero _))
  exact (dft_apply δ _).trans ((congrArg₂ (· + ·) (congrArg₂ (· - ·)
    ((congrArg _ hδ).trans (map_zero _)) ((congrArg _ hE).trans (map_zero _))) hδ).trans
      ((add_zero _).trans (sub_self 0)))

private lemma dft_comp (r : A) {X : CobarGr R 𝒞 A} {Y : CobarGr R 𝒞 B} (hX : dft δ A X = 0)
    (hY : dft δ B Y = 0) : dft δ _ (GrOperad.comp (R := R) r X Y) = 0 :=
  (dft_apply δ _).trans (alg_to_dft (alg_Eδ (GrOperad.comp (R := R) r)
    ((wtΩ R V).app A) (δ.app A) (GrOperad.tw (R := R) true) ((wtΩ R V).app B) (δ.app B)
    ((wtΩ R V).app _) (δ.app _) (fun x y => δ.app_comp r x y) (wtΩ_comp r) wtΩ_tw X Y
    (alg_of_dft ((dft_apply δ X).symm.trans hX)) (alg_of_dft ((dft_apply δ Y).symm.trans hY))))

private lemma dft_corolla (hδ : ∀ (A : Type) [Fintype A] [DecidableEq A] (c : 𝒞 A),
      δ.app A (Cobar.ιL R 𝒞 A c) = Cobar.ιL R 𝒞 A (ϑ A c))
    (hϑ : ∀ (A : Type) [Fintype A] [DecidableEq A] (c : 𝒞 A),
      (FreeGrL.wtD R V).app A (ϑ A c) = ϑ A ((FreeGrL.wtD R V).app A c) - ϑ A c)
    {k : ℕ} (g : GrGen R (CobarGen R 𝒞) k) (e : Fin k ≃ A) :
    dft δ A ((𝒥Ω).proj A (𝔅 (SetOperad.map e (Reg.std (corolla g))))) = 0 :=
  (exists_ιL_eq (R := R) (V := V) g.1.1).elim fun _ hy =>
    (congrArg (dft δ A) ((FreeGrL.proj_bas_map e _).trans (congrArg (GrOperad.map (R := R) e)
      ((FreeGrL.proj_bas_corolla g).trans hy.symm)))).trans
      ((dft_map δ e _).trans ((congrArg _ (dft_ιL δ ϑ hδ hϑ _)).trans (map_zero _)))

private lemma dft_comp_bas {A₁ B₁ : Type} [Fintype A₁] [DecidableEq A₁] [Fintype B₁]
    [DecidableEq B₁] (r : A₁) (p : Reg (TreeOfArity (GrGen R (CobarGen R 𝒞))) A₁)
    (q : Reg (TreeOfArity (GrGen R (CobarGen R 𝒞))) B₁) (e : Without A₁ r ⊕ B₁ ≃ A)
    (hp : dft δ A₁ ((𝒥Ω).proj A₁ (𝔅 p)) = 0) (hq : dft δ B₁ ((𝒥Ω).proj B₁ (𝔅 q)) = 0) :
    dft δ A ((𝒥Ω).proj A (𝔅 (SetOperad.map e (SetOperad.comp r p q)))) = 0 :=
  (congrArg (dft δ A) ((FreeGrL.proj_bas_map e _).trans (congrArg (GrOperad.map (R := R) e)
    (FreeGrL.proj_bas_comp r p q)))).trans ((dft_map δ e _).trans ((congrArg _
      ((map_smul _ _ _).trans ((congrArg _ (dft_comp δ r hp hq)).trans (smul_zero _)))).trans
        (map_zero _)))

private theorem dft_bas (hδ : ∀ (A : Type) [Fintype A] [DecidableEq A] (c : 𝒞 A),
      δ.app A (Cobar.ιL R 𝒞 A c) = Cobar.ιL R 𝒞 A (ϑ A c))
    (hϑ : ∀ (A : Type) [Fintype A] [DecidableEq A] (c : 𝒞 A),
      (FreeGrL.wtD R V).app A (ϑ A c) = ϑ A ((FreeGrL.wtD R V).app A c) - ϑ A c)
    (x : Reg (TreeOfArity (GrGen R (CobarGen R 𝒞))) A) :
    dft δ A ((𝒥Ω).proj A (𝔅 x)) = 0 :=
  tree_induction (motive := fun A _ _ x => dft δ A ((𝒥Ω).proj A (𝔅 x)) = 0)
    (fun _ _ _ _ hl => (FreeGrL.proj_bas_leaf hl).elim fun e he =>
      (congrArg _ he).trans (dft_unit δ e))
    (fun _ _ _ _ g e => dft_corolla δ ϑ hδ hϑ g e)
    (fun _ _ _ _ _ _ _ _ _ r p q e _ _ hp hq => dft_comp_bas δ r p q e hp hq) A x

/-- **An inner differential lowers the weight by one**: an odd derivation `δ` extending
`s⁻¹ c̄ ↦ s⁻¹ (ϑ c)‾` with `E ϑ = ϑ E - ϑ` on the cut cooperad satisfies `E δ = δ E - δ`. -/
theorem wtΩ_δ (hδ : ∀ (A : Type) [Fintype A] [DecidableEq A] (c : 𝒞 A),
      δ.app A (Cobar.ιL R 𝒞 A c) = Cobar.ιL R 𝒞 A (ϑ A c))
    (hϑ : ∀ (A : Type) [Fintype A] [DecidableEq A] (c : 𝒞 A),
      (FreeGrL.wtD R V).app A (ϑ A c) = ϑ A ((FreeGrL.wtD R V).app A c) - ϑ A c)
    (Y : CobarGr R 𝒞 A) :
    (wtΩ R V).app A (δ.app A Y) = δ.app A ((wtΩ R V).app A Y) - δ.app A Y := by
  refine alg_of_dft ((dft_apply δ Y).symm.trans ?_)
  have h := Function.surjInv_eq ((𝒥Ω).proj_surjective A) Y
  rw [← h]
  exact lin_eq_zero_of_single (dft δ A ∘ₗ (𝒥Ω).proj A) (fun x => dft_bas δ ϑ hδ hϑ x) _

/-! ### The acyclicity of the cobar construction with an inner differential -/

section Acyclic

variable (hδ : ∀ (A : Type) [Fintype A] [DecidableEq A] (c : FreeGrL R V A),
      δ.app A (Cobar.ιL R (FreeGrL R V) A c) = Cobar.ιL R (FreeGrL R V) A (ϑ A c))
    (hϑ : ∀ (A : Type) [Fintype A] [DecidableEq A] (c : FreeGrL R V A),
      (FreeGrL.wtD R V).app A (ϑ A c) = ϑ A ((FreeGrL.wtD R V).app A c) - ϑ A c)

include hδ hϑ in
lemma δ_mem_wt {j : ℕ} {Y : CobarGr R 𝒞 A} (hY : Y ∈ wt R V (j + 1) A) :
    δ.app A Y ∈ wt R V j A :=
  mem_wt.2 ((wtΩ_δ δ ϑ hδ hϑ Y).trans ((congrArg (fun z => δ.app A z - δ.app A Y)
    (mem_wt.1 hY)).trans ((congrArg (· - δ.app A Y) (map_smul _ _ _)).trans (alg_succ _ _))))

lemma δ_wt0 [Algebra ℚ R] {Y : CobarGr R 𝒞 A} (hY : Y ∈ wt R V 0 A) : δ.app A Y = 0 := by
  have hu := mem_unitsΩ_of_mem_wt hY
  clear hY
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨e, rfl⟩ := hy
    exact (δ.app_map e _).trans ((congrArg _ δ.app_one).trans (map_zero _))
  | zero => exact map_zero _
  | add y z _ _ hy hz => exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hy hz).trans (add_zero 0))
  | smul a y _ hy => exact (map_smul _ _ _).trans ((congrArg _ hy).trans (smul_zero _))

variable {Q : Type*} [AddCommGroup Q] [Module R Q] (c : CobarGr R (FreeGrL R V) A →ₗ[R] Q)

/-- The counit-like map is injective on the parts of weight at most one. -/
private lemma base_of [Algebra ℚ R]
    (hbase : ∀ u ∈ unitsΩ R V A, ∀ v : V A,
      c (u + Cobar.ιL R 𝒞 A ((FreeGrL.ι R V).app A v)) = 0 →
        u + Cobar.ιL R 𝒞 A ((FreeGrL.ι R V).app A v) = 0)
    {y₀ y₁ : CobarGr R 𝒞 A} (h₀ : y₀ ∈ wt R V 0 A) (h₁ : y₁ ∈ wt R V 1 A)
    (h : c (y₀ + y₁) = 0) : y₀ + y₁ = 0 :=
  (mem_corGen_of_mem_wt h₁).elim fun v hv => by
    have hv' : Cobar.ιL R 𝒞 A ((FreeGrL.ι R V).app A v) = y₁ := hv
    rw [← hv'] at h ⊢
    exact hbase y₀ (mem_unitsΩ_of_mem_wt h₀) v h

include hδ hϑ in
/-- **The acyclicity of the cobar construction with an inner differential**: for a differential
`D = d - δ`, `δ` an inner differential, over a `ℚ`-algebra, without generators without inputs, a
`D`-cycle killed by a map `c` with `c ∘ D = 0`, injective on the units and the generators of the
corollas, is a `D`-boundary. -/
theorem exists_sub_eq [Algebra ℚ R] (hV0 : ∀ v : V (Fin 0), v = 0)
    (hDD : ∀ y : CobarGr R 𝒞 A, (Cobar.d R 𝒞).app A ((Cobar.d R 𝒞).app A y - δ.app A y)
      - δ.app A ((Cobar.d R 𝒞).app A y - δ.app A y) = 0)
    (hc : ∀ y, c ((Cobar.d R 𝒞).app A y - δ.app A y) = 0)
    (hbase : ∀ u ∈ unitsΩ R V A, ∀ v : V A,
      c (u + Cobar.ιL R 𝒞 A ((FreeGrL.ι R V).app A v)) = 0 →
        u + Cobar.ιL R 𝒞 A ((FreeGrL.ι R V).app A v) = 0)
    (y : CobarGr R 𝒞 A) (hy : (Cobar.d R 𝒞).app A y - δ.app A y = 0) (hcy : c y = 0) :
    ∃ z, (Cobar.d R 𝒞).app A z - δ.app A z = y := by
  letI := (isInternal_wt (R := R) (V := V) (A := A)).chooseDecomposition
  exact exists_eq_D_of_weights (fun j => wt R V j A) ((wtΩ R V).app A) ((Cobar.d R 𝒞).app A)
    (hM R V A) (δ.app A) (FreeGrL.secC R (CobarGen R 𝒞) A) c
    (fun _ _ hy => mem_wt.1 hy) (fun _ _ hy => d_mem_wt hV0 hy)
    (fun _ _ hy => δ_mem_wt δ ϑ hδ hϑ hy) (fun _ hy => δ_wt0 δ hy) hDD
    (fun y => dh_hd hV0 y) (fun y => secC_sub_mem_wt y) hc
    (fun _ h₀ _ h₁ h => base_of c hbase h₀ h₁ h) y hy hcy

include hδ hϑ in
/-- **The units and the generators of the corollas are cycles** under the hypotheses of
`exists_sub_eq`. -/
theorem sub_eq_zero_of_low [Algebra ℚ R] (hV0 : ∀ v : V (Fin 0), v = 0)
    (hc : ∀ y, c ((Cobar.d R 𝒞).app A y - δ.app A y) = 0)
    (hbase : ∀ u ∈ unitsΩ R V A, ∀ v : V A,
      c (u + Cobar.ιL R 𝒞 A ((FreeGrL.ι R V).app A v)) = 0 →
        u + Cobar.ιL R 𝒞 A ((FreeGrL.ι R V).app A v) = 0)
    {u : CobarGr R 𝒞 A} (hu : u ∈ unitsΩ R V A) (v : V A) :
    (Cobar.d R 𝒞).app A (u + Cobar.ιL R 𝒞 A ((FreeGrL.ι R V).app A v))
      - δ.app A (u + Cobar.ιL R 𝒞 A ((FreeGrL.ι R V).app A v)) = 0 := by
  have h₀ : u ∈ wt R V 0 A := unitsΩ_le hu
  have h₁ : Cobar.ιL R 𝒞 A ((FreeGrL.ι R V).app A v) ∈ wt R V 1 A := corGen_le ⟨v, rfl⟩
  have hD : (Cobar.d R 𝒞).app A (u + Cobar.ιL R 𝒞 A ((FreeGrL.ι R V).app A v))
      - δ.app A (u + Cobar.ιL R 𝒞 A ((FreeGrL.ι R V).app A v))
      = ((Cobar.d R 𝒞).app A u - δ.app A (Cobar.ιL R 𝒞 A ((FreeGrL.ι R V).app A v)))
        + (Cobar.d R 𝒞).app A (Cobar.ιL R 𝒞 A ((FreeGrL.ι R V).app A v)) :=
    (congrArg₂ (· - ·) (map_add ((Cobar.d R 𝒞).app A) _ _) ((map_add (δ.app A) _ _).trans
      ((congrArg (· + δ.app A (Cobar.ιL R 𝒞 A ((FreeGrL.ι R V).app A v))) (δ_wt0 δ h₀)).trans
        (zero_add _)))).trans (add_sub_right_comm _ _ _)
  refine hD.trans (base_of c hbase (Submodule.sub_mem _ (d_mem_wt hV0 h₀)
    (δ_mem_wt δ ϑ hδ hϑ h₁)) (d_mem_wt hV0 h₁) ?_)
  exact (congrArg c hD).symm.trans (hc _)

end Acyclic

/-! ### Linear maps on the units -/

lemma map_mem_of_unitsΩ {N : Type*} [AddCommGroup N] [Module R N]
    (φ : CobarGr R 𝒞 A →ₗ[R] N) {S : Submodule R N}
    (h : ∀ e : Unit ≃ A,
      φ (GrOperad.map (R := R) e (GrOperad.one (R := R) (P := CobarGr R 𝒞))) ∈ S)
    {Y : CobarGr R 𝒞 A} (hY : Y ∈ unitsΩ R V A) : φ Y ∈ S := by
  induction hY using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨e, rfl⟩ := hy
    exact h e
  | zero => exact (congrArg (· ∈ S) (map_zero φ)).mpr (zero_mem _)
  | add y z _ _ hy hz => exact (congrArg (· ∈ S) (map_add φ y z)).mpr (add_mem hy hz)
  | smul a y _ hy => exact (congrArg (· ∈ S) (map_smul φ a y)).mpr (Submodule.smul_mem _ a hy)

/-- **A linear map injective on the multiples of the units is injective on their span.** -/
lemma eq_zero_of_unitsΩ {N : Type*} [AddCommGroup N] [Module R N]
    (φ : CobarGr R 𝒞 A →ₗ[R] N)
    (h : ∀ (e : Unit ≃ A) (a : R),
      a • φ (GrOperad.map (R := R) e (GrOperad.one (R := R) (P := CobarGr R 𝒞))) = 0 → a = 0)
    {Y : CobarGr R 𝒞 A} (hY : Y ∈ unitsΩ R V A) (hφ : φ Y = 0) : Y = 0 := by
  by_cases hA : Nonempty (Unit ≃ A)
  · obtain ⟨e₀⟩ := hA
    haveI : Unique (Unit ≃ A) := @uniqueOfSubsingleton _ ⟨fun e₁ e₂ => Equiv.ext fun u => by
      have hA : ∀ a a' : A, a = a' := fun a a' => by
        rw [← e₀.apply_symm_apply a, ← e₀.apply_symm_apply a']
      exact hA _ _⟩ e₀
    rw [unitsΩ, Set.range_unique] at hY
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hY
    exact (congrArg (· • GrOperad.map (R := R) (default : Unit ≃ A)
      (GrOperad.one (R := R) (P := CobarGr R 𝒞)))
        (h default a ((map_smul φ a _).symm.trans hφ))).trans (zero_smul R _)
  · have hb : Set.range (fun e : Unit ≃ A =>
        GrOperad.map (R := R) e (GrOperad.one (R := R) (P := CobarGr R 𝒞))) = ∅ :=
      Set.range_eq_empty_iff.2 (not_nonempty_iff.1 hA)
    rw [unitsΩ, hb, Submodule.span_empty, Submodule.mem_bot] at hY
    exact hY

end Cobar

end Inner

end Operad
