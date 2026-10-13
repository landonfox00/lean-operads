/-
# The cobar construction of the Koszul dual cooperad

The Koszul dual cooperad of the shuffle operad `P` presented by relators `R` is, up to the signs of
the operadic suspension, the linear dual of the Koszul dual operad `P^!`, presented by the Koszul
dual relators `R^! = dualRel R`; so its cobar construction is the linear dual of the bar
construction of `P^!`. On bar trees, with the pairing in which they are orthonormal
(`ShuffleBar.pairL`):

* **the cobar differential** (`ShuffleBar.δ`) cuts an uncut edge, with the sign of the merge it
  undoes: it is the transpose of the bar differential (`ShuffleBar.pairL_d_δ`), and squares to
  zero (`ShuffleBar.δ_δ`);
* **the cobar construction** (`ShuffleBar.Cobar R n s`) is, in arity `n` and degree `s` (the
  number of components), the chains orthogonal to the relator subcomplex of `R^!`, which `δ`
  preserves (`ShuffleBar.δ_mem_cobarOf`); in degree one it is the Koszul dual cooperad on the
  monomials, the orthogonal of the ideal of `R^!` (`ShuffleBar.KDmono_eq_orthogonal`);
* **a chain orthogonal to the cycles of the bar construction of `P^!` is a cobar boundary**
  (`ShuffleBar.exists_δ_eq`), a linear functional extended from the boundaries and the relator
  subcomplex;
* so **if `P^!` is Koszul, the cobar construction is exact below the top degree**
  (`ShuffleBar.exact_cobarOf`), and in the top degree, the fully cut bar trees, its boundaries are
  the ideal of `R` on the monomials (`ShuffleBar.map_δ_cobar_top`), for every `R`.

With the Koszulness of the Koszul dual of a quadratic Gröbner basis (`ShuffleBar.isKoszul_dualRel`):
**the cobar construction of the Koszul dual cooperad of a shuffle operad with a quadratic Gröbner
basis is a resolution of it** (`ShuffleBar.cobar_resolution`): exact below the top degree, where
it is the free operad on all the monomials, modulo the ideal of the relators.
-/
import Operad.ShuffleDualKoszul

namespace Operad

namespace ShuffleBar

open LTree Module

variable {E : Type*} [Fintype E] [DecidableEq E] {K : Type*} [Field K]

/-! ## The pairing and the cobar differential -/

variable (K) in
/-- **The pairing of chains** in which the bar trees are orthonormal. -/
noncomputable def pairL : (BarTree E →₀ K) →ₗ[K] (BarTree E →₀ K) →ₗ[K] K :=
  Finsupp.lsum K fun x => LinearMap.smulRight LinearMap.id (Finsupp.lapply x)

omit [Fintype E] [DecidableEq E] in
@[simp] lemma pairL_single (x : BarTree E) (a : K) (w : BarTree E →₀ K) :
    pairL K (Finsupp.single x a) w = a * w x := by
  simp [pairL]

omit [Fintype E] [DecidableEq E] in
@[simp] lemma pairL_single_right (v : BarTree E →₀ K) (x : BarTree E) (a : K) :
    pairL K v (Finsupp.single x a) = v x * a := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v v' hv hv' => rw [map_add, LinearMap.add_apply, hv, hv', Finsupp.add_apply, add_mul]
  | single y b =>
    rw [pairL_single, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs with h h' h'
    · rw [mul_comm]
    · exact absurd h.symm h'
    · exact absurd h'.symm h
    · simp

variable (K) in
/-- **The cobar differential of a bar tree**: the cuts of its uncut edges, each with the sign of
the merge it undoes. -/
noncomputable def δTree (x : BarTree E) : BarTree E →₀ K :=
  ∑ k ∈ (x.mapDec Prod.fst).edgeKeys \ cutKeys x,
    sgn K (cutK x k) k • Finsupp.single (cutK x k) 1

variable (K) in
/-- **The cobar differential.** -/
noncomputable def δ : (BarTree E →₀ K) →ₗ[K] (BarTree E →₀ K) :=
  Finsupp.linearCombination K (δTree K)

omit [Fintype E] [DecidableEq E] in
@[simp] lemma δ_single (x : BarTree E) (c : K) : δ K (Finsupp.single x c) = c • δTree K x := by
  simp [δ]

omit [Fintype E] [DecidableEq E] in
/-- **The cobar differential is the transpose of the bar differential**, on two valid bar
trees. -/
lemma dTree_apply_eq {x y : BarTree E} (hx : Valid x) (hy : Valid y) :
    dTree K y x = δTree K x y := by
  classical
  simp only [dTree, δTree, Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have hset : (cutKeys y).filter (fun k => mergeK y k = x) =
      ((x.mapDec Prod.fst).edgeKeys \ cutKeys x).filter (fun k => cutK x k = y) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hk, rfl⟩
      refine ⟨⟨?_, ?_⟩, cutK_mergeK hy.nodup hy.root hk⟩
      · rw [full_mergeK]
        exact cutKeys_subset_edgeKeys hy.root hk
      · rw [cutKeys_mergeK y hy.nodup hk]
        exact Finset.notMem_erase k _
    · rintro ⟨⟨hkE, hkc⟩, rfl⟩
      refine ⟨?_, mergeK_cutK hx.root hkc⟩
      rw [cutKeys_cutK hx.nodup hkE]
      exact Finset.mem_insert_self k _
  rw [hset]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [(Finset.mem_filter.1 hk).2]

omit [Fintype E] [DecidableEq E] in
lemma valid_of_supported {v : BarTree E →₀ K} (hv : v ∈ Finsupp.supported K K {x | Valid x})
    {x : BarTree E} (hx : v x ≠ 0) : Valid x :=
  (Finsupp.mem_supported K v).1 hv (Finsupp.mem_support_iff.2 hx)

omit [Fintype E] [DecidableEq E] in
/-- The cobar differential keeps the chains of valid bar trees. -/
lemma δ_mem_valid {v : BarTree E →₀ K} (hv : v ∈ Finsupp.supported K K {x | Valid x}) :
    δ K v ∈ Finsupp.supported K K {x | Valid x} := by
  refine map_mem_of_supported K (δ K) (fun y hy => ?_) hv
  rw [δ_single, one_smul, δTree]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
    (Finsupp.single_mem_supported K _ ?_)
  exact ⟨(isShuffle_cutK _ _).2 hy.shuffle, by simpa using hy.nodup,
    (rootFlag_cutK _ _).trans hy.root⟩

omit [Fintype E] [DecidableEq E] in
/-- The bar differential keeps the chains of valid bar trees. -/
lemma d_mem_valid {v : BarTree E →₀ K} (hv : v ∈ Finsupp.supported K K {x | Valid x}) :
    d K v ∈ Finsupp.supported K K {x | Valid x} := by
  refine map_mem_of_supported K (d K) (fun y hy => ?_) hv
  rw [d_single, one_smul, dTree]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
    (Finsupp.single_mem_supported K _ (Valid.mergeK hy k))

omit [Fintype E] [DecidableEq E] in
lemma C_valid {n s : ℕ} {v : BarTree E →₀ K} (hv : v ∈ C K n s) :
    v ∈ Finsupp.supported K K {x | Valid x} :=
  Finsupp.supported_mono (fun _ hx => hx.1) hv

omit [Fintype E] [DecidableEq E] in
/-- **The cobar differential is the transpose of the bar differential.** -/
theorem pairL_d_δ {v w : BarTree E →₀ K} (hv : v ∈ Finsupp.supported K K {x | Valid x})
    (hw : w ∈ Finsupp.supported K K {x | Valid x}) :
    pairL K (d K w) v = pairL K w (δ K v) := by
  have hsingle : ∀ y, Valid y → pairL K (d K (Finsupp.single y 1)) v =
      pairL K (Finsupp.single y 1) (δ K v) := fun y hy => by
    have := map_mem_of_supported K (P := ⊥)
      ((pairL K (d K (Finsupp.single y 1))) - (pairL K (Finsupp.single y 1)) ∘ₗ δ K)
      (fun x hx => by
        simp only [LinearMap.sub_apply, LinearMap.comp_apply, d_single, δ_single, one_smul,
          pairL_single_right, pairL_single, Submodule.mem_bot, mul_one, one_mul]
        rw [dTree_apply_eq hx hy, sub_self]) hv
    simpa [sub_eq_zero] using this
  have := map_mem_of_supported K (P := ⊥)
    ((pairL K).flip v ∘ₗ d K - (pairL K).flip (δ K v)) (fun y hy => by
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.flip_apply,
        Submodule.mem_bot]
      rw [hsingle y hy, sub_self]) hw
  simpa [sub_eq_zero] using this

omit [Fintype E] [DecidableEq E] in
/-- **The cobar differential squares to zero.** -/
theorem δ_δ {v : BarTree E →₀ K} (hv : v ∈ Finsupp.supported K K {x | Valid x}) :
    δ K (δ K v) = 0 := by
  ext y
  by_cases hy : Valid y
  · have hy1 : Finsupp.single y (1 : K) ∈ Finsupp.supported K K {x | Valid x} :=
      Finsupp.single_mem_supported K _ hy
    have h1 := pairL_d_δ (δ_mem_valid hv) hy1
    have h2 := pairL_d_δ hv (d_mem_valid hy1)
    rw [d_single, one_smul] at h1 h2
    rw [d_dTree K y hy.nodup, map_zero, LinearMap.zero_apply] at h2
    rw [Finsupp.zero_apply, ← one_mul (δ K (δ K v) y), ← pairL_single, ← h1, ← h2]
  · rw [Finsupp.zero_apply]
    by_contra h
    exact hy (valid_of_supported (δ_mem_valid (δ_mem_valid hv)) h)

omit [Fintype E] [DecidableEq E] in
/-- **The cobar differential raises the degree**: a cut adds a component. -/
lemma δ_mem_C {n s : ℕ} {v : BarTree E →₀ K} (hv : v ∈ C K n s) : δ K v ∈ C K n (s + 1) := by
  refine map_mem_of_supported K (δ K) (fun y hy => ?_) hv
  rw [δ_single, one_smul, δTree]
  refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _
    (Finsupp.single_mem_supported K _ ?_)
  obtain ⟨hkE, hkc⟩ := Finset.mem_sdiff.1 hk
  refine ⟨⟨(isShuffle_cutK _ _).2 hy.1.shuffle, by simpa using hy.1.nodup,
    (rootFlag_cutK _ _).trans hy.1.root⟩, by simpa using hy.2.1, ?_⟩
  rw [cutKeys_cutK hy.1.nodup hkE, Finset.card_insert_of_notMem hkc, hy.2.2]

/-! ## The cobar construction -/

omit [Fintype E] [DecidableEq E] in
/-- A linear form vanishing on the kernel of a linear map factors through it. -/
lemma exists_comp_eq_of_ker_le {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (θ : V →ₗ[K] W) (ψ : V →ₗ[K] K) (h : LinearMap.ker θ ≤ LinearMap.ker ψ) :
    ∃ φ : W →ₗ[K] K, ∀ x, φ (θ x) = ψ x := by
  let φ₀ : LinearMap.range θ →ₗ[K] K :=
    (LinearMap.ker θ).liftQ ψ h ∘ₗ θ.quotKerEquivRange.symm.toLinearMap
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend φ₀
  refine ⟨φ, fun x => ?_⟩
  have := LinearMap.congr_fun hφ ⟨θ x, LinearMap.mem_range_self θ x⟩
  rw [LinearMap.comp_apply, Submodule.coe_subtype] at this
  rw [this]
  simp [φ₀]

omit [Fintype E] [DecidableEq E] in
/-- **A linear form given on the image of a subspace, vanishing on another subspace, extends to
the whole space** when it is well defined on their sum. -/
lemma exists_form_of_ker {M : Type*} [AddCommGroup M] [Module K M] (B Q : Submodule K M)
    (f : M →ₗ[K] M) (g : M →ₗ[K] K) (h : ∀ x ∈ B, ∀ j ∈ Q, f x + j = 0 → g x = 0) :
    ∃ φ : M →ₗ[K] K, (∀ x ∈ B, φ (f x) = g x) ∧ ∀ j ∈ Q, φ j = 0 := by
  let θ : (B × Q) →ₗ[K] M :=
    f ∘ₗ B.subtype ∘ₗ LinearMap.fst K B Q + Q.subtype ∘ₗ LinearMap.snd K B Q
  let ψ : (B × Q) →ₗ[K] K := g ∘ₗ B.subtype ∘ₗ LinearMap.fst K B Q
  have hker : LinearMap.ker θ ≤ LinearMap.ker ψ := by
    rintro ⟨x, j⟩ hxj
    exact h x x.2 j j.2 hxj
  obtain ⟨φ, hφ⟩ := exists_comp_eq_of_ker_le θ ψ hker
  refine ⟨φ, fun x hx => ?_, fun j hj => ?_⟩
  · simpa [θ, ψ] using hφ (⟨x, hx⟩, 0)
  · simpa [θ, ψ] using hφ (0, ⟨j, hj⟩)

variable (K) in
/-- **The dual of the bar construction of the operad presented by `R'`**, in arity `n` and degree
`s`: the chains of the bar trees of that arity and degree orthogonal to the relator subcomplex. -/
noncomputable def CobarOf (R' : Submodule K (Mono E 3 → K)) (n s : ℕ) :
    Submodule K (BarTree E →₀ K) where
  carrier := {v | v ∈ C K n s ∧ ∀ j ∈ J K R' ⊓ C K n s, pairL K j v = 0}
  add_mem' {v w} hv hw :=
    ⟨add_mem hv.1 hw.1, fun j hj => by rw [map_add, hv.2 j hj, hw.2 j hj, add_zero]⟩
  zero_mem' := ⟨zero_mem _, fun j _ => map_zero _⟩
  smul_mem' c v hv :=
    ⟨Submodule.smul_mem _ c hv.1, fun j hj => by rw [map_smul, hv.2 j hj, smul_zero]⟩

variable (K) in
/-- **The cobar construction of the Koszul dual cooperad** of the shuffle operad presented by `R`,
in arity `n` and degree `s`: the dual of the bar construction of the Koszul dual operad. -/
noncomputable abbrev Cobar (R : Submodule K (Mono E 3 → K)) (n s : ℕ) :
    Submodule K (BarTree E →₀ K) :=
  CobarOf K (dualRel K R) n s

variable {R' : Submodule K (Mono E 3 → K)}

/-- **The cobar differential preserves the cobar construction.** -/
theorem δ_mem_cobarOf {n s : ℕ} {v : BarTree E →₀ K} (hv : v ∈ CobarOf K R' n s) :
    δ K v ∈ CobarOf K R' n (s + 1) := by
  refine ⟨δ_mem_C hv.1, fun j hj => ?_⟩
  rw [← pairL_d_δ (C_valid hv.1) (C_valid hj.2)]
  exact hv.2 _ ⟨d_mem_J K R' hj.1, d_mem_C K hj.2⟩


/-- **A chain orthogonal to the cycles modulo the relator subcomplex is a cobar boundary**: the
functional `d x + j ↦ ⟨x, v⟩` on the boundaries and the relator subcomplex, well defined by the
hypothesis, extended to all the chains, is the pairing with a cochain whose cobar differential is
`v`. -/
theorem exists_δ_eq {n s : ℕ} {v : BarTree E →₀ K} (hvC : v ∈ C K n (s + 1))
    (hv : ∀ x ∈ C K n (s + 1), d K x ∈ J K R' → pairL K x v = 0) :
    ∃ u ∈ CobarOf K R' n s, δ K u = v := by
  classical
  obtain ⟨φ, hφd, hφJ⟩ := exists_form_of_ker (C (E := E) K n (s + 1)) (J K R' ⊓ C K n s) (d K)
    ((pairL K).flip v) fun x hx j hj hxj => by
      rw [LinearMap.flip_apply]
      refine hv x hx ?_
      rw [eq_neg_of_add_eq_zero_left hxj]
      exact neg_mem hj.1
  set T := (barTrees (E := E) n).filter fun z => Adm n s z with hT
  set u : BarTree E →₀ K := ∑ z ∈ T, φ (Finsupp.single z 1) • Finsupp.single z 1 with hu
  have huA : u ∈ C K n s := Submodule.sum_mem _ fun z hz =>
    Submodule.smul_mem _ _ (Finsupp.single_mem_supported K _ (Finset.mem_filter.1 hz).2)
  -- the pairing with `u` is `φ` on the chains of degree `s`
  have hpair : ∀ c ∈ C K n s, pairL K c u = φ c := fun c hc => by
    have := map_mem_of_supported K (P := ⊥) ((pairL K).flip u - φ) (fun z hz => by
      have hzT : z ∈ T := Finset.mem_filter.2 ⟨mem_barTrees hz, hz⟩
      simp only [LinearMap.sub_apply, LinearMap.flip_apply, pairL_single, one_mul,
        Submodule.mem_bot, hu, Finsupp.finsetSum_apply, Finsupp.smul_apply,
        Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq' T z, if_pos hzT, sub_self]) hc
    simpa [sub_eq_zero] using this
  refine ⟨u, ⟨huA, fun j hj => ?_⟩, ?_⟩
  · rw [hpair j hj.2, hφJ j hj]
  · ext x
    by_cases hx : Adm n (s + 1) x
    · have hx1 : Finsupp.single x (1 : K) ∈ C K n (s + 1) := Finsupp.single_mem_supported K _ hx
      have h1 := pairL_d_δ (C_valid huA) (C_valid hx1)
      rw [pairL_single, one_mul] at h1
      rw [← h1, hpair _ (d_mem_C K hx1), hφd _ hx1, LinearMap.flip_apply, pairL_single, one_mul]
    · have h1 : δ K u x = 0 := by
        by_contra h
        exact hx ((Finsupp.mem_supported K _).1 (δ_mem_C huA) (Finsupp.mem_support_iff.2 h))
      have h2 : v x = 0 := by
        by_contra h
        exact hx ((Finsupp.mem_supported K _).1 hvC (Finsupp.mem_support_iff.2 h))
      rw [h1, h2]

/-- **If the operad presented by `R'` is Koszul, the dual of its bar construction is exact below
the top degree**: every cocycle is a coboundary. -/
theorem exact_cobarOf (hK : IsKoszul K R') {n s : ℕ} (hs : s + 2 < n) {v : BarTree E →₀ K}
    (hv : v ∈ CobarOf K R' n (s + 1)) (hδ : δ K v = 0) : ∃ u ∈ CobarOf K R' n s, δ K u = v := by
  refine exists_δ_eq hv.1 fun x hx hdx => ?_
  obtain ⟨y, hy, hxy⟩ := hK n (s + 1) (by omega) x hx hdx
  have h1 : pairL K (d K y) v = 0 := by
    rw [pairL_d_δ (C_valid hv.1) (C_valid hy), hδ, map_zero]
  have h2 : pairL K (x - d K y) v = 0 :=
    hv.2 _ ⟨hxy, Submodule.sub_mem _ hx (d_mem_C K hy)⟩
  rw [map_sub, LinearMap.sub_apply, h1, sub_zero] at h2
  exact h2

/-! ## The top degree -/

/-- **The pairing with a chain of top degree**, on the monomials. -/
lemma pairL_ofMono {n : ℕ} (x : BarTree E →₀ K) (f : Mono E n → K) :
    pairL K x (ofMono K n f) = ∑ m, toMono K n x m * f m := by
  show pairL K x (∑ m, ((tauS m.1 : K) * f m) • Finsupp.single (fullBar m.1) 1) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, pairL_single_right, smul_eq_mul]
  show (tauS m.1 : K) * f m * (x (fullBar m.1) * 1) = (tauS m.1 : K) * x (fullBar m.1) * f m
  ring

/-- **The cobar boundaries of top degree are the chains orthogonal to the Koszul dual cooperad of
`R'`**, the cycles of top degree of its bar construction. -/
theorem exists_δ_eq_top_iff {n : ℕ} (hn : 2 ≤ n) {c : BarTree E →₀ K} (hc : c ∈ C K n (n - 1)) :
    (∃ u ∈ CobarOf K R' n (n - 2), δ K u = c) ↔ ∀ x ∈ KD K R' n, pairL K x c = 0 := by
  have hn1 : n - 2 + 1 = n - 1 := by omega
  constructor
  · rintro ⟨u, hu, rfl⟩ x hx
    rw [← pairL_d_δ (C_valid hu.1) (C_valid hx.1)]
    exact hu.2 _ ⟨hx.2, d_mem_C K (by rw [hn1]; exact hx.1)⟩
  · intro h
    exact exists_δ_eq (by rw [hn1]; exact hc) fun x hx hdx => h x ⟨by rw [← hn1]; exact hx, hdx⟩

/-- **In the top degree, the cobar boundaries are the ideal of the relators**, on the monomials:
the cobar construction of the Koszul dual cooperad has, in its top degree, the homology of the
operad presented by `R`. -/
theorem map_δ_cobar_top (R : Submodule K (Mono E 3 → K)) {n : ℕ} (hn : 2 ≤ n) :
    (Cobar K R n (n - 2)).map (toMono K n ∘ₗ δ K) = idealOf K R n := by
  have hn1 : n - 2 + 1 = n - 1 := by omega
  rw [← dualRel_dualRel R, idealOf_dualRel_eq_orthogonal, dualRel_dualRel]
  ext f
  rw [Submodule.mem_map, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩ g hg
    rw [KDmono_eq_map _ hn] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    have hδ : δ K u ∈ C K n (n - 1) := by rw [← hn1]; exact δ_mem_C hu.1
    show diagForm _ _ _ = 0
    rw [diagForm_apply]
    simp only [one_mul, LinearMap.comp_apply]
    rw [← pairL_ofMono, ofMono_toMono hδ]
    exact (exists_δ_eq_top_iff hn hδ).1 ⟨u, hu, rfl⟩ x hx
  · intro h
    obtain ⟨u, hu, hδu⟩ := (exists_δ_eq_top_iff (R' := dualRel K R) hn (ofMono_mem_C hn f)).2
      fun x hx => by
        rw [pairL_ofMono]
        have := h (toMono K n x) (by rw [KDmono_eq_map _ hn]; exact ⟨x, hx, rfl⟩)
        rw [LinearMap.BilinForm.IsOrtho, diagForm_apply] at this
        simpa only [one_mul] using this
    exact ⟨u, hu, by rw [LinearMap.comp_apply, hδu, toMono_ofMono]⟩

/-! ## A quadratic Gröbner basis -/

variable {rk : E → ℕ} {L : Set (LTree E)} {R : Submodule K (Mono E 3 → K)}

/-- **The cobar construction of the Koszul dual cooperad of a shuffle operad with a quadratic
Gröbner basis is exact below the top degree.** -/
theorem exact_cobar (hG : IsGroebner K rk L R) {n s : ℕ} (hs : s + 2 < n) {v : BarTree E →₀ K}
    (hv : v ∈ Cobar K R n (s + 1)) (hδ : δ K v = 0) : ∃ u ∈ Cobar K R n s, δ K u = v :=
  exact_cobarOf (isKoszul_dualRel hG) hs hv hδ

/-- **In the top degree the cobar construction is all the chains**, the free operad on the
monomials: the relator subcomplex of the Koszul dual relators has no fully cut bar trees. -/
theorem cobar_top_eq (hG : IsGroebner K rk L R) (n : ℕ) :
    Cobar K R n (n - 1) = C K n (n - 1) := by
  refine le_antisymm (fun v hv => hv.1) fun v hv => ⟨hv, fun j hj => ?_⟩
  have hjN : j ∈ Finsupp.supported K K (Nrm {w | w ∉ L} n (n - 1)) :=
    Finsupp.supported_mono (fun x (hx : Adm n (n - 1) x) =>
      (⟨hx, adm_top_normal _ hx⟩ : x ∈ Nrm {w | w ∉ L} n (n - 1))) hj.2
  have hj0 : j = 0 := by
    rw [← ΦL_normal K (dualData hG) hjN, ΦL_J K (dualData hG) hj.1]
  rw [hj0, map_zero, LinearMap.zero_apply]

/-- **The cobar construction of the Koszul dual cooperad of a shuffle operad with a quadratic
Gröbner basis is a resolution of the operad**: in every arity `n ≥ 2` it is exact below the top
degree, where its chains are those of the free operad on the monomials and its boundaries are the
ideal of the relators. -/
theorem cobar_resolution (hG : IsGroebner K rk L R) {n : ℕ} (hn : 2 ≤ n) :
    (∀ s, s + 2 < n → ∀ v ∈ Cobar K R n (s + 1), δ K v = 0 → ∃ u ∈ Cobar K R n s, δ K u = v) ∧
      Cobar K R n (n - 1) = C K n (n - 1) ∧
      (Cobar K R n (n - 2)).map (toMono K n ∘ₗ δ K) = idealOf K R n :=
  ⟨fun _ hs _ hv hδ => exact_cobar hG hs hv hδ, cobar_top_eq hG n, map_δ_cobar_top R hn⟩

end ShuffleBar

end Operad
