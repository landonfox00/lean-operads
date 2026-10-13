/-
# The Gerstenhaber operad has `n!` operations of arity `n`

The exterior algebra `Λ g` of the Lie algebra `g` of noncommutative polynomials in the letters `ℕ`
is a Gerstenhaber algebra (`Operad.ExtBV.gerAlg`), so the operations of `Ger` evaluate on the odd
inputs `gv a = ι [a]` of the letters.

* **Filling the two inputs of a binary operation** (`GerDim.gbin`): in the graded endomorphism
  operad its value is, up to a sign, the operation applied to the values of the inputs
  (`GerDim.gbin_fam_apply`).
* **The values of the homogeneous operations on the letters `s`** (`GerDim.Tsp`) contain the inputs
  (`GerDim.gv_mem_Tsp`) and, for disjoint sets of letters, their products and brackets
  (`GerDim.mul_mem_Tsp`, `GerDim.dv_mem_Tsp`). So they contain the products of left-normed brackets
  of the blocks of a permutation (`GerDim.leadE_mem_Tsp`), the blocks cut before the left-to-right
  minima as for `Pois`.
* **These are independent** (`GerDim.linearIndependent_leadE`): a left-normed bracket is up to sign
  the vector of the left-normed commutator of its word (`GerDim.combE_eq`), and killing the words
  whose first letter is not the least leaves the word itself (`GerDim.kill_lc`). The products
  become, up to sign, distinct vectors of the basis of the exterior algebra indexed by sets of
  words (`GerDim.map_prodE`).

With the upper bound (`Operad.GerDim.finite_finrank_le`): **`dim Ger(n) = n!`**
(`GerDim.finrank_ger`, `GerDim.finrank_ger_eq`), over any field.
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Operad.ExteriorBV
import Operad.PoisModel
import Operad.GerPBW

universe u v w

namespace Operad

namespace GerDim

open Sym GrEnd EndGr

/-! ## Filling the two inputs of a binary operation -/

section Bin

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable (R) in
/-- **Fill the two inputs of a binary operation**, in a graded operad. -/
noncomputable def gbin (g : P (Fin 2)) (x : P A) (y : P B) : P (A ⊕ B) :=
  GrOperad.map (R := R) (binEquiv A B)
    (GrOperad.comp (R := R) (Sum.inl slotOne) (GrOperad.comp (R := R) (0 : Fin 2) g x) y)

lemma gbin_par {r p q : Bool} {g : P (Fin 2)} {x : P A} {y : P B}
    (hg : GrOperad.par (R := R) r g = g) (hx : GrOperad.par (R := R) p x = x)
    (hy : GrOperad.par (R := R) q y = y) :
    GrOperad.par (R := R) (xor (xor r p) q) (gbin R g x y) = gbin R g x y := by
  unfold gbin
  rw [← GrOperad.map_par]
  congr 1
  have h1 := GrOperad.comp_par (R := R) (P := P) (0 : Fin 2) r p g x
  rw [hg, hx] at h1
  have h2 := GrOperad.comp_par (R := R) (P := P) (Sum.inl slotOne) (xor r p) q
    (GrOperad.comp (R := R) (0 : Fin 2) g x) y
  rw [h1, hy] at h2
  exact h2

lemma app_gbin {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
    (φ : GrOperadHom R P Q) (g : P (Fin 2)) (x : P A) (y : P B) :
    φ.app _ (gbin R g x y) = gbin R (φ.app _ g) (φ.app _ x) (φ.app _ y) := by
  unfold gbin
  rw [φ.app_map, φ.app_comp, φ.app_comp]

end Bin

section EndBin

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V] [SuperMod R V]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **The value of a relabelled operation.** -/
lemma map_fam_apply (e : A ≃ B) (F : EndGr R V A) (L : LinOrd A) (x : B → V) :
    (GrOperad.map (R := R) e F).fam (LinOrd.map e L) x = F.fam L fun a => x (e a) := by
  show EndOp.mapL R V e (F.fam (LinOrd.map e.symm (LinOrd.map e L))) x = _
  rw [lo_map_symm_map]
  rfl

omit [DecidableEq A] in
lemma bsg_mul_self (L : LinOrd A) (i : A) (q : Bool) (c : A → Bool) :
    bsg R L i q c * bsg R L i q c = 1 := by
  rw [bsg_mul, Bool.xor_self, bsg_false]

/-- **The value of a binary operation with both inputs filled**, up to a sign. -/
theorem gbin_fam_apply (F : EndGr R V (Fin 2)) {p q : Bool} {G : EndGr R V A}
    {H : EndGr R V B} (hG : GrOperad.par (R := R) p G = G) (hH : GrOperad.par (R := R) q H = H)
    (M : LinOrd A) (N : LinOrd B) {c : A ⊕ B → Bool} {x : A ⊕ B → V}
    (hx : IsHom (R := R) c x) :
    ∃ s : R, s * s = 1 ∧
      (gbin R F G H).fam (LinOrd.map (binEquiv A B)
        (LinOrd.comp (Sum.inl slotOne) (LinOrd.comp 0 (LinOrd.std 2) M) N)) x
        = s • F.fam (LinOrd.std 2)
          ![G.fam M (fun a => x (Sum.inl a)), H.fam N (fun b => x (Sum.inr b))] := by
  have hG' : parML R V p (G.fam M) = G.fam M := by
    rw [← parE_fam]
    exact congrArg (fun X : EndGr R V A => X.fam M) hG
  have hH' : parML R V q (H.fam N) = H.fam N := by
    rw [← parE_fam]
    exact congrArg (fun X : EndGr R V B => X.fam N) hH
  have hx' : IsHom (R := R) (fun a => c (binEquiv A B a)) (fun a => x (binEquiv A B a)) :=
    fun a => hx _
  refine ⟨?s, ?_, ?_⟩
  rotate_left
  show EndOp.mapL R V (binEquiv A B) ((compE (Sum.inl slotOne) (compE 0 F G) H).fam
    (LinOrd.map (binEquiv A B).symm (LinOrd.map (binEquiv A B) _))) x = _
  rw [lo_map_symm_map, compE_fam, compFam_comp, compE_fam, compFam_comp]
  show kcomp R V _ _ _ _ (fun a => x (binEquiv A B a)) = _
  rw [kcomp_apply_hom _ _ _ hH' hx', kcomp_apply_hom _ _ _ hG' (isHom_feed _ hx' hH'), smul_smul]
  · congr 1
    · exact rfl
    congr 1
    funext k
    fin_cases k
    · simp only [Fin.zero_eta, Fin.isValue, feed_self, Matrix.cons_val_zero]
      congr 1
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [feed_of_ne (by decide)]
      exact feed_self _ _ _
  · rw [mul_mul_mul_comm, bsg_mul_self, bsg_mul_self, one_mul]

end EndBin

/-! ## The values of the operations in the exterior algebra of noncommutative polynomials -/

section Values

variable (K : Type u) [Field K]

/-- **The noncommutative polynomials** in the letters `ℕ`, a Lie algebra under the commutator. -/
abbrev Gw := MonoidAlgebra K (FreeMonoid ℕ)

/-- Their exterior algebra, a Gerstenhaber algebra. -/
abbrev Ew := ExteriorAlgebra K (Gw K)

/-- The basis vector of a word. -/
noncomputable def wd (u : List ℕ) : Gw K := MonoidAlgebra.single (FreeMonoid.ofList u) 1

/-- **The input attached to a letter**: the vector of the one-letter word, an odd element. -/
noncomputable def gv (a : ℕ) : Ew K := ExteriorAlgebra.ι K (wd K [a])

/-- **The algebra over `Ger`.** -/
noncomputable abbrev alg : GrAlgebra K (Ew K) (GerOp K) := ExtBV.gerAlg K (Gw K)

variable {K}

lemma isHom_gv {A : Type} [Fintype A] [DecidableEq A] (f : A → ℕ) :
    IsHom (R := K) (fun _ => true) fun a => gv K (f a) :=
  fun _ => (ExtBV.isP_iff true _).2 (ExtBV.ι_mem _)

/-- **Changing the order** multiplies a value at homogeneous inputs by a scalar. -/
lemma fam_change {V : Type v} [AddCommGroup V] [Module K V] [SuperMod K V] {A : Type}
    [Fintype A] [DecidableEq A] (F : EndGr K V A) (L L' : LinOrd A) {c : A → Bool} {x : A → V}
    (hx : IsHom (R := K) c x) : F.fam L' x = rsg K L L' c • F.fam L x := by
  rw [fam_compat F L L', twist_apply_hom hx]

variable (K) in
/-- **Evaluation at the inputs of the letters.** -/
noncomputable def ev (s : Finset ℕ) : GerOp K ↥s →ₗ[K] Ew K where
  toFun q := ((alg K).app ↥s q).fam (dord ↥s) fun a => gv K a.1
  map_add' q q' := by rw [map_add, add_fam]; rfl
  map_smul' c q := by rw [map_smul, smul_fam]; rfl

variable (K) in
/-- **The values of the homogeneous operations** on the letters `s`, at any order. -/
noncomputable def Tsp (s : Finset ℕ) : Submodule K (Ew K) :=
  Submodule.span K {y | ∃ (q : GerOp K ↥s) (b : Bool) (L : LinOrd ↥s),
    GrOperad.par (R := K) b q = q ∧ y = ((alg K).app ↥s q).fam L fun a => gv K a.1}

lemma val_mem_Tsp {s : Finset ℕ} {q : GerOp K ↥s} {b : Bool} (hq : GrOperad.par (R := K) b q = q)
    (L : LinOrd ↥s) : (((alg K).app ↥s q).fam L fun a => gv K a.1) ∈ Tsp K s :=
  Submodule.subset_span ⟨q, b, L, hq, rfl⟩

/-- **The values are values of the evaluation.** -/
lemma Tsp_le (s : Finset ℕ) : Tsp K s ≤ LinearMap.range (ev K s) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨q, b, L, -, rfl⟩
  refine ⟨rsg K (dord ↥s) L (fun _ => true) • q, ?_⟩
  rw [map_smul, fam_change _ (dord ↥s) L (isHom_gv _)]
  rfl

/-- **The input of a letter is a value**: of the unit. -/
lemma gv_mem_Tsp (a : ℕ) : gv K a ∈ Tsp K {a} := by
  let e : Unit ≃ ({a} : Finset ℕ) :=
    ⟨fun _ => ⟨a, Finset.mem_singleton_self a⟩, fun _ => (), fun _ => rfl,
      fun x => Subtype.ext (Finset.mem_singleton.1 x.2).symm⟩
  have hq : GrOperad.par (R := K) false (GrOperad.map (R := K) e (GrOperad.one (R := K)))
      = (GrOperad.map (R := K) e (GrOperad.one (R := K)) : GerOp K ↥({a} : Finset ℕ)) := by
    rw [← GrOperad.map_par, GrOperad.par_one]
  have h := val_mem_Tsp hq (dord _)
  rwa [GrOperadHom.app_map, GrOperadHom.app_one] at h

lemma par_presGen (e : GerGen 2) :
    GrOperad.par (R := K) (gerPar 2 e) (FreeGr.presGen (Ger.rel K) e)
      = FreeGr.presGen (Ger.rel K) e := by
  show GrOperad.par (R := K) _ ((GrOperadIdeal.span K (Ger.rel K)).projHom.app (Fin 2)
      (FreeGr.gen e)) = (GrOperadIdeal.span K (Ger.rel K)).projHom.app (Fin 2) (FreeGr.gen e)
  rw [← GrOperadHom.app_par, FreeGr.par_gen]

/-- **The values are closed under the operations of the generators**, on disjoint letters. -/
theorem binop_mem_Tsp (e : GerGen 2) (β : Ew K →ₗ[K] Ew K →ₗ[K] Ew K)
    (hβ : ∀ y z, EndGr.sv ((alg K).app _ (FreeGr.presGen (Ger.rel K) e)) ![y, z] = β y z)
    {s t : Finset ℕ} (h : Disjoint s t) {y z : Ew K} (hy : y ∈ Tsp K s) (hz : z ∈ Tsp K t) :
    β y z ∈ Tsp K (s ∪ t) := by
  have hm := Submodule.apply_mem_map₂ β hy hz
  rw [Tsp, Tsp, Submodule.map₂_span_span] at hm
  refine (Submodule.span_le.2 ?_) hm
  rintro _ ⟨_, ⟨q₁, b₁, L₁, hq₁, rfl⟩, _, ⟨q₂, b₂, L₂, hq₂, rfl⟩, rfl⟩
  set G := FreeGr.presGen (Ger.rel K) e
  have hq₁' : GrOperad.par (R := K) b₁ ((alg K).app _ q₁) = (alg K).app _ q₁ := by
    rw [← GrOperadHom.app_par, hq₁]
  have hq₂' : GrOperad.par (R := K) b₂ ((alg K).app _ q₂) = (alg K).app _ q₂ := by
    rw [← GrOperadHom.app_par, hq₂]
  have hQ : GrOperad.par (R := K) (xor (xor (gerPar 2 e) b₁) b₂)
      (GrOperad.map (R := K) (Equiv.Finset.union s t h) (gbin K G q₁ q₂))
      = GrOperad.map (R := K) (Equiv.Finset.union s t h) (gbin K G q₁ q₂) := by
    rw [← GrOperad.map_par, gbin_par (par_presGen e) hq₁ hq₂]
  obtain ⟨c, hc, hv⟩ := gbin_fam_apply ((alg K).app _ G) hq₁' hq₂' L₁ L₂
    (isHom_gv (K := K) fun a : ↥s ⊕ ↥t => (Equiv.Finset.union s t h a).1)
  have hval := val_mem_Tsp hQ (LinOrd.map (Equiv.Finset.union s t h) (LinOrd.map (binEquiv _ _)
    (LinOrd.comp (Sum.inl slotOne) (LinOrd.comp 0 (LinOrd.std 2) L₁) L₂)))
  rw [GrOperadHom.app_map, app_gbin] at hval
  have hQv : ((GrOperad.map (R := K) (Equiv.Finset.union s t h)
      (gbin K ((alg K).app _ G) ((alg K).app _ q₁) ((alg K).app _ q₂))).fam
      (LinOrd.map (Equiv.Finset.union s t h) (LinOrd.map (binEquiv _ _)
        (LinOrd.comp (Sum.inl slotOne) (LinOrd.comp 0 (LinOrd.std 2) L₁) L₂))))
      (fun a => gv K a.1)
      = c • β (((alg K).app _ q₁).fam L₁ fun a => gv K a.1)
        (((alg K).app _ q₂).fam L₂ fun a => gv K a.1) := by
    rw [map_fam_apply]
    exact hv.trans (congrArg (c • ·) (hβ _ _))
  rw [hQv] at hval
  have := Submodule.smul_mem _ c hval
  rwa [smul_smul, hc, one_smul] at this

/-- **Products of values on disjoint letters are values.** -/
lemma mul_mem_Tsp {s t : Finset ℕ} (h : Disjoint s t) {y z : Ew K} (hy : y ∈ Tsp K s)
    (hz : z ∈ Tsp K t) : y * z ∈ Tsp K (s ∪ t) :=
  binop_mem_Tsp GerGen.mul (LinearMap.mul K (Ew K))
    (fun y z => by rw [ExtBV.sv_gerAlg_mul]; rfl) h hy hz

/-- **Brackets of values on disjoint letters are values.** -/
lemma dv_mem_Tsp {s t : Finset ℕ} (h : Disjoint s t) {y z : Ew K} (hy : y ∈ Tsp K s)
    (hz : z ∈ Tsp K t) : ExtBV.dv K (Gw K) y z ∈ Tsp K (s ∪ t) :=
  binop_mem_Tsp GerGen.br (ExtBV.dv K (Gw K))
    (fun y z => by rw [ExtBV.sv_gerAlg_br]; rfl) h hy hz

end Values

/-! ## Left-normed brackets and their products -/

section Lead

open PoisDim

variable (K : Type u) [Field K]

/-- **The left-normed bracket** `⟨⟨a, c₁⟩, …, c_k⟩` of the inputs of a word. -/
noncomputable def combE : List ℕ → Ew K
  | [] => 0
  | a :: rest => rest.foldl (fun p c => ExtBV.dv K (Gw K) p (gv K c)) (gv K a)

variable {K}

lemma combE_single (a : ℕ) : combE K [a] = gv K a := rfl

lemma combE_append_single {w : List ℕ} (hw : w ≠ []) (c : ℕ) :
    combE K (w ++ [c]) = ExtBV.dv K (Gw K) (combE K w) (gv K c) := by
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hw
  simp only [List.cons_append, combE, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- **Left-normed brackets of words without repetition are values.** -/
theorem combE_mem_Tsp : ∀ (w : List ℕ), w.Nodup → w ≠ [] → combE K w ∈ Tsp K w.toFinset := by
  intro w
  induction w using List.reverseRecOn with
  | nil => intro _ h; exact absurd rfl h
  | append_singleton w c ih =>
    intro hnd _
    by_cases hw : w = []
    · subst hw
      simpa [combE_single] using gv_mem_Tsp (K := K) c
    · have hc : c ∉ w := by
        have := (List.nodup_append.1 hnd).2.2
        exact fun h => this c h c (List.mem_singleton_self c) rfl
      rw [combE_append_single hw, List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
        insert_empty_eq]
      exact dv_mem_Tsp (Finset.disjoint_singleton_right.2 (by simpa using hc))
        (ih (List.nodup_append.1 hnd).1 hw) (gv_mem_Tsp c)

variable (K) in
/-- **The product of the left-normed brackets** of blocks. -/
noncomputable def prodE (bs : List (List ℕ)) : Ew K := (bs.map (combE K)).prod

/-- **Products of left-normed brackets of disjoint blocks are values.** -/
theorem prodE_mem_Tsp : ∀ (bs : List (List ℕ)), bs ≠ [] → bs.flatten.Nodup → (∀ B ∈ bs, B ≠ []) →
    prodE K bs ∈ Tsp K bs.flatten.toFinset
  | [], h, _, _ => absurd rfl h
  | [B], _, hnd, hne => by
    simpa [prodE] using combE_mem_Tsp B (by simpa using hnd) (hne B (List.mem_singleton_self B))
  | B :: B' :: bs, _, hnd, hne => by
    rw [prodE, List.map_cons, List.prod_cons, List.flatten_cons, List.toFinset_append]
    have h1 := List.nodup_append.1 (List.flatten_cons ▸ hnd)
    refine mul_mem_Tsp ?_ (combE_mem_Tsp B h1.1 (hne B (by simp)))
      (prodE_mem_Tsp (B' :: bs) (by simp) h1.2.1 fun C hC => hne C (by simp [hC]))
    rw [List.disjoint_toFinset_iff_disjoint]
    exact fun a ha hb => h1.2.2 a ha a hb rfl

variable (K) in
/-- **The products of the left-normed brackets of the blocks of the permutations.** -/
noncomputable def leadE (n : ℕ) (l : (List.range n).permutations.toFinset) : Ew K :=
  prodE K (cut l.1)

/-- **They are values.** -/
theorem leadE_mem_Tsp {n : ℕ} (hn : 0 < n) (l : (List.range n).permutations.toFinset) :
    leadE K n l ∈ Tsp K (Finset.range n) := by
  have hl := nodup_of_mem l
  have hp : l.1.Perm (List.range n) := List.mem_permutations.1 (List.mem_toFinset.1 l.2)
  have h := prodE_mem_Tsp (K := K) (cut l.1) (fun h => by
      have hlen := hp.length_eq
      rw [← flatten_cut l.1, h] at hlen
      simp at hlen
      omega)
    (by rw [flatten_cut]; exact hl) fun B hB => (mem_cut l.1 B hB).1
  rwa [flatten_cut, List.toFinset_eq_of_perm _ _ hp, List.toFinset_range] at h

/-! ## Independence -/

variable (K) in
/-- **The left-normed commutator** of the letters of a word. -/
noncomputable def lc : List ℕ → Gw K
  | [] => 0
  | a :: rest => rest.foldl (fun p c => ⁅p, wd K [c]⁆) (wd K [a])

lemma lc_append_single {w : List ℕ} (hw : w ≠ []) (c : ℕ) :
    lc K (w ++ [c]) = ⁅lc K w, wd K [c]⁆ := by
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hw
  simp only [List.cons_append, lc, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- **A left-normed bracket of inputs is, up to sign, the vector of a left-normed commutator.** -/
theorem combE_eq : ∀ (w : List ℕ), w ≠ [] →
    ∃ c : K, c * c = 1 ∧ combE K w = c • ExteriorAlgebra.ι K (lc K w) := by
  intro w
  induction w using List.reverseRecOn with
  | nil => intro h; exact absurd rfl h
  | append_singleton w c ih =>
    intro _
    by_cases hw : w = []
    · subst hw
      exact ⟨1, one_mul 1, by rw [one_smul]; rfl⟩
    · obtain ⟨d, hd, h⟩ := ih hw
      refine ⟨-d, by rw [neg_mul_neg, hd], ?_⟩
      rw [combE_append_single hw, h, map_smul, LinearMap.smul_apply, gv, ExtBV.dv_ι_ι,
        lc_append_single hw, smul_neg, neg_smul]

lemma lie_wd (u v : List ℕ) : ⁅wd K u, wd K v⁆ = wd K (u ++ v) - wd K (v ++ u) := by
  rw [Ring.lie_def, wd, wd, MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single,
    one_mul, ← FreeMonoid.ofList_append, ← FreeMonoid.ofList_append]
  rfl

variable (K) in
/-- The span of the bad rearrangements of a word. -/
noncomputable def badG (w : List ℕ) : Submodule K (Gw K) :=
  Submodule.span K {p | ∃ u, u.Perm w ∧ Bad u ∧ p = wd K u}

/-- **A left-normed commutator is its word plus bad rearrangements**, for a word whose first
letter is its least. -/
theorem lc_sub_mem : ∀ (w : List ℕ), w.Nodup → w ≠ [] → (∀ a ∈ w, w.headI ≤ a) →
    lc K w - wd K w ∈ badG K w := by
  intro w
  induction w using List.reverseRecOn with
  | nil => intro _ h; exact absurd rfl h
  | append_singleton w c ih =>
    intro hnd _ hmin
    by_cases hw : w = []
    · subst hw
      rw [List.nil_append, show lc K [c] = wd K [c] from rfl, sub_self]
      exact zero_mem _
    · have hc : c ∉ w := by
        have := (List.nodup_append.1 hnd).2.2
        exact fun h => this c h c (List.mem_singleton_self c) rfl
      have hhead : (w ++ [c]).headI = w.headI := by
        obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hw
        rfl
      have hmin' : ∀ a ∈ w, w.headI ≤ a := fun a ha => hhead ▸ hmin a (by simp [ha])
      have hlt : w.headI < c := by
        have hle := hhead ▸ hmin c (by simp)
        refine lt_of_le_of_ne hle fun h => hc ?_
        rw [← h]
        obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hw
        simp
      have ih' := ih (List.nodup_append.1 hnd).1 hw hmin'
      have key : lc K (w ++ [c]) - wd K (w ++ [c]) =
          ⁅lc K w - wd K w, wd K [c]⁆ - wd K ([c] ++ w) := by
        rw [lc_append_single hw, sub_lie, lie_wd]
        abel
      rw [key]
      refine sub_mem ?_ (Submodule.subset_span ⟨[c] ++ w, List.perm_append_comm,
        ⟨w.headI, ?_, hlt⟩, rfl⟩)
      · refine Submodule.span_induction (p := fun p _ =>
          ⁅p, wd K [c]⁆ ∈ badG K (w ++ [c])) ?_ ?_ ?_ ?_ ih'
        · rintro _ ⟨u, hu, ⟨a, ha, hau⟩, rfl⟩
          have hune : u ≠ [] := fun h => hw (List.perm_nil.1 (h ▸ hu).symm)
          rw [lie_wd]
          refine sub_mem (Submodule.subset_span ⟨u ++ [c], hu.append_right _, ⟨a, by simp [ha],
            ?_⟩, rfl⟩) (Submodule.subset_span ⟨[c] ++ u, ?_, ⟨w.headI, ?_, hlt⟩, rfl⟩)
          · obtain ⟨b, rest, rfl⟩ := List.exists_cons_of_ne_nil hune
            exact hau
          · exact List.perm_append_comm.trans (hu.append_right _)
          · obtain ⟨b, rest, rfl⟩ := List.exists_cons_of_ne_nil hw
            exact List.mem_append_right _ (hu.symm.subset (List.mem_cons_self))
        · beta_reduce
          rw [zero_lie]
          exact zero_mem _
        · intro x y _ _ hx hy
          rw [add_lie]
          exact add_mem hx hy
        · intro a x _ hx
          rw [smul_lie]
          exact Submodule.smul_mem _ a hx
      · obtain ⟨b, rest, rfl⟩ := List.exists_cons_of_ne_nil hw
        simp

variable (K) in
/-- **The linear map killing the bad words.** -/
noncomputable def kill : Gw K →ₗ[K] Gw K :=
  Finsupp.linearCombination K fun u : FreeMonoid ℕ =>
    if Bad (FreeMonoid.toList u) then 0 else MonoidAlgebra.single u (1 : K)

lemma kill_wd (u : List ℕ) : kill K (wd K u) = if Bad u then 0 else wd K u := by
  rw [kill, wd, MonoidAlgebra.single]
  erw [Finsupp.linearCombination_single]
  rw [one_smul, FreeMonoid.toList_ofList]

lemma kill_badG {w : List ℕ} {p : Gw K} (hp : p ∈ badG K w) : kill K p = 0 := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, _, hu, rfl⟩ := hx
    rw [kill_wd, if_pos hu]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_smul, hx, smul_zero]

/-- **Killing the bad words in a left-normed commutator leaves its word.** -/
theorem kill_lc (w : List ℕ) (hnd : w.Nodup) (hne : w ≠ []) (hmin : ∀ a ∈ w, w.headI ≤ a) :
    kill K (lc K w) = wd K w := by
  have h := kill_badG (K := K) (lc_sub_mem w hnd hne hmin)
  rw [map_sub, sub_eq_zero, kill_wd, if_neg] at h
  · exact h
  · rintro ⟨a, ha, hlt⟩
    exact absurd (hmin a ha) (not_le.2 hlt)

end Lead

/-! ## The basis of the exterior algebra -/

section Basis

open PoisDim

variable (K : Type u) [Field K]

/-- The basis of the words. -/
noncomputable def bW : Module.Basis (List ℕ) K (Gw K) :=
  (Finsupp.basisSingleOne : Module.Basis (FreeMonoid ℕ) K (FreeMonoid ℕ →₀ K)).reindex
    FreeMonoid.toList

/-- **The basis of the exterior algebra**, indexed by the finite sets of words. -/
noncomputable def bE : Module.Basis (Finset (List ℕ)) K (Ew K) := (bW K).ExteriorAlgebra

variable {K}

lemma bW_apply (u : List ℕ) : bW K u = wd K u := by
  rw [bW]
  erw [Module.Basis.reindex_apply, Finsupp.coe_basisSingleOne]
  rfl

lemma bE_empty : bE K ∅ = 1 := by
  rw [bE, ExteriorAlgebra.basis_apply_ofCard (bW K) (n := 0) Finset.card_empty]
  simp [ExteriorAlgebra.ιMulti_apply]

lemma bE_singleton (w : List ℕ) : bE K {w} = ExteriorAlgebra.ι K (wd K w) := by
  rw [bE, ExteriorAlgebra.basis_apply_ofCard (bW K) (n := 1) (Finset.card_singleton w)]
  simp only [ExteriorAlgebra.ιMulti_apply, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
    List.prod_nil, mul_one, Function.comp_apply]
  have h := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
    (Set.powersetCard.ofCard (Finset.card_singleton w)) _).1 ⟨0, rfl⟩
  rw [← Set.powersetCard.mem_coe_iff, Set.powersetCard.val_ofCard, Finset.mem_singleton] at h
  rw [h, bW_apply]

/-- **Wedging a basis vector of a new word.** -/
lemma ι_mul_bE (w : List ℕ) (T : Finset (List ℕ)) (hw : w ∉ T) :
    ∃ c : K, c * c = 1 ∧ ExteriorAlgebra.ι K (wd K w) * bE K T = c • bE K (insert w T) := by
  have hd : Disjoint (Set.powersetCard.ofCard (Finset.card_singleton w)).val
      (Set.powersetCard.ofCard (rfl : T.card = T.card)).val := by
    simpa using hw
  have h := ExteriorAlgebra.basis_mul_of_disjoint (bW K) _ _ hd
  rw [Set.powersetCard.coe_disjUnion, Finset.disjUnion_eq_union, Set.powersetCard.val_ofCard,
    Set.powersetCard.val_ofCard, ← Finset.insert_eq] at h
  refine ⟨((Equiv.Perm.sign (Set.powersetCard.permOfDisjoint hd) : ℤ) : K), ?_, ?_⟩
  · rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  · rw [← bE_singleton]
    refine h.trans ?_
    rw [Units.smul_def, Int.cast_smul_eq_zsmul]
    rfl

/-- **Killing the bad words in a product of left-normed brackets of blocks** leaves a basis
vector up to sign. -/
theorem map_prodE : ∀ bs : List (List ℕ), bs.Nodup →
    (∀ B ∈ bs, B.Nodup ∧ B ≠ [] ∧ ∀ x ∈ B, B.headI ≤ x) →
    ∃ c : K, c * c = 1 ∧ ExteriorAlgebra.map (kill K) (prodE K bs) = c • bE K bs.toFinset
  | [], _, _ => ⟨1, one_mul 1, by
      rw [prodE, List.map_nil, List.prod_nil, map_one, List.toFinset_nil, bE_empty, one_smul]⟩
  | B :: bs, hnd, h => by
    obtain ⟨h₁, h₂, h₃⟩ := h B (by simp)
    obtain ⟨c₁, hc₁, e₁⟩ := combE_eq (K := K) B h₂
    obtain ⟨c₂, hc₂, e₂⟩ := map_prodE bs (List.nodup_cons.1 hnd).2 fun C hC => h C (by simp [hC])
    obtain ⟨c₃, hc₃, e₃⟩ := ι_mul_bE (K := K) B bs.toFinset
      (by simpa using (List.nodup_cons.1 hnd).1)
    refine ⟨c₁ * c₂ * c₃, ?_, ?_⟩
    · rw [show c₁ * c₂ * c₃ * (c₁ * c₂ * c₃) = (c₁ * c₁) * (c₂ * c₂) * (c₃ * c₃) by ring, hc₁,
        hc₂, hc₃, one_mul, one_mul]
    · rw [prodE, List.map_cons, List.prod_cons, map_mul, ← prodE, e₂, e₁, map_smul,
        ExteriorAlgebra.map_apply_ι, kill_lc B h₁ h₂ h₃, smul_mul_smul_comm, e₃, smul_smul,
        List.toFinset_cons]

/-- **The products of the left-normed brackets of the blocks are independent.** -/
theorem linearIndependent_leadE (n : ℕ) : LinearIndependent K (leadE K n) := by
  refine LinearIndependent.of_comp (ExteriorAlgebra.map (kill K)).toLinearMap ?_
  have hcut : ∀ l : (List.range n).permutations.toFinset, (cut l.1).Nodup := fun l =>
    (pairwise_cut l.1 (nodup_of_mem l)).1.imp fun h e => by
      subst e
      exact lt_irrefl _ h
  choose c hc hm using fun l : (List.range n).permutations.toFinset =>
    map_prodE (K := K) (cut l.1) (hcut l) (block_props (nodup_of_mem l))
  have hinj : Function.Injective
      fun l : (List.range n).permutations.toFinset => (cut l.1).toFinset := by
    intro l l' h
    refine Subtype.ext (cut_injective (nodup_of_mem l) (nodup_of_mem l') ?_)
    refine Multiset.coe_eq_coe.2 ((List.perm_ext_iff_of_nodup (hcut l) (hcut l')).2 fun B => ?_)
    rw [← List.mem_toFinset, ← List.mem_toFinset]
    exact Iff.of_eq (congrArg (B ∈ ·) h)
  have hli := ((bE K).linearIndependent.comp _ hinj).units_smul
    fun l => (IsUnit.of_mul_eq_one _ (hc l)).unit
  convert hli using 1
  funext l
  rw [Pi.smul_apply', Units.smul_def, IsUnit.unit_spec, Function.comp_apply,
    Function.comp_apply, AlgHom.toLinearMap_apply]
  exact hm l

end Basis

/-! ## The dimension -/

variable (K : Type u) [Field K]

/-- **The Gerstenhaber operad has at least `n!` operations of arity `n`.** -/
theorem factorial_le_finrank {n : ℕ} (hn : 0 < n) [Module.Finite K (GerOp K ↥(Finset.range n))] :
    n.factorial ≤ Module.finrank K (GerOp K ↥(Finset.range n)) := by
  choose q hq using fun l => Tsp_le (K := K) _ (leadE_mem_Tsp (K := K) hn l)
  have li : LinearIndependent K q :=
    LinearIndependent.of_comp (ev K _) (by
      convert linearIndependent_leadE (K := K) n using 1
      funext l
      exact hq l)
  rw [← PoisDim.card_perms n]
  exact li.fintype_card_le_finrank

/-- **The Gerstenhaber operad has exactly `n!` operations of arity `n`.** -/
theorem finrank_ger {n : ℕ} (hn : 0 < n) :
    Module.finrank K (GerOp K ↥(Finset.range n)) = n.factorial := by
  obtain ⟨hfin, hle⟩ := finite_finrank_le K n
  exact le_antisymm hle (factorial_le_finrank K hn)

/-- **Relabelling the inputs**, a linear equivalence. -/
noncomputable def mapEquiv {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) : GerOp K A ≃ₗ[K] GerOp K B :=
  LinearEquiv.ofLinear (GrOperad.map (R := K) e) (GrOperad.map (R := K) e.symm)
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, ← GrOperad.map_trans, Equiv.symm_trans_self, GrOperad.map_refl]
      rfl)
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, ← GrOperad.map_trans, Equiv.self_trans_symm, GrOperad.map_refl]
      rfl)

/-- **The Gerstenhaber operad has exactly `n!` operations on `n` inputs**, on any nonempty finite
set of inputs. -/
theorem finrank_ger_eq (A : Type) [Fintype A] [DecidableEq A] [Nonempty A] :
    Module.finrank K (GerOp K A) = (Fintype.card A).factorial := by
  let e : A ≃ Finset.range (Fintype.card A) := Fintype.equivOfCardEq (by simp)
  rw [(mapEquiv K e).finrank_eq, finrank_ger K Fintype.card_pos]

end GerDim

end Operad
