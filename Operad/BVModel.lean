/-
# The BV operad has `2ⁿ n!` operations of arity `n`

The model is the exterior algebra of `g × hⁿ`, a BV algebra under the Chevalley–Eilenberg operator
(`Operad.ExtBV.isBV`), with `g` the noncommutative polynomials in the letters and `h` the Heisenberg
algebra of `3 × 3` matrices spanned by `p, q` and `w = [p, q]`, one block per input (`BVDim.Lw`,
`BVDim.bL`). The input of the letter `a` is `p_a q_a a`, and the operator turns it into `-w_a a`
(`BVDim.Δ_yIn`): the markers `p_a q_a` or `w_a` record whether the operator acted.

* **The deviation of marked vectors** (`ExtBV.dv_marked`): the markers commute with everything
  else, so `⟨M u, M' u'⟩ = ± M M' [u, u']`. Hence a left-normed bracket of inputs, some acted on
  by the operator, is up to sign the product of their markers times the vector of the left-normed
  commutator of the word (`BVDim.combZ_marked`), and similarly for products of such brackets over
  the blocks of a permutation (`BVDim.prodZ_marked`).
* **They are values** of operations of `BV` (`BVDim.leadZ_mem_Tsp`), by the closure of the values
  under the product, the bracket and the operator (`Operad.AlgVal`).
* **They are independent** (`BVDim.linearIndependent_leadZ`): killing the bad words leaves, up to
  sign, products of distinct basis vectors, basis vectors of the exterior algebra
  (`BVDim.vprod_basis`) recording the permutation and the inputs acted on (`BVDim.js_injective`).

With the upper bound (`Operad.BVGer.finite_finrank_le`): **`dim BV(n) = 2ⁿ n!`**
(`BVGer.finrank_bv`, `BVGer.finrank_bv_eq`), over any field.
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.Algebra.Lie.Prod
import Mathlib.Logic.Encodable.Basic
import Operad.AlgValues
import Operad.BVDim

universe u

namespace Operad

namespace ExtBV

open ExteriorAlgebra
open CliffordAlgebra (evenOdd involute involute_ι)

variable {R : Type u} [CommRing R] {L : Type u} [LieRing L] [LieAlgebra R L]

/-- The exterior algebra. -/
local notation "E" => ExteriorAlgebra R L

/-- The quadratic form of the exterior algebra. -/
local notation "Q₀" => (0 : QuadraticForm R L)

/-- The product of the vectors of a list. -/
noncomputable def vprod (vs : List L) : E := (vs.map (ι R)).prod

lemma vprod_nil : vprod (R := R) ([] : List L) = 1 := rfl

lemma vprod_cons (v : L) (vs : List L) : vprod (R := R) (v :: vs) = ι R v * vprod vs := rfl

lemma vprod_append (vs ws : List L) : vprod (R := R) (vs ++ ws) = vprod vs * vprod ws := by
  rw [vprod, List.map_append, List.prod_append]
  rfl

/-- **The derivation `D_v` kills a product of vectors commuting with `v`.** -/
lemma Dm_vprod (v : L) : ∀ (ws : List L), (∀ w ∈ ws, ⁅v, w⁆ = 0) →
    Dm R L v (vprod ws) = 0
  | [], _ => Dm_one v
  | w :: ws, h => by
    rw [vprod_cons, Dm_ι_mul, h w (List.mem_cons_self), map_zero, zero_mul, zero_add,
      Dm_vprod v ws fun w' hw' => h w' (List.mem_cons_of_mem _ hw'), mul_zero]

/-- **The deviation of a product of vectors** whose derivations kill `Y`. -/
lemma dv_vprod_mul : ∀ (vs : List L) (Z Y : E), (∀ v ∈ vs, Dm R L v Y = 0) →
    dv R L (vprod vs * Z) Y = (-1 : R) ^ vs.length • (vprod vs * dv R L Z Y)
  | [], Z, Y, _ => by rw [vprod_nil, one_mul, one_mul, List.length_nil, pow_zero, one_smul]
  | v :: vs, Z, Y, h => by
    rw [vprod_cons, mul_assoc, dv_ι_mul, h v (List.mem_cons_self), mul_zero, neg_zero, zero_sub,
      dv_vprod_mul vs Z Y fun w hw => h w (List.mem_cons_of_mem _ hw), mul_smul_comm,
      List.length_cons, pow_succ, mul_comm, ← smul_smul, neg_one_smul, mul_assoc]

/-- **The deviation of two marked vectors**: `⟨M u, M' u'⟩ = ± M M' [u, u']` when the markers
commute with everything else. -/
lemma dv_marked (vs vs' : List L) (u u' : L) (h₁ : ∀ v ∈ vs, ⁅v, u'⁆ = 0 ∧ ∀ v' ∈ vs', ⁅v, v'⁆ = 0)
    (h₂ : ∀ v' ∈ vs', ⁅u, v'⁆ = 0) :
    dv R L (vprod vs * ι R u) (vprod vs' * ι R u')
      = (-1 : R) ^ (vs.length + 1) • (vprod (vs ++ vs') * ι R ⁅u, u'⁆) := by
  rw [dv_vprod_mul vs _ _ fun v hv => ?_, dv_ι, Dm_mul, Dm_vprod u vs' h₂, zero_mul, zero_add,
    Dm_ι, vprod_append, pow_succ, ← smul_smul, neg_one_smul, mul_neg, smul_neg, ← neg_smul,
    mul_assoc]
  · rw [smul_neg, neg_smul]
  · rw [Dm_mul, Dm_vprod v vs' (h₁ v hv).2, zero_mul, zero_add, Dm_ι, (h₁ v hv).1, map_zero,
      mul_zero]

/-- **The grade involution of a product of vectors.** -/
lemma involute_vprod : ∀ vs : List L,
    involute (vprod (R := R) vs) = (-1 : R) ^ vs.length • vprod vs
  | [] => by rw [vprod_nil, map_one, List.length_nil, pow_zero, one_smul]
  | v :: vs => by
    rw [vprod_cons, map_mul, involute_ι, involute_vprod vs, List.length_cons, pow_succ,
      mul_comm, ← smul_smul, neg_one_smul, neg_mul, mul_smul_comm]

/-- **Moving a vector past a product of vectors.** -/
lemma ι_mul_vprod (u : L) (vs : List L) :
    ι R u * vprod vs = (-1 : R) ^ vs.length • (vprod vs * ι R u) := by
  rw [ι_mul_comm, involute_vprod, smul_mul_assoc]

/-- **A product of marked vectors**: `(M u) (M' Y) = ± (M M') (u Y)`. -/
lemma marked_mul (vs vs' : List L) (u : L) (Y : E) :
    vprod (R := R) vs * ι R u * (vprod vs' * Y)
      = (-1 : R) ^ vs'.length • (vprod (vs ++ vs') * (ι R u * Y)) := by
  rw [mul_assoc, ← mul_assoc (ι R u), ι_mul_vprod, smul_mul_assoc, mul_smul_comm, vprod_append,
    mul_assoc, mul_assoc]

end ExtBV

namespace BVDim

open ExteriorAlgebra ExtBV GerDim PoisDim
open CliffordAlgebra (evenOdd)

/-! ## The model: noncommutative polynomials and Heisenberg markers -/

section Model

variable (K : Type u) [Field K] (n : ℕ)

/-- The markers: a Heisenberg algebra in each block, inside `3 × 3` matrices. -/
abbrev Hn := Fin n → Matrix (Fin 3) (Fin 3) K

/-- **The Lie algebra of the model**: noncommutative polynomials times the markers. -/
abbrev Lw := Gw K × Hn K n

/-- The indices of the basis of `Lw`: words and matrix units of the blocks. -/
abbrev Idx := List ℕ ⊕ (Fin n × Fin 3 × Fin 3)

noncomputable instance : LinearOrder (Idx n) :=
  LinearOrder.lift' Encodable.encode Encodable.encode_injective

/-- **The basis of `Lw`.** -/
noncomputable def bL : Module.Basis (Idx n) K (Lw K n) :=
  ((bW K).prod (Pi.basis fun _ : Fin n => Matrix.stdBasis K (Fin 3) (Fin 3))).reindex
    (Equiv.sumCongr (Equiv.refl _) (Equiv.sigmaEquivProd _ _))

variable {K n}

lemma bL_inl (u : List ℕ) : bL K n (Sum.inl u) = (wd K u, 0) := by
  rw [bL, Module.Basis.reindex_apply]
  show ((bW K).prod (Pi.basis fun _ : Fin n => Matrix.stdBasis K (Fin 3) (Fin 3))) (Sum.inl u) = _
  simp [bW_apply]

lemma bL_inr (a : Fin n) (i j : Fin 3) :
    bL K n (Sum.inr (a, i, j)) = (0, Pi.single a (Matrix.single i j 1)) := by
  rw [bL, Module.Basis.reindex_apply]
  show ((bW K).prod (Pi.basis fun _ : Fin n => Matrix.stdBasis K (Fin 3) (Fin 3)))
    (Sum.inr ⟨a, (i, j)⟩) = _
  simp [Pi.basis_apply, Matrix.stdBasis_eq_single]

/-- The vector of a polynomial. -/
abbrev eG (x : Gw K) : Lw K n := (x, 0)

lemma lie_eG (x y : Gw K) : ⁅eG (n := n) x, eG (n := n) y⁆ = eG (n := n) ⁅x, y⁆ :=
  Prod.ext rfl (show ⁅(0 : Hn K n), 0⁆ = 0 from lie_self _)

lemma lie_eG_inr (x : Gw K) (a : Fin n) (i j : Fin 3) :
    ⁅eG (n := n) x, bL K n (Sum.inr (a, i, j))⁆ = 0 := by
  rw [bL_inr]
  exact Prod.ext (show ⁅x, (0 : Gw K)⁆ = 0 from lie_zero _)
    (show ⁅(0 : Hn K n), _⁆ = 0 from zero_lie _)

lemma lie_inr_eG (x : Gw K) (a : Fin n) (i j : Fin 3) :
    ⁅bL K n (Sum.inr (a, i, j)), eG (n := n) x⁆ = 0 := by
  rw [← lie_skew, lie_eG_inr, neg_zero]

lemma lie_inr_ne {a b : Fin n} (hab : a ≠ b) (i j k l : Fin 3) :
    ⁅bL K n (Sum.inr (a, i, j)), bL K n (Sum.inr (b, k, l))⁆ = 0 := by
  rw [bL_inr, bL_inr]
  refine Prod.ext (show ⁅(0 : Gw K), 0⁆ = 0 from lie_self _) ?_
  show ⁅(Pi.single a (Matrix.single i j (1 : K)) : Hn K n),
    (Pi.single b (Matrix.single k l (1 : K)) : Hn K n)⁆ = 0
  rw [Ring.lie_def]
  funext c
  by_cases hc : c = a
  · subst hc
    simp [Ne.symm hab]
  · simp [hc]

lemma lie_pq (a : Fin n) :
    ⁅bL K n (Sum.inr (a, 0, 1)), bL K n (Sum.inr (a, 1, 2))⁆ = bL K n (Sum.inr (a, 0, 2)) := by
  rw [bL_inr, bL_inr, bL_inr]
  refine Prod.ext (show ⁅(0 : Gw K), 0⁆ = 0 from lie_self _) ?_
  show ⁅(Pi.single a (Matrix.single (0 : Fin 3) (1 : Fin 3) (1 : K)) : Hn K n),
    (Pi.single a (Matrix.single (1 : Fin 3) (2 : Fin 3) (1 : K)) : Hn K n)⁆
      = (Pi.single a (Matrix.single (0 : Fin 3) (2 : Fin 3) (1 : K)) : Hn K n)
  rw [Ring.lie_def]
  funext c
  by_cases hc : c = a
  · subst hc
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.single_eq_same]
    rw [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ (by decide),
      sub_zero, one_mul]
  · simp [hc]

end Model

/-! ## The BV algebra and its inputs -/

section Inputs

variable (K : Type u) [Field K] (n : ℕ)

/-- The exterior algebra of the model. -/
abbrev Ew := ExteriorAlgebra K (Lw K n)

/-- **The algebra over `BV`.** -/
noncomputable abbrev φB : GrAlgebra K (Ew K n) (BVOp K) := bvAlg K (Lw K n)

/-- The markers of the input `a`: `p_a, q_a`, or `w_a = [p_a, q_a]` when the operator acts. -/
def mv (ε : Fin n → Bool) (a : Fin n) : List (Idx n) :=
  if ε a then [Sum.inr (a, 0, 2)] else [Sum.inr (a, 0, 1), Sum.inr (a, 1, 2)]

/-- The markers of the letters of a word. -/
def mvs (ε : Fin n → Bool) (w : List ℕ) : List (Idx n) :=
  w.flatMap fun a => if h : a < n then mv n ε ⟨a, h⟩ else []

/-- **The input of a letter**: `p_a q_a a`, odd. -/
noncomputable def yIn (a : ℕ) : Ew K n :=
  vprod ((mvs n (fun _ => false) [a]).map (bL K n)) * ι K (eG (n := n) (wd K [a]))

/-- **The input or its image under the operator.** -/
noncomputable def zIn (ε : Fin n → Bool) (a : ℕ) : Ew K n :=
  if h : a < n then (if ε ⟨a, h⟩ then Δ K (Lw K n) (yIn K n a) else yIn K n a) else yIn K n a

variable {K n}

lemma vprod_mem : ∀ vs : List (Lw K n), vprod (R := K) vs ∈ evenOdd (0 : QuadraticForm K (Lw K n))
    (vs.length : ZMod 2)
  | [] => by
    rw [vprod_nil, List.length_nil, Nat.cast_zero, ← map_one (algebraMap K (Ew K n))]
    exact algebraMap_mem 1
  | v :: vs => by
    rw [vprod_cons, List.length_cons, Nat.cast_succ]
    exact mul_mem' (by ring) (ι_mem v) (vprod_mem vs)

lemma yIn_odd (a : ℕ) : SuperMod.pr (R := K) true (yIn K n a) = yIn K n a := by
  refine (isP_iff true _).2 (mul_mem' ?_ (vprod_mem _) (ι_mem _))
  simp only [mvs, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  split_ifs <;> simp [mv, bz]; decide

lemma mvs_append (ε : Fin n → Bool) (w w' : List ℕ) :
    mvs n ε (w ++ w') = mvs n ε w ++ mvs n ε w' := List.flatMap_append

lemma mem_mvs {ε : Fin n → Bool} {w : List ℕ} {x : Idx n} (hx : x ∈ mvs n ε w) :
    ∃ (a : Fin n) (i j : Fin 3), a.1 ∈ w ∧ x = Sum.inr (a, i, j) := by
  obtain ⟨a, ha, hx⟩ := List.mem_flatMap.1 hx
  split_ifs at hx with h
  · refine ⟨⟨a, h⟩, ?_⟩
    unfold mv at hx
    split_ifs at hx
    · exact ⟨0, 2, ha, List.mem_singleton.1 hx⟩
    · rcases List.mem_pair.1 hx with rfl | rfl
      · exact ⟨0, 1, ha, rfl⟩
      · exact ⟨1, 2, ha, rfl⟩
  · simp at hx

lemma lie_mvs_eG {ε : Fin n → Bool} {w : List ℕ} {v : Lw K n}
    (hv : v ∈ (mvs n ε w).map (bL K n)) (x : Gw K) : ⁅v, eG (n := n) x⁆ = 0 := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hv
  obtain ⟨a, i, j, -, rfl⟩ := mem_mvs hy
  exact lie_inr_eG x a i j

lemma lie_eG_mvs {ε : Fin n → Bool} {w : List ℕ} {v : Lw K n}
    (hv : v ∈ (mvs n ε w).map (bL K n)) (x : Gw K) : ⁅eG (n := n) x, v⁆ = 0 := by
  rw [← lie_skew, lie_mvs_eG hv, neg_zero]

lemma lie_mvs_mvs {ε : Fin n → Bool} {w w' : List ℕ} (hd : ∀ a ∈ w, a ∉ w') {v v' : Lw K n}
    (hv : v ∈ (mvs n ε w).map (bL K n)) (hv' : v' ∈ (mvs n ε w').map (bL K n)) : ⁅v, v'⁆ = 0 := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hv
  obtain ⟨a, i, j, ha, rfl⟩ := mem_mvs hy
  obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hv'
  obtain ⟨b, k, l, hb, rfl⟩ := mem_mvs hy'
  exact lie_inr_ne (fun e => hd a ha (by rw [e]; exact hb)) i j k l

/-- **The operator on an input**: `Δ (p q a) = -w a`. -/
lemma Δ_yIn {a : ℕ} (h : a < n) :
    Δ K (Lw K n) (yIn K n a)
      = -(vprod ((mv n (fun _ => true) ⟨a, h⟩).map (bL K n)) * ι K (eG (n := n) (wd K [a]))) := by
  simp only [yIn, mvs, List.flatMap_cons, List.flatMap_nil, List.append_nil, dif_pos h, mv,
    Bool.false_eq_true, if_false, if_true, List.map_cons, List.map_nil, vprod_cons, vprod_nil,
    mul_one, mul_assoc]
  rw [Δ_ι_mul, Δ_ι_mul, Δ_ι, mul_zero, sub_zero, Dm_ι, Dm_ι_mul, Dm_ι, lie_pq,
    lie_inr_eG, map_zero, mul_zero, add_zero, lie_inr_eG, map_zero, neg_zero]
  simp

end Inputs

/-! ## Left-normed brackets of the inputs, marked -/

section Marked

variable {K : Type u} [Field K] {n : ℕ}

variable (K n) in
/-- **The left-normed bracket of the inputs** of a word. -/
noncomputable def combZ (ε : Fin n → Bool) : List ℕ → Ew K n
  | [] => 0
  | a :: rest => rest.foldl (fun p c => dv K (Lw K n) p (zIn K n ε c)) (zIn K n ε a)

variable (K n) in
/-- **The product of the left-normed brackets** of blocks. -/
noncomputable def prodZ (ε : Fin n → Bool) (bs : List (List ℕ)) : Ew K n :=
  (bs.map (combZ K n ε)).prod

lemma combZ_single (ε : Fin n → Bool) (a : ℕ) : combZ K n ε [a] = zIn K n ε a := rfl

lemma combZ_append_single (ε : Fin n → Bool) {w : List ℕ} (hw : w ≠ []) (c : ℕ) :
    combZ K n ε (w ++ [c]) = dv K (Lw K n) (combZ K n ε w) (zIn K n ε c) := by
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hw
  simp only [List.cons_append, combZ, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma mvs_single (ε : Fin n → Bool) {a : ℕ} (h : a < n) : mvs n ε [a] = mv n ε ⟨a, h⟩ := by
  simp [mvs, h]

lemma sign_sq {s₁ s₂ : K} (hs₁ : s₁ * s₁ = 1) (hs₂ : s₂ * s₂ = 1) (k : ℕ) :
    s₁ * s₂ * (-1) ^ k * (s₁ * s₂ * (-1) ^ k) = 1 := by
  calc _ = (s₁ * s₁) * (s₂ * s₂) * ((-1) ^ k * (-1) ^ k) := by ring
    _ = 1 := by rw [hs₁, hs₂, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul, one_mul]

/-- **An input, marked.** -/
lemma zIn_marked (ε : Fin n → Bool) {a : ℕ} (h : a < n) :
    ∃ s : K, s * s = 1 ∧ zIn K n ε a
      = s • (vprod ((mvs n ε [a]).map (bL K n)) * ι K (eG (n := n) (wd K [a]))) := by
  rw [mvs_single ε h, zIn, dif_pos h]
  by_cases he : ε ⟨a, h⟩
  · refine ⟨-1, by ring, ?_⟩
    rw [if_pos he, Δ_yIn h, neg_one_smul]
    congr 4
    simp [mv, he]
  · refine ⟨1, by ring, ?_⟩
    rw [if_neg he, one_smul, yIn, mvs_single _ h]
    congr 3
    simp [mv, he]

/-- **A left-normed bracket of inputs, marked**: the markers of its letters times the vector of
the left-normed commutator. -/
theorem combZ_marked (ε : Fin n → Bool) : ∀ (w : List ℕ), w.Nodup → w ≠ [] → (∀ a ∈ w, a < n) →
    ∃ s : K, s * s = 1 ∧ combZ K n ε w
      = s • (vprod ((mvs n ε w).map (bL K n)) * ι K (eG (n := n) (lc K w))) := by
  intro w
  induction w using List.reverseRecOn with
  | nil => intro _ h; exact absurd rfl h
  | append_singleton w c ih =>
    intro hnd _ hlt
    have hc : c < n := hlt c (by simp)
    by_cases hw : w = []
    · subst hw
      exact zIn_marked ε hc
    · have hcw : c ∉ w := by
        have := (List.nodup_append.1 hnd).2.2
        exact fun h => this c h c (List.mem_singleton_self c) rfl
      obtain ⟨s₁, hs₁, h₁⟩ := ih (List.nodup_append.1 hnd).1 hw fun a ha => hlt a (by simp [ha])
      obtain ⟨s₂, hs₂, h₂⟩ := zIn_marked (K := K) ε hc
      refine ⟨s₁ * s₂ * (-1) ^ ((mvs n ε w).map (bL K n)).length.succ, ?_, ?_⟩
      · exact sign_sq hs₁ hs₂ _
      · rw [combZ_append_single ε hw, h₁, h₂, LinearMap.map_smul₂, map_smul,
          dv_marked _ _ _ _ (fun v hv => ⟨lie_mvs_eG hv _, fun v' hv' => lie_mvs_mvs
            (fun a ha h' => hcw (by rw [← List.mem_singleton.1 h']; exact ha)) hv hv'⟩)
            (fun v' hv' => lie_eG_mvs hv' _), lie_eG, ← lc_append_single hw, smul_smul,
          smul_smul, ← List.map_append, ← mvs_append]

/-- **A product of left-normed brackets of inputs, marked.** -/
theorem prodZ_marked (ε : Fin n → Bool) : ∀ bs : List (List ℕ),
    (∀ B ∈ bs, B.Nodup ∧ B ≠ [] ∧ ∀ a ∈ B, a < n) →
    ∃ s : K, s * s = 1 ∧ prodZ K n ε bs = s • (vprod ((bs.flatMap (mvs n ε)).map (bL K n))
      * (bs.map fun B => ι K (eG (n := n) (lc K B))).prod)
  | [], _ => ⟨1, one_mul 1, by simp [prodZ, vprod_nil]⟩
  | B :: bs, h => by
    obtain ⟨h₁, h₂, h₃⟩ := h B (by simp)
    obtain ⟨s₁, hs₁, e₁⟩ := combZ_marked (K := K) ε B h₁ h₂ h₃
    obtain ⟨s₂, hs₂, e₂⟩ := prodZ_marked ε bs fun C hC => h C (by simp [hC])
    refine ⟨s₁ * s₂ * (-1) ^ ((bs.flatMap (mvs n ε)).map (bL K n)).length, ?_, ?_⟩
    · exact sign_sq hs₁ hs₂ _
    · rw [prodZ, List.map_cons, List.prod_cons, ← prodZ, e₁, e₂, smul_mul_smul_comm, marked_mul,
        smul_smul, List.flatMap_cons, List.map_append, List.map_cons, List.prod_cons]

end Marked

/-! ## The marked brackets are values -/

section Values

variable {K : Type u} [Field K] {n : ℕ}

lemma sv_φB_bB :
    EndGr.sv ((φB K n).app _ (BVGer.bB K)) = dvOp K (Lw K n) := by
  rw [BV.app_devOf]
  refine GrEnd.ext_hom fun c v hv => ?_
  rw [EndGr.vec_two v, BV.sv_devOf _ _ (by rw [sv_bvAlg_mul]; exact isBV.par_m)
    (by rw [sv_bvAlg_op]; exact isBV.par_d) (hv 0) (hv 1), sv_bvAlg_mul, sv_bvAlg_op,
    BV_dv_eq ((isP_iff _ _).1 (hv 0))]
  rfl

lemma zIn_mem_Tsp (ε : Fin n → Bool) (a : ℕ) :
    zIn K n ε a ∈ AlgVal.Tsp (φB K n) (yIn K n) {a} := by
  unfold zIn
  split_ifs
  · exact AlgVal.unary_mem_Tsp (FreeGr.par_presGen (gp := bvPar) BVGen.op) (Δ K (Lw K n))
      (fun x => by rw [sv_bvAlg_op]; rfl) a
  all_goals exact AlgVal.input_mem_Tsp a

lemma dv_mem_Tsp {s t : Finset ℕ} (h : Disjoint s t) {y z : Ew K n}
    (hy : y ∈ AlgVal.Tsp (φB K n) (yIn K n) s) (hz : z ∈ AlgVal.Tsp (φB K n) (yIn K n) t) :
    dv K (Lw K n) y z ∈ AlgVal.Tsp (φB K n) (yIn K n) (s ∪ t) :=
  AlgVal.binop_mem_Tsp (fun a => yIn_odd a) (BVGer.par_bB K) (dv K (Lw K n))
    (fun y z => by rw [sv_φB_bB]; rfl) h hy hz

lemma mul_mem_Tsp {s t : Finset ℕ} (h : Disjoint s t) {y z : Ew K n}
    (hy : y ∈ AlgVal.Tsp (φB K n) (yIn K n) s) (hz : z ∈ AlgVal.Tsp (φB K n) (yIn K n) t) :
    y * z ∈ AlgVal.Tsp (φB K n) (yIn K n) (s ∪ t) :=
  AlgVal.binop_mem_Tsp (fun a => yIn_odd a) (BVGer.par_mB K) (LinearMap.mul K (Ew K n))
    (fun y z => by rw [sv_bvAlg_mul]; rfl) h hy hz

theorem combZ_mem_Tsp (ε : Fin n → Bool) : ∀ (w : List ℕ), w.Nodup → w ≠ [] →
    combZ K n ε w ∈ AlgVal.Tsp (φB K n) (yIn K n) w.toFinset := by
  intro w
  induction w using List.reverseRecOn with
  | nil => intro _ h; exact absurd rfl h
  | append_singleton w c ih =>
    intro hnd _
    by_cases hw : w = []
    · subst hw
      simpa [combZ_single] using zIn_mem_Tsp (K := K) ε c
    · have hc : c ∉ w := by
        have := (List.nodup_append.1 hnd).2.2
        exact fun h => this c h c (List.mem_singleton_self c) rfl
      rw [combZ_append_single ε hw, List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
        insert_empty_eq]
      exact dv_mem_Tsp (Finset.disjoint_singleton_right.2 (by simpa using hc))
        (ih (List.nodup_append.1 hnd).1 hw) (zIn_mem_Tsp ε c)

theorem prodZ_mem_Tsp (ε : Fin n → Bool) : ∀ (bs : List (List ℕ)), bs ≠ [] → bs.flatten.Nodup →
    (∀ B ∈ bs, B ≠ []) → prodZ K n ε bs ∈ AlgVal.Tsp (φB K n) (yIn K n) bs.flatten.toFinset
  | [], h, _, _ => absurd rfl h
  | [B], _, hnd, hne => by
    simpa [prodZ] using combZ_mem_Tsp ε B (by simpa using hnd) (hne B (List.mem_singleton_self B))
  | B :: B' :: bs, _, hnd, hne => by
    rw [prodZ, List.map_cons, List.prod_cons, List.flatten_cons, List.toFinset_append]
    have h1 := List.nodup_append.1 (List.flatten_cons ▸ hnd)
    refine mul_mem_Tsp ?_ (combZ_mem_Tsp ε B h1.1 (hne B (by simp)))
      (prodZ_mem_Tsp ε (B' :: bs) (by simp) h1.2.1 fun C hC => hne C (by simp [hC]))
    rw [List.disjoint_toFinset_iff_disjoint]
    exact fun a ha hb => h1.2.2 a ha a hb rfl

end Values

/-! ## Products of basis vectors -/

section BasisProd

variable {K : Type u} [Field K] {M : Type u} [AddCommGroup M] [Module K M] {I : Type}
  [LinearOrder I] (b : Module.Basis I K M)

lemma basisE_empty : b.ExteriorAlgebra ∅ = 1 := by
  rw [ExteriorAlgebra.basis_apply_ofCard b (n := 0) Finset.card_empty]
  simp [ExteriorAlgebra.ιMulti_apply]

lemma basisE_singleton (j : I) : b.ExteriorAlgebra {j} = ExteriorAlgebra.ι K (b j) := by
  rw [ExteriorAlgebra.basis_apply_ofCard b (n := 1) (Finset.card_singleton j)]
  simp only [ExteriorAlgebra.ιMulti_apply, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
    List.prod_nil, mul_one, Function.comp_apply]
  have h := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
    (Set.powersetCard.ofCard (Finset.card_singleton j)) _).1 ⟨0, rfl⟩
  rw [← Set.powersetCard.mem_coe_iff, Set.powersetCard.val_ofCard, Finset.mem_singleton] at h
  rw [h]

lemma ι_mul_basisE (j : I) (T : Finset I) (hj : j ∉ T) :
    ∃ c : K, c * c = 1 ∧
      ExteriorAlgebra.ι K (b j) * b.ExteriorAlgebra T = c • b.ExteriorAlgebra (insert j T) := by
  have hd : Disjoint (Set.powersetCard.ofCard (Finset.card_singleton j)).val
      (Set.powersetCard.ofCard (rfl : T.card = T.card)).val := by
    simpa using hj
  have h := ExteriorAlgebra.basis_mul_of_disjoint b _ _ hd
  rw [Set.powersetCard.coe_disjUnion, Finset.disjUnion_eq_union, Set.powersetCard.val_ofCard,
    Set.powersetCard.val_ofCard, ← Finset.insert_eq] at h
  refine ⟨((Equiv.Perm.sign (Set.powersetCard.permOfDisjoint hd) : ℤ) : K), ?_, ?_⟩
  · rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  · rw [← basisE_singleton]
    refine h.trans ?_
    rw [Units.smul_def, Int.cast_smul_eq_zsmul]

/-- **A product of distinct basis vectors** is a basis vector of the exterior algebra, up to
sign. -/
lemma vprod_basis : ∀ js : List I, js.Nodup →
    ∃ c : K, c * c = 1 ∧ (js.map fun j => ExteriorAlgebra.ι K (b j)).prod
      = c • b.ExteriorAlgebra js.toFinset
  | [], _ => ⟨1, one_mul 1, by rw [List.map_nil, List.prod_nil, List.toFinset_nil, basisE_empty,
      one_smul]⟩
  | j :: js, h => by
    obtain ⟨c₁, hc₁, e₁⟩ := vprod_basis js (List.nodup_cons.1 h).2
    obtain ⟨c₂, hc₂, e₂⟩ := ι_mul_basisE b j js.toFinset (by simpa using (List.nodup_cons.1 h).1)
    refine ⟨c₁ * c₂, by rw [show c₁ * c₂ * (c₁ * c₂) = (c₁ * c₁) * (c₂ * c₂) by ring, hc₁, hc₂,
      one_mul], ?_⟩
    rw [List.map_cons, List.prod_cons, e₁, mul_smul_comm, e₂, smul_smul, List.toFinset_cons]

end BasisProd

/-! ## Independence -/

section Independence

variable {K : Type u} [Field K] {n : ℕ}

variable (K n) in
/-- **Killing the bad words**, on the model. -/
noncomputable def F : Ew K n →ₐ[K] Ew K n :=
  ExteriorAlgebra.map (LinearMap.prodMap (kill K) LinearMap.id)

lemma F_vprod (vs : List (Lw K n)) :
    F K n (vprod vs) = vprod (vs.map (LinearMap.prodMap (kill K) LinearMap.id)) := by
  rw [vprod, map_list_prod, List.map_map, vprod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun v _ => ExteriorAlgebra.map_apply_ι _ v)

lemma prodMap_inr (x : Fin n × Fin 3 × Fin 3) :
    LinearMap.prodMap (kill K) LinearMap.id (bL K n (Sum.inr x)) = bL K n (Sum.inr x) := by
  obtain ⟨a, i, j⟩ := x
  rw [bL_inr]
  simp

lemma F_markers (ms : List (Idx n)) (hms : ∀ x ∈ ms, ∃ y, x = Sum.inr y) :
    (ms.map (bL K n)).map (LinearMap.prodMap (kill K) LinearMap.id) = ms.map (bL K n) := by
  rw [List.map_map]
  refine List.map_congr_left fun x hx => ?_
  obtain ⟨y, rfl⟩ := hms x hx
  exact prodMap_inr y

lemma F_blocks : ∀ bs : List (List ℕ), (∀ B ∈ bs, B.Nodup ∧ B ≠ [] ∧ ∀ x ∈ B, B.headI ≤ x) →
    F K n (bs.map fun B => ι K (eG (n := n) (lc K B))).prod
      = vprod ((bs.map Sum.inl).map (bL K n))
  | [], _ => by simp; rfl
  | B :: bs, h => by
    obtain ⟨h₁, h₂, h₃⟩ := h B (by simp)
    rw [List.map_cons, List.prod_cons, map_mul, F_blocks bs fun C hC => h C (by simp [hC])]
    simp only [List.map_cons, vprod_cons]
    rw [F, ExteriorAlgebra.map_apply_ι, bL_inl]
    congr 2
    exact Prod.ext (kill_lc B h₁ h₂ h₃) rfl

/-- The indices of a marked product of left-normed brackets. -/
def js (bs : List (List ℕ)) (ε : Fin n → Bool) : List (Idx n) :=
  bs.flatMap (mvs n ε) ++ bs.map (Sum.inl : List ℕ → Idx n)

lemma flatMap_mvs (ε : Fin n → Bool) : ∀ bs : List (List ℕ),
    bs.flatMap (mvs n ε) = mvs n ε bs.flatten
  | [] => rfl
  | B :: bs => by rw [List.flatMap_cons, List.flatten_cons, mvs_append, flatMap_mvs ε bs]

lemma mvs_inr {ε : Fin n → Bool} {w : List ℕ} {x : Idx n} (hx : x ∈ mvs n ε w) :
    ∃ y, x = Sum.inr y := by
  obtain ⟨a, i, j, -, rfl⟩ := mem_mvs hx
  exact ⟨_, rfl⟩

lemma nodup_mvs (ε : Fin n → Bool) {w : List ℕ} (hw : w.Nodup) : (mvs n ε w).Nodup := by
  refine List.nodup_flatMap.2 ⟨fun a _ => ?_, hw.imp fun {a b} hab => ?_⟩
  · split_ifs
    · unfold mv
      split_ifs <;> simp [Prod.ext_iff]
    · exact List.nodup_nil
  · intro x hx hy
    obtain ⟨a', i, j, ha', rfl⟩ := mem_mvs (w := [a]) (ε := ε) (by simpa [mvs] using hx)
    obtain ⟨b', k, l, hb', h'⟩ := mem_mvs (w := [b]) (ε := ε) (by simpa [mvs] using hy)
    simp only [Sum.inr.injEq, Prod.mk.injEq] at h'
    simp only [List.mem_singleton] at ha' hb'
    exact hab (by rw [← ha', ← hb', h'.1])

lemma mem_mvs_w {ε : Fin n → Bool} {w : List ℕ} (a : Fin n) :
    (Sum.inr (a, 0, 2) : Idx n) ∈ mvs n ε w ↔ a.1 ∈ w ∧ ε a = true := by
  constructor
  · intro h
    obtain ⟨b, hb, hx⟩ := List.mem_flatMap.1 h
    split_ifs at hx with hbn
    · unfold mv at hx
      split_ifs at hx with he
      · simp only [List.mem_singleton, Sum.inr.injEq, Prod.mk.injEq] at hx
        obtain ⟨rfl, -⟩ := hx
        exact ⟨hb, he⟩
      · simp at hx
    · simp at hx
  · rintro ⟨ha, he⟩
    refine List.mem_flatMap.2 ⟨a.1, ha, ?_⟩
    rw [dif_pos a.2]
    simp [mv, he]

end Independence

/-! ## The lower bound -/

section Final

open PoisDim

variable (K : Type u) [Field K] (n : ℕ)

/-- The index set: a permutation and the inputs carrying the operator. -/
abbrev Ix := (List.range n).permutations.toFinset × (Fin n → Bool)

/-- **The products of the left-normed brackets of the blocks, with the operator at some inputs.** -/
noncomputable def leadZ (x : Ix n) : Ew K n := prodZ K n x.2 (cut x.1.1)

variable {K n}

lemma perm_of_mem (l : (List.range n).permutations.toFinset) : l.1.Perm (List.range n) :=
  List.mem_permutations.1 (List.mem_toFinset.1 l.2)

lemma lt_of_mem_cut (l : (List.range n).permutations.toFinset) {B : List ℕ} (hB : B ∈ cut l.1)
    {a : ℕ} (ha : a ∈ B) : a < n := by
  have h : a ∈ l.1 := by
    rw [← flatten_cut l.1]
    exact List.mem_flatten.2 ⟨B, hB, ha⟩
  simpa using (perm_of_mem l).subset h

lemma nodup_cut (l : (List.range n).permutations.toFinset) : (cut l.1).Nodup :=
  (pairwise_cut l.1 (nodup_of_mem l)).1.imp fun h e => by
    subst e
    exact lt_irrefl _ h

lemma js_nodup (x : Ix n) : (js (cut x.1.1) x.2).Nodup := by
  rw [js, List.nodup_append]
  refine ⟨?_, (nodup_cut x.1).map Sum.inl_injective, fun a ha b hb e => ?_⟩
  · rw [flatMap_mvs, flatten_cut]
    exact nodup_mvs _ (nodup_of_mem x.1)
  · obtain ⟨y, rfl⟩ := mvs_inr (by rwa [flatMap_mvs] at ha)
    obtain ⟨B, -, rfl⟩ := List.mem_map.1 hb
    exact Sum.inr_ne_inl e

lemma F_leadZ (x : Ix n) : ∃ c : K, c * c = 1 ∧
    F K n (leadZ K n x) = c • (bL K n).ExteriorAlgebra (js (cut x.1.1) x.2).toFinset := by
  have hB := block_props (nodup_of_mem x.1)
  obtain ⟨s, hs, e⟩ := prodZ_marked (K := K) x.2 (cut x.1.1) fun B hB' =>
    ⟨(hB B hB').1, (hB B hB').2.1, fun a ha => lt_of_mem_cut x.1 hB' ha⟩
  obtain ⟨c, hc, e'⟩ := vprod_basis (K := K) (bL K n) _ (js_nodup x)
  refine ⟨s * c, by rw [show s * c * (s * c) = (s * s) * (c * c) by ring, hs, hc, one_mul], ?_⟩
  rw [leadZ, e, map_smul, map_mul, F_vprod, F_markers _ fun y hy => mvs_inr (by
      rwa [flatMap_mvs] at hy), F_blocks _ hB, ← vprod_append, ← List.map_append, ← js, vprod,
    List.map_map, ← smul_smul]
  convert congrArg (s • ·) e' using 4
  congr 1
  exact Subsingleton.elim _ _

lemma js_injective : Function.Injective fun x : Ix n => (js (cut x.1.1) x.2).toFinset := by
  rintro ⟨l, ε⟩ ⟨l', ε'⟩ h
  simp only at h
  have hinl : ∀ (l : (List.range n).permutations.toFinset) (ε : Fin n → Bool) (B : List ℕ),
      (Sum.inl B : Idx n) ∈ (js (cut l.1) ε).toFinset ↔ B ∈ cut l.1 := by
    intro l ε B
    rw [List.mem_toFinset, js, List.mem_append]
    constructor
    · rintro (h | h)
      · obtain ⟨y, hy⟩ := mvs_inr (by rwa [flatMap_mvs] at h)
        exact absurd hy Sum.inl_ne_inr
      · obtain ⟨C, hC, e⟩ := List.mem_map.1 h
        exact Sum.inl_injective e ▸ hC
    · exact fun h => Or.inr (List.mem_map_of_mem h)
  have hinr : ∀ (l : (List.range n).permutations.toFinset) (ε : Fin n → Bool) (a : Fin n),
      (Sum.inr (a, 0, 2) : Idx n) ∈ (js (cut l.1) ε).toFinset ↔ ε a = true := by
    intro l ε a
    rw [List.mem_toFinset, js, List.mem_append, flatMap_mvs, flatten_cut, mem_mvs_w]
    constructor
    · rintro (h | h)
      · exact h.2
      · obtain ⟨C, -, e⟩ := List.mem_map.1 h
        exact absurd e Sum.inl_ne_inr
    · exact fun he => Or.inl ⟨(perm_of_mem l).symm.subset (by simp), he⟩
  have hl : l = l' := by
    refine Subtype.ext (cut_injective (nodup_of_mem l) (nodup_of_mem l') ?_)
    refine Multiset.coe_eq_coe.2 ((List.perm_ext_iff_of_nodup (nodup_cut l)
      (nodup_cut l')).2 fun B => ?_)
    rw [← hinl l ε, ← hinl l' ε', h]
  subst hl
  refine Prod.ext rfl (funext fun a => ?_)
  have := hinr l ε a
  rw [h, hinr l ε' a] at this
  exact Bool.eq_iff_iff.2 this.symm

/-- **The values are independent.** -/
theorem linearIndependent_leadZ : LinearIndependent K (leadZ K n) := by
  refine LinearIndependent.of_comp (F K n).toLinearMap ?_
  choose c hc hm using fun x : Ix n => F_leadZ (K := K) x
  have hli := (((bL K n).ExteriorAlgebra).linearIndependent.comp _ js_injective).units_smul
    fun x => (IsUnit.of_mul_eq_one _ (hc x)).unit
  convert hli using 1
  funext x
  rw [Pi.smul_apply', Units.smul_def, IsUnit.unit_spec, Function.comp_apply,
    Function.comp_apply, AlgHom.toLinearMap_apply]
  exact hm x

lemma leadZ_mem_Tsp (hn : 0 < n) (x : Ix n) :
    leadZ K n x ∈ AlgVal.Tsp (φB K n) (yIn K n) (Finset.range n) := by
  have hl := nodup_of_mem x.1
  have hp := perm_of_mem x.1
  have h := prodZ_mem_Tsp (K := K) (n := n) x.2 (cut x.1.1) (fun h => by
      have hlen := hp.length_eq
      rw [← flatten_cut x.1.1, h] at hlen
      simp at hlen
      omega)
    (by rw [flatten_cut]; exact hl) fun B hB => (mem_cut x.1.1 B hB).1
  rwa [flatten_cut, List.toFinset_eq_of_perm _ _ hp, List.toFinset_range] at h

lemma card_Ix : Fintype.card (Ix n) = n.factorial * 2 ^ n := by
  rw [Fintype.card_prod, card_perms, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

variable (K) in
/-- **The BV operad has at least `2ⁿ n!` operations of arity `n`.** -/
theorem le_finrank {n : ℕ} (hn : 0 < n) [Module.Finite K (BVOp K ↥(Finset.range n))] :
    2 ^ n * n.factorial ≤ Module.finrank K (BVOp K ↥(Finset.range n)) := by
  choose q hq using fun x : Ix n =>
    AlgVal.Tsp_le (fun a => yIn_odd a) _ (leadZ_mem_Tsp (K := K) hn x)
  have li : LinearIndependent K q :=
    LinearIndependent.of_comp (AlgVal.ev (φB K n) (yIn K n) _) (by
      convert linearIndependent_leadZ (K := K) (n := n) using 1
      funext x
      exact hq x)
  rw [mul_comm, ← card_Ix]
  exact li.fintype_card_le_finrank

end Final

end BVDim

namespace BVGer

variable (K : Type u) [Field K]

/-- **The BV operad has exactly `2ⁿ n!` operations of arity `n`.** -/
theorem finrank_bv {n : ℕ} (hn : 0 < n) :
    Module.finrank K (BVOp K ↥(Finset.range n)) = 2 ^ n * n.factorial := by
  haveI : Nonempty ↥(Finset.range n) := ⟨⟨0, Finset.mem_range.2 hn⟩⟩
  obtain ⟨hfin, hle⟩ := finite_finrank_le K ↥(Finset.range n)
  simp only [Fintype.card_coe, Finset.card_range] at hle
  exact le_antisymm hle (BVDim.le_finrank K hn)

/-- **Relabelling the inputs**, a linear equivalence. -/
noncomputable def mapEquiv {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) : BVOp K A ≃ₗ[K] BVOp K B :=
  LinearEquiv.ofLinear (GrOperad.map (R := K) e) (GrOperad.map (R := K) e.symm)
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, ← GrOperad.map_trans, Equiv.symm_trans_self, GrOperad.map_refl]
      rfl)
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, ← GrOperad.map_trans, Equiv.self_trans_symm, GrOperad.map_refl]
      rfl)

/-- **The BV operad has exactly `2ⁿ n!` operations on `n` inputs**, on any nonempty finite set of
inputs. -/
theorem finrank_bv_eq (A : Type) [Fintype A] [DecidableEq A] [Nonempty A] :
    Module.finrank K (BVOp K A) = 2 ^ Fintype.card A * (Fintype.card A).factorial := by
  let e : A ≃ Finset.range (Fintype.card A) := Fintype.equivOfCardEq (by simp)
  rw [(mapEquiv K e).finrank_eq, finrank_bv K Fintype.card_pos]

end BVGer

end Operad
