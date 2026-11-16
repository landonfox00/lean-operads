/-
# Symmetric braces in a pre-Lie algebra

For a bilinear product `m` on `L`, the braces are defined by `x{} = x` and
`x{y₁, …, y_k, z} = x{y₁, …, y_k} z - ∑ᵢ x{y₁, …, yᵢ z, …, y_k}` (`PreLieBrace.brace`,
`PreLieBrace.brace_snoc`). They are additive and homogeneous in each entry
(`PreLieBrace.brace_update_add`, `PreLieBrace.brace_update_sum`, `PreLieBrace.brace_update_smul`).

* **For a pre-Lie product the braces are symmetric** (`PreLieBrace.brace_comp_perm`): expanding
  the last two entries (`PreLieBrace.brace_snoc_snoc`), the pre-Lie identity makes the expansion
  symmetric in them (`PreLieBrace.expand_symm`), and the adjacent transpositions generate the
  symmetric group (`Equiv.Perm.mclosure_swap_castSucc_succ`).
* So the braces of a family indexed by a finite type do not depend on the numbering
  (`PreLieBrace.braceT`, `PreLieBrace.braceT_eq`).
-/
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Module.BigOperators

namespace Operad

namespace PreLieBrace

variable {R : Type*} [CommRing R] {L : Type*} [AddCommGroup L] [Module R L]
  (m : L →ₗ[R] L →ₗ[R] L)

/-- **The braces of a bilinear product**: `x{} = x` and
`x{y₁, …, y_k, z} = x{y₁, …, y_k} z - ∑ᵢ x{y₁, …, yᵢ z, …, y_k}`. -/
def brace : (k : ℕ) → L → (Fin k → L) → L
  | 0, x, _ => x
  | k + 1, x, y =>
    m (brace k x (Fin.init y)) (y (Fin.last k))
      - ∑ i : Fin k,
          brace k x (Function.update (Fin.init y) i (m (Fin.init y i) (y (Fin.last k))))

lemma brace_zero (x : L) (y : Fin 0 → L) : brace m 0 x y = x := rfl

lemma brace_succ (k : ℕ) (x : L) (y : Fin (k + 1) → L) :
    brace m (k + 1) x y = m (brace m k x (Fin.init y)) (y (Fin.last k))
      - ∑ i : Fin k,
          brace m k x (Function.update (Fin.init y) i (m (Fin.init y i) (y (Fin.last k)))) :=
  rfl

/-- The braces, on a family with a last entry. -/
lemma brace_snoc (k : ℕ) (x : L) (Y : Fin k → L) (z : L) :
    brace m (k + 1) x (Fin.snoc (α := fun _ => L) Y z)
      = m (brace m k x Y) z - ∑ i : Fin k, brace m k x (Function.update Y i (m (Y i) z)) := by
  rw [brace_succ, Fin.init_snoc, Fin.snoc_last]

/-- **The braces are additive in each entry.** -/
lemma brace_update_add : ∀ (k : ℕ) (x : L) (Y : Fin k → L) (j : Fin k) (u v : L),
    brace m k x (Function.update Y j (u + v))
      = brace m k x (Function.update Y j u) + brace m k x (Function.update Y j v)
  | 0, _, _, j, _, _ => j.elim0
  | k + 1, x, Y, j, u, v => by
    induction j using Fin.lastCases with
    | last =>
      simp only [brace_succ, Fin.init_update_last, Function.update_self, map_add]
      have h : ∀ i : Fin k,
          brace m k x (Function.update (Fin.init Y) i (m (Fin.init Y i) u + m (Fin.init Y i) v))
            = brace m k x (Function.update (Fin.init Y) i (m (Fin.init Y i) u))
              + brace m k x (Function.update (Fin.init Y) i (m (Fin.init Y i) v)) :=
        fun i => brace_update_add k x (Fin.init Y) i _ _
      rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib]
      abel
    | cast j =>
      have hl : ∀ w : L, Function.update Y j.castSucc w (Fin.last k) = Y (Fin.last k) :=
        fun w => Function.update_of_ne (Fin.castSucc_lt_last j).ne' _ _
      have hs : ∀ (w : L) (i : Fin k),
          brace m k x (Function.update (Function.update (Fin.init Y) j w) i
            (m (Function.update (Fin.init Y) j w i) (Y (Fin.last k))))
          = if i = j then brace m k x (Function.update (Fin.init Y) j (m w (Y (Fin.last k))))
            else brace m k x (Function.update (Function.update (Fin.init Y) i
              (m (Fin.init Y i) (Y (Fin.last k)))) j w) := by
        intro w i
        by_cases hij : i = j
        · subst hij
          rw [if_pos rfl, Function.update_self, Function.update_idem]
        · rw [if_neg hij, Function.update_of_ne hij, Function.update_comm hij]
      simp only [brace_succ, Fin.init_update_castSucc, hl, hs]
      rw [brace_update_add k x (Fin.init Y) j u v, map_add, LinearMap.add_apply]
      have h2 : ∀ i : Fin k,
          (if i = j then brace m k x (Function.update (Fin.init Y) j (m (u + v) (Y (Fin.last k))))
            else brace m k x (Function.update (Function.update (Fin.init Y) i
              (m (Fin.init Y i) (Y (Fin.last k)))) j (u + v)))
          = (if i = j then brace m k x (Function.update (Fin.init Y) j (m u (Y (Fin.last k))))
              else brace m k x (Function.update (Function.update (Fin.init Y) i
                (m (Fin.init Y i) (Y (Fin.last k)))) j u))
            + (if i = j then brace m k x (Function.update (Fin.init Y) j (m v (Y (Fin.last k))))
              else brace m k x (Function.update (Function.update (Fin.init Y) i
                (m (Fin.init Y i) (Y (Fin.last k)))) j v)) := by
        intro i
        by_cases hij : i = j
        · simp only [if_pos hij, map_add, LinearMap.add_apply]
          exact brace_update_add k x (Fin.init Y) j _ _
        · simp only [if_neg hij]
          exact brace_update_add k x _ j u v
      rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_add_distrib]
      abel

/-- The inner sum of the braces, when the entry `j` has been changed. -/
lemma sum_update_update (k : ℕ) (x : L) (Y : Fin k → L) (j : Fin k) (w a : L) :
    ∑ i : Fin k, brace m k x (Function.update (Function.update Y j w) i
        (m (Function.update Y j w i) a))
      = brace m k x (Function.update Y j (m w a))
        + ∑ i : Fin k, if i = j then 0
            else brace m k x (Function.update (Function.update Y j w) i (m (Y i) a)) := by
  have h : ∀ i : Fin k, brace m k x (Function.update (Function.update Y j w) i
        (m (Function.update Y j w i) a))
      = (if i = j then brace m k x (Function.update Y j (m w a)) else 0)
        + (if i = j then 0
            else brace m k x (Function.update (Function.update Y j w) i (m (Y i) a))) := by
    intro i
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl, add_zero, Function.update_self, Function.update_idem]
    · rw [if_neg hij, if_neg hij, zero_add, Function.update_of_ne hij]
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_univ j)]

/-- The braces with two more entries `a`, `b`, expanded in the braces without them. -/
def expand (k : ℕ) (x : L) (Y : Fin k → L) (a b : L) : L :=
  (m (m (brace m k x Y) a) b - m (brace m k x Y) (m a b))
    - ∑ j : Fin k, (m (brace m k x (Function.update Y j (m (Y j) a))) b
        + m (brace m k x (Function.update Y j (m (Y j) b))) a)
    + ∑ j : Fin k, brace m k x (Function.update Y j (m (Y j) (m a b) + m (m (Y j) b) a))
    + ∑ j : Fin k, ∑ i : Fin k, if i = j then 0
        else brace m k x (Function.update (Function.update Y j (m (Y j) b)) i (m (Y i) a))

lemma brace_snoc_snoc (k : ℕ) (x : L) (Y : Fin k → L) (a b : L) :
    brace m (k + 2) x (Fin.snoc (α := fun _ => L) (Fin.snoc (α := fun _ => L) Y a) b)
      = expand m k x Y a b := by
  have h1 : ∀ j : Fin k, brace m (k + 1) x
      (Function.update (Fin.snoc (α := fun _ => L) Y a) j.castSucc
        (m (Fin.snoc (α := fun _ => L) Y a j.castSucc) b))
      = m (brace m k x (Function.update Y j (m (Y j) b))) a
        - (brace m k x (Function.update Y j (m (m (Y j) b) a))
          + ∑ i : Fin k, if i = j then 0
              else brace m k x (Function.update (Function.update Y j (m (Y j) b)) i
                (m (Y i) a))) := by
    intro j
    rw [Fin.snoc_castSucc, ← Fin.snoc_update, brace_snoc, sum_update_update]
  have h2 : brace m (k + 1) x
      (Function.update (Fin.snoc (α := fun _ => L) Y a) (Fin.last k)
        (m (Fin.snoc (α := fun _ => L) Y a (Fin.last k)) b))
      = m (brace m k x Y) (m a b)
        - ∑ j : Fin k, brace m k x (Function.update Y j (m (Y j) (m a b))) := by
    rw [Fin.snoc_last, Fin.update_snoc_last, brace_snoc]
  rw [brace_snoc, Fin.sum_univ_castSucc, Finset.sum_congr rfl fun j _ => h1 j, h2, brace_snoc,
    map_sub, LinearMap.sub_apply, map_sum, LinearMap.sum_apply]
  unfold expand
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, brace_update_add]
  abel

/-- **The expansion is symmetric in the two new entries**, by the pre-Lie identity. -/
lemma expand_symm
    (hpl : ∀ x y z : L, m (m x y) z - m x (m y z) = m (m x z) y - m x (m z y))
    (k : ℕ) (x : L) (Y : Fin k → L) (a b : L) : expand m k x Y a b = expand m k x Y b a := by
  have g1 := hpl (brace m k x Y) a b
  have g2 : ∑ j : Fin k, (m (brace m k x (Function.update Y j (m (Y j) a))) b
        + m (brace m k x (Function.update Y j (m (Y j) b))) a)
      = ∑ j : Fin k, (m (brace m k x (Function.update Y j (m (Y j) b))) a
        + m (brace m k x (Function.update Y j (m (Y j) a))) b) :=
    Finset.sum_congr rfl fun j _ => add_comm _ _
  have g3 : ∀ j : Fin k, m (Y j) (m a b) + m (m (Y j) b) a
      = m (Y j) (m b a) + m (m (Y j) a) b := fun j => by
    have h := sub_eq_sub_iff_add_eq_add.1 (hpl (Y j) a b)
    rw [add_comm (m (Y j) (m a b)), add_comm (m (Y j) (m b a))]
    exact h.symm
  have g4 : ∑ j : Fin k, ∑ i : Fin k, (if i = j then 0
        else brace m k x (Function.update (Function.update Y j (m (Y j) b)) i (m (Y i) a)))
      = ∑ j : Fin k, ∑ i : Fin k, (if i = j then 0
        else brace m k x (Function.update (Function.update Y j (m (Y j) a)) i (m (Y i) b))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij.symm]
    · rw [if_neg hij, if_neg (Ne.symm hij), Function.update_comm (Ne.symm hij)]
  unfold expand
  rw [g1, g2, Finset.sum_congr rfl fun j _ => congrArg
    (fun w => brace m k x (Function.update Y j w)) (g3 j), g4]

/-- **The braces are symmetric in their last two entries.** -/
theorem brace_snoc_snoc_comm
    (hpl : ∀ x y z : L, m (m x y) z - m x (m y z) = m (m x z) y - m x (m z y))
    (k : ℕ) (x : L) (Y : Fin k → L) (a b : L) :
    brace m (k + 2) x (Fin.snoc (α := fun _ => L) (Fin.snoc (α := fun _ => L) Y a) b)
      = brace m (k + 2) x (Fin.snoc (α := fun _ => L) (Fin.snoc (α := fun _ => L) Y b) a) := by
  rw [brace_snoc_snoc, brace_snoc_snoc, expand_symm m hpl]

/-- A permutation of the entries before the last one, when the shorter braces are symmetric. -/
lemma brace_snoc_comp_perm (k : ℕ)
    (ih : ∀ (σ : Equiv.Perm (Fin k)) (x : L) (y : Fin k → L),
      brace m k x (y ∘ σ) = brace m k x y)
    (τ : Equiv.Perm (Fin k)) (x : L) (Y : Fin k → L) (b : L) :
    brace m (k + 1) x (Fin.snoc (α := fun _ => L) (Y ∘ τ) b)
      = brace m (k + 1) x (Fin.snoc (α := fun _ => L) Y b) := by
  rw [brace_snoc, brace_snoc, ih]
  congr 1
  have h : ∀ i : Fin k, brace m k x (Function.update (Y ∘ τ) i (m ((Y ∘ τ) i) b))
      = brace m k x (Function.update Y (τ i) (m (Y (τ i)) b)) := by
    intro i
    have e : Function.update (Y ∘ τ) i (m ((Y ∘ τ) i) b)
        = Function.update Y (τ i) (m (Y (τ i)) b) ∘ τ := by
      rw [Function.update_comp_equiv, Equiv.symm_apply_apply]
      rfl
    rw [e, ih]
  rw [Finset.sum_congr rfl fun i _ => h i]
  exact Equiv.sum_comp τ fun i => brace m k x (Function.update Y i (m (Y i) b))

/-- **The braces of a pre-Lie product are symmetric**: invariant under the permutations of their
entries. -/
theorem brace_comp_perm
    (hpl : ∀ x y z : L, m (m x y) z - m x (m y z) = m (m x z) y - m x (m z y)) :
    ∀ (k : ℕ) (σ : Equiv.Perm (Fin k)) (x : L) (y : Fin k → L),
      brace m k x (y ∘ σ) = brace m k x y
  | 0, _, _, _ => rfl
  | 1, σ, x, y => by
    rw [Subsingleton.elim σ 1]
    rfl
  | k + 2, σ, x, y => by
    have ih := brace_comp_perm hpl (k + 1)
    let H : Submonoid (Equiv.Perm (Fin (k + 2))) :=
      { carrier := {σ | ∀ (x : L) (y : Fin (k + 2) → L),
          brace m (k + 2) x (y ∘ σ) = brace m (k + 2) x y}
        one_mem' := fun _ _ => rfl
        mul_mem' := fun {σ τ} hσ hτ x y => by
          have e : y ∘ ⇑(σ * τ) = (y ∘ σ) ∘ τ := rfl
          rw [e, hτ, hσ] }
    have hgen : Set.range (fun i : Fin (k + 1) => Equiv.swap i.castSucc i.succ) ⊆ H := by
      rintro _ ⟨i, rfl⟩ x y
      induction i using Fin.lastCases with
      | last =>
        have e1 : y = Fin.snoc (α := fun _ => L)
            (Fin.snoc (α := fun _ => L) (Fin.init (Fin.init y))
              (y (Fin.last k).castSucc)) (y (Fin.last (k + 1))) := by
          funext j
          induction j using Fin.lastCases with
          | last => rw [Fin.snoc_last]
          | cast j =>
            rw [Fin.snoc_castSucc]
            induction j using Fin.lastCases with
            | last => rw [Fin.snoc_last]
            | cast j =>
              rw [Fin.snoc_castSucc]
              rfl
        have e2 : y ∘ Equiv.swap (Fin.last k).castSucc (Fin.last k).succ
            = Fin.snoc (α := fun _ => L)
              (Fin.snoc (α := fun _ => L) (Fin.init (Fin.init y))
                (y (Fin.last (k + 1)))) (y (Fin.last k).castSucc) := by
          funext j
          rw [Function.comp_apply, Fin.succ_last]
          induction j using Fin.lastCases with
          | last => rw [Fin.snoc_last, Equiv.swap_apply_right]
          | cast j =>
            rw [Fin.snoc_castSucc]
            induction j using Fin.lastCases with
            | last => rw [Fin.snoc_last, Equiv.swap_apply_left]
            | cast j =>
              rw [Fin.snoc_castSucc, Equiv.swap_apply_of_ne_of_ne
                (fun h => (Fin.castSucc_lt_last j).ne (Fin.castSucc_injective _ h))
                (Fin.castSucc_lt_last _).ne]
              rfl
        rw [e2]
        conv_rhs => rw [e1]
        exact (brace_snoc_snoc_comm m hpl k x _ _ _).symm
      | cast i =>
        have e1 : y = Fin.snoc (α := fun _ => L) (Fin.init y) (y (Fin.last (k + 1))) :=
          (Fin.snoc_init_self y).symm
        have e2 : y ∘ Equiv.swap i.castSucc.castSucc i.castSucc.succ
            = Fin.snoc (α := fun _ => L)
              (Fin.init y ∘ Equiv.swap i.castSucc i.succ) (y (Fin.last (k + 1))) := by
          funext j
          rw [Function.comp_apply, Fin.succ_castSucc]
          induction j using Fin.lastCases with
          | last =>
            rw [Fin.snoc_last, Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_lt_last _).ne'
              (Fin.castSucc_lt_last _).ne']
          | cast j =>
            rw [Fin.snoc_castSucc, (Fin.castSucc_injective _).swap_apply]
            rfl
        rw [e2]
        conv_rhs => rw [e1]
        exact brace_snoc_comp_perm m (k + 1) ih _ x _ _
    have htop : (⊤ : Submonoid (Equiv.Perm (Fin (k + 2)))) ≤ H := by
      rw [← Equiv.Perm.mclosure_swap_castSucc_succ (k + 1)]
      exact Submonoid.closure_le.2 hgen
    exact htop (Submonoid.mem_top σ) x y

/-- **The braces vanish when an entry does.** -/
lemma brace_update_zero (k : ℕ) (x : L) (Y : Fin k → L) (j : Fin k) :
    brace m k x (Function.update Y j 0) = 0 := by
  have h := brace_update_add m k x Y j 0 0
  rw [add_zero] at h
  calc brace m k x (Function.update Y j 0)
      = (brace m k x (Function.update Y j 0) + brace m k x (Function.update Y j 0))
        - brace m k x (Function.update Y j 0) := by abel
    _ = brace m k x (Function.update Y j 0) - brace m k x (Function.update Y j 0) := by
      rw [← h]
    _ = 0 := sub_self _

/-- **The braces are additive in each entry, over finite sums.** -/
lemma brace_update_sum {ι : Type*} (s : Finset ι) (k : ℕ) (x : L) (Y : Fin k → L) (j : Fin k)
    (f : ι → L) :
    brace m k x (Function.update Y j (∑ t ∈ s, f t))
      = ∑ t ∈ s, brace m k x (Function.update Y j (f t)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, brace_update_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, brace_update_add, ih]

/-- **The braces are homogeneous in each entry.** -/
lemma brace_update_smul : ∀ (k : ℕ) (x : L) (Y : Fin k → L) (j : Fin k) (c : R) (u : L),
    brace m k x (Function.update Y j (c • u)) = c • brace m k x (Function.update Y j u)
  | 0, _, _, j, _, _ => j.elim0
  | k + 1, x, Y, j, c, u => by
    induction j using Fin.lastCases with
    | last =>
      simp only [brace_succ, Fin.init_update_last, Function.update_self, map_smul, smul_sub,
        Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      exact brace_update_smul k x (Fin.init Y) i c _
    | cast j =>
      have hl : ∀ w : L, Function.update Y j.castSucc w (Fin.last k) = Y (Fin.last k) :=
        fun w => Function.update_of_ne (Fin.castSucc_lt_last j).ne' _ _
      have hs : ∀ (w : L) (i : Fin k),
          brace m k x (Function.update (Function.update (Fin.init Y) j w) i
            (m (Function.update (Fin.init Y) j w i) (Y (Fin.last k))))
          = if i = j then brace m k x (Function.update (Fin.init Y) j (m w (Y (Fin.last k))))
            else brace m k x (Function.update (Function.update (Fin.init Y) i
              (m (Fin.init Y i) (Y (Fin.last k)))) j w) := by
        intro w i
        by_cases hij : i = j
        · subst hij
          rw [if_pos rfl, Function.update_self, Function.update_idem]
        · rw [if_neg hij, Function.update_of_ne hij, Function.update_comm hij]
      simp only [brace_succ, Fin.init_update_castSucc, hl, hs]
      rw [brace_update_smul k x (Fin.init Y) j c u, map_smul, LinearMap.smul_apply, smul_sub,
        Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hij : i = j
      · simp only [if_pos hij, map_smul, LinearMap.smul_apply]
        exact brace_update_smul k x (Fin.init Y) j c _
      · simp only [if_neg hij]
        exact brace_update_smul k x _ j c u

/-- **The braces of a family indexed by a finite type**, through a numbering. -/
noncomputable def braceT (x : L) {ι : Type*} [Fintype ι] (f : ι → L) : L :=
  brace m (Fintype.card ι) x (f ∘ (Fintype.equivFin ι).symm)

/-- **The braces of a family indexed by a finite type do not depend on the numbering.** -/
theorem braceT_eq
    (hpl : ∀ x y z : L, m (m x y) z - m x (m y z) = m (m x z) y - m x (m z y))
    (x : L) {ι : Type*} [Fintype ι] (f : ι → L) {k : ℕ} (e : Fin k ≃ ι) :
    braceT m x f = brace m k x (f ∘ e) := by
  have hk : k = Fintype.card ι := by simpa using Fintype.card_congr e
  subst hk
  have h : f ∘ e = (f ∘ (Fintype.equivFin ι).symm) ∘ (e.trans (Fintype.equivFin ι)) := by
    funext i
    simp
  rw [h, brace_comp_perm m hpl]
  rfl

end PreLieBrace

end Operad
