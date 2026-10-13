/-
# Formal deformations of a symmetric operad, and rigidity

A **formal deformation** of a symmetric operad `P` over `R` (`FormalDeformation`) is a sequence of
two-cochains `μ_k`, with `μ_0` the composition of `P`, such that `x ⋆ y = Σ_k t^k μ_k(x, y)` is
an operad structure on `P[[t]]` with the action and the unit of `P`: order by order, equivariance,
the unit laws and the two associativity laws (Bao, Wang, Xu, Ye, Zhang, and Zhao, Def. 8.1, with
the action and the unit fixed). The power series then form a symmetric operad
(`FormalDeformation.Series`, `FormalDeformation.instSymOperad`).

A **trivialization** is a sequence of equivariant linear maps `φ_k`, `φ_0` the identity and `φ_k`
killing the unit for `k ≥ 1`, such that `Φ = Σ_k t^k φ_k` carries the composition of `P` to `⋆`:
`φ_n(x ∘ y) = Σ_{a+b+c=n} μ_a(φ_b x, φ_c y)` for every `n` (`IsMorAt`).

* **The obstruction is a cocycle** (`isCocycle_obstruction`): if `Φ` is a morphism up to order
  `n - 1`, its defect at order `n`, leaving out the terms with `φ_n` (`obstruction`), is a
  two-cocycle; and `Φ` extends to order `n` exactly when that cocycle is the coboundary of `φ_n`
  (`isMorAt_iff`). The proof embeds the first-order deformation `P_ω` of the obstruction into the
  power series modulo `t^{n+1}` (`truncIdeal`), and a linear map that is injective and carries
  the operations of `P_ω` to those of an operad makes `ω` a cocycle
  (`SymCochain.isCocycle_of_injective`).
* **Rigidity** (`exists_trivialization`): if every two-cocycle of `P` is a coboundary, every
  formal deformation has a trivialization (Bao, Wang, Xu, Ye, Zhang, and Zhao, Thm. 8.2, for the
  deformations with the action and the unit fixed).
* **The trivialization is an isomorphism** (`exists_iso_trivial`): `Φ` is then a morphism of
  operads from the power series of the trivial deformation (`trivial`, all `μ_k = 0` for
  `k ≥ 1`) to those of the given one (`trivHom`), bijective in each arity
  (`trivHomApp_bijective`, solving `Φ x = y` order by order) and the identity at order zero.
-/
import Operad.Deformation
import Operad.SymQuot
import Mathlib.Algebra.BigOperators.NatAntidiagonal

universe u v

namespace Operad

open Sym Finset

/-! ## Regrouping sums over antidiagonals -/

section Reindex

variable {β : Type*} [AddCommMonoid β]

/-- Regrouping the five indices of `(x ⋆ y) ⋆ z`: the outer orders first. -/
lemma sum_antidiagonal_reidx_left (m : ℕ) (G : ℕ → ℕ → ℕ → ℕ → ℕ → β) :
    ∑ p ∈ antidiagonal m, ∑ q ∈ antidiagonal p.2, ∑ r ∈ antidiagonal q.1,
      ∑ s ∈ antidiagonal r.2, G p.1 r.1 s.1 s.2 q.2
    = ∑ p ∈ antidiagonal m, ∑ q ∈ antidiagonal p.2, ∑ r ∈ antidiagonal q.2,
      ∑ s ∈ antidiagonal p.1, G s.1 s.2 q.1 r.1 r.2 := by
  simp only [Finset.sum_sigma']
  apply Finset.sum_nbij'
    (fun ⟨⟨a, _⟩, ⟨_, c⟩, ⟨a', _⟩, ⟨b', c'⟩⟩ =>
      ⟨⟨a + a', b' + c' + c⟩, ⟨b', c' + c⟩, ⟨c', c⟩, ⟨a, a'⟩⟩)
    (fun ⟨⟨_, _⟩, ⟨b', _⟩, ⟨c', c⟩, ⟨a, a'⟩⟩ =>
      ⟨⟨a, a' + b' + c' + c⟩, ⟨a' + b' + c', c⟩, ⟨a', b' + c'⟩, ⟨b', c'⟩⟩)
  all_goals aesop (add simp [Finset.mem_sigma, Finset.mem_antidiagonal]) (add safe (by omega))

/-- Regrouping the five indices of `x ⋆ (y ⋆ z)`: the outer orders first. -/
lemma sum_antidiagonal_reidx_right (m : ℕ) (H : ℕ → ℕ → ℕ → ℕ → ℕ → β) :
    ∑ p ∈ antidiagonal m, ∑ q ∈ antidiagonal p.2, ∑ r ∈ antidiagonal q.2,
      ∑ s ∈ antidiagonal r.2, H p.1 q.1 r.1 s.1 s.2
    = ∑ p ∈ antidiagonal m, ∑ q ∈ antidiagonal p.2, ∑ r ∈ antidiagonal q.2,
      ∑ s ∈ antidiagonal p.1, H s.1 q.1 s.2 r.1 r.2 := by
  simp only [Finset.sum_sigma']
  apply Finset.sum_nbij'
    (fun ⟨⟨a, _⟩, ⟨b, _⟩, ⟨a'', _⟩, ⟨b'', c''⟩⟩ =>
      ⟨⟨a + a'', b + b'' + c''⟩, ⟨b, b'' + c''⟩, ⟨b'', c''⟩, ⟨a, a''⟩⟩)
    (fun ⟨⟨_, _⟩, ⟨b, _⟩, ⟨b'', c''⟩, ⟨a, a''⟩⟩ =>
      ⟨⟨a, b + a'' + b'' + c''⟩, ⟨b, a'' + b'' + c''⟩, ⟨a'', b'' + c''⟩, ⟨b'', c''⟩⟩)
  all_goals aesop (add simp [Finset.mem_sigma, Finset.mem_antidiagonal]) (add safe (by omega))

end Reindex

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]

/-! ## Formal deformations -/

variable (R P) in
/-- **A formal deformation** of `P`: two-cochains `μ_k` with `μ_0` the composition of `P`, such
that `x ⋆ y = Σ_k t^k μ_k(x, y)` is an operad structure on `P[[t]]` with the action and the unit of
`P`, written order by order. -/
structure FormalDeformation where
  /-- The coefficient of `t^k` of the deformed composition. -/
  μ : ℕ → SymCochain R P
  /-- The constant term is the composition of `P`. -/
  μ_zero : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (x : P A) (y : P B), μ 0 i x y = SymOperad.comp (R := R) i x y
  /-- Equivariance. -/
  map_comp : ∀ (k : ℕ) {A A' B B' : Type} [Fintype A] [DecidableEq A] [Fintype A']
    [DecidableEq A'] [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] (σ : A ≃ A')
    (τ : B ≃ B') (i : A) (x : P A) (y : P B),
    SymOperad.map (R := R) (compEquiv σ τ i) (μ k i x y)
      = μ k (σ i) (SymOperad.map (R := R) σ x) (SymOperad.map (R := R) τ y)
  /-- The right unit, in positive order. -/
  comp_one : ∀ (k : ℕ), k ≠ 0 → ∀ {A : Type} [Fintype A] [DecidableEq A] (i : A) (x : P A),
    μ k i x (SymOperad.one R) = 0
  /-- The left unit, in positive order. -/
  one_comp : ∀ (k : ℕ), k ≠ 0 → ∀ {B : Type} [Fintype B] [DecidableEq B] (y : P B),
    μ k () (SymOperad.one R) y = 0
  /-- Sequential associativity, at order `n`. -/
  assoc_seq : ∀ (n : ℕ) {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] (i : A) (j : B) (x : P A) (y : P B) (z : P D),
    SymOperad.map (R := R) (seqEquiv i j D)
        (∑ p ∈ antidiagonal n, μ p.1 (Sum.inr j) (μ p.2 i x y) z)
      = ∑ p ∈ antidiagonal n, μ p.1 i x (μ p.2 j y z)
  /-- Parallel associativity, at order `n`. -/
  assoc_par : ∀ (n : ℕ) {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] {i k : A} (hik : i ≠ k) (x : P A) (y : P B) (z : P D),
    SymOperad.map (R := R) (parEquiv hik B D)
        (∑ p ∈ antidiagonal n, μ p.1 (Sum.inl ⟨k, Ne.symm hik⟩) (μ p.2 i x y) z)
      = ∑ p ∈ antidiagonal n, μ p.1 (Sum.inl ⟨i, hik⟩) (μ p.2 k x z) y

namespace FormalDeformation

variable (μ : FormalDeformation R P)

/-! ### The deformed operad on power series -/

/-- The power series `P(A)[[t]]`, with the deformed composition of `μ`. -/
@[nolint unusedArguments]
def Series (_μ : FormalDeformation R P) (A : Type) [Fintype A] [DecidableEq A] : Type v :=
  ℕ → P A

instance (A : Type) [Fintype A] [DecidableEq A] : AddCommGroup (μ.Series A) :=
  inferInstanceAs (AddCommGroup (ℕ → P A))

instance (A : Type) [Fintype A] [DecidableEq A] : Module R (μ.Series A) :=
  inferInstanceAs (Module R (ℕ → P A))

variable {A B C D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C]
  [DecidableEq C] [Fintype D] [DecidableEq D]

/-- The coefficient `m` of a series. -/
def coeff (m : ℕ) : μ.Series A →ₗ[R] P A where
  toFun x := x m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma coeff_apply (m : ℕ) (x : μ.Series A) : μ.coeff m x = x m := rfl

@[ext] lemma ext' {x y : μ.Series A} (h : ∀ m, x m = y m) : x = y := funext h

@[simp] lemma add_apply' (x y : μ.Series A) (m : ℕ) : (x + y) m = x m + y m := rfl

@[simp] lemma smul_apply' (c : R) (x : μ.Series A) (m : ℕ) : (c • x) m = c • x m := rfl

@[simp] lemma zero_apply' (m : ℕ) : (0 : μ.Series A) m = 0 := rfl

/-- Relabelling, coefficient by coefficient. -/
def smap (e : A ≃ B) : μ.Series A →ₗ[R] μ.Series B where
  toFun x m := SymOperad.map (R := R) e (x m)
  map_add' x y := funext fun m => map_add _ (x m) (y m)
  map_smul' c x := funext fun m => map_smul _ c (x m)

@[simp] lemma smap_apply (e : A ≃ B) (x : μ.Series A) (m : ℕ) :
    μ.smap e x m = SymOperad.map (R := R) e (x m) := rfl

/-- **The deformed composition**: the coefficient `m` of `x ⋆ᵢ y` is
`Σ_{a+b+c=m} μ_a(x_b, y_c)`. -/
def scomp (i : A) : μ.Series A →ₗ[R] μ.Series B →ₗ[R] μ.Series (Without A i ⊕ B) :=
  LinearMap.mk₂ R
    (fun x y m => ∑ p ∈ antidiagonal m, ∑ q ∈ antidiagonal p.2, μ.μ p.1 i (x q.1) (y q.2))
    (fun x x' y => funext fun m => by
      simp only [add_apply', map_add, LinearMap.add_apply, Finset.sum_add_distrib])
    (fun c x y => funext fun m => by
      simp only [smul_apply', map_smul, LinearMap.smul_apply, Finset.smul_sum])
    (fun x y y' => funext fun m => by
      simp only [add_apply', map_add, Finset.sum_add_distrib])
    (fun c x y => funext fun m => by
      simp only [smul_apply', map_smul, Finset.smul_sum])

lemma scomp_apply (i : A) (x : μ.Series A) (y : μ.Series B) (m : ℕ) :
    μ.scomp i x y m
      = ∑ p ∈ antidiagonal m, ∑ q ∈ antidiagonal p.2, μ.μ p.1 i (x q.1) (y q.2) := rfl

/-- The unit series. -/
def sone : μ.Series Unit := fun m => if m = 0 then SymOperad.one R else 0

/-- The inner sum of `x ⋆ 1`: only `y_0 = 1` survives. -/
lemma sum_comp_sone (i : A) (x : μ.Series A) (a k : ℕ) :
    ∑ q ∈ antidiagonal k, μ.μ a i (x q.1) (μ.sone q.2) = μ.μ a i (x k) (SymOperad.one R) := by
  rw [Finset.sum_eq_single (k, 0)]
  · rfl
  · intro q hq hne
    have : q.2 ≠ 0 := by
      intro h
      apply hne
      rw [Finset.mem_antidiagonal] at hq
      ext <;> simp <;> omega
    simp [sone, this]
  · intro h
    exact absurd (Finset.mem_antidiagonal.mpr (by simp)) h

/-- The inner sum of `1 ⋆ y`: only `x_0 = 1` survives. -/
lemma sum_sone_comp (y : μ.Series B) (a k : ℕ) :
    ∑ q ∈ antidiagonal k, μ.μ a () (μ.sone q.1) (y q.2) = μ.μ a () (SymOperad.one R) (y k) := by
  rw [Finset.sum_eq_single (0, k)]
  · rfl
  · intro q hq hne
    have : q.1 ≠ 0 := by
      intro h
      apply hne
      rw [Finset.mem_antidiagonal] at hq
      ext <;> simp <;> omega
    simp [sone, this]
  · intro h
    exact absurd (Finset.mem_antidiagonal.mpr (by simp)) h

/-- Of a sum over `antidiagonal m` of a term vanishing in positive first index, only `(0, m)`
survives. -/
lemma sum_antidiagonal_fst_zero {M : Type*} [AddCommMonoid M] (m : ℕ) (f : ℕ → ℕ → M)
    (hf : ∀ a b, a ≠ 0 → f a b = 0) : ∑ p ∈ antidiagonal m, f p.1 p.2 = f 0 m := by
  rw [Finset.sum_eq_single (0, m)]
  · intro p _ hne
    apply hf
    intro h
    apply hne
    have := Finset.mem_antidiagonal.mp ‹_›
    ext <;> simp <;> omega
  · intro h
    exact absurd (Finset.mem_antidiagonal.mpr (by simp)) h

/-- **The power series form an operad** under the deformed composition. -/
instance instSymOperad : SymOperad R μ.Series where
  map e := μ.smap e
  map_refl x := funext fun m => SymOperad.map_refl (R := R) (x m)
  map_trans e f x := funext fun m => SymOperad.map_trans (R := R) e f (x m)
  one := μ.sone
  comp i := μ.scomp i
  map_comp σ τ i x y := funext fun m => by
    simp only [smap_apply, scomp_apply, map_sum, μ.map_comp]
  comp_one i x := funext fun m => by
    simp only [smap_apply, scomp_apply, sum_comp_sone]
    rw [sum_antidiagonal_fst_zero m (fun a b => μ.μ a i (x b) (SymOperad.one R))
      (fun a b ha => μ.comp_one a ha i (x b)), μ.μ_zero, SymOperad.comp_one]
  one_comp y := funext fun m => by
    simp only [smap_apply, scomp_apply, sum_sone_comp]
    rw [sum_antidiagonal_fst_zero m (fun a b => μ.μ a () (SymOperad.one R) (y b))
      (fun a b ha => μ.one_comp a ha (y b)), μ.μ_zero, SymOperad.one_comp]
  comp_assoc_seq i j x y z := funext fun m => by
    simp only [smap_apply, scomp_apply, map_sum, LinearMap.sum_apply]
    rw [sum_antidiagonal_reidx_left m
      (fun a a' b' c' c => SymOperad.map (R := R) (seqEquiv i j _)
        (μ.μ a (Sum.inr j) (μ.μ a' i (x b') (y c')) (z c))),
      sum_antidiagonal_reidx_right m
      (fun a b a'' b'' c'' => μ.μ a i (x b) (μ.μ a'' j (y b'') (z c'')))]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
      Finset.sum_congr rfl fun r _ => ?_
    rw [← map_sum, μ.assoc_seq]
  comp_assoc_par hik x y z := funext fun m => by
    simp only [smap_apply, scomp_apply, map_sum, LinearMap.sum_apply]
    rw [sum_antidiagonal_reidx_left m
      (fun a a' b' c' c => SymOperad.map (R := R) (parEquiv hik _ _)
        (μ.μ a (Sum.inl ⟨_, Ne.symm hik⟩) (μ.μ a' _ (x b') (y c')) (z c))),
      sum_antidiagonal_reidx_left m
      (fun a a' b' c' c => μ.μ a (Sum.inl ⟨_, hik⟩) (μ.μ a' _ (x b') (z c')) (y c))]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [← Finset.Nat.sum_antidiagonal_swap]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← map_sum, μ.assoc_par]
    rfl

/-! ### The power series modulo `t^{n+1}` -/

/-- **The ideal `t^{n+1} P[[t]]`**: the series vanishing up to order `n`. -/
def truncIdeal (n : ℕ) : SymOperadIdeal R μ.Series where
  sub A _ _ :=
    { carrier := {x | ∀ m ≤ n, x m = 0}
      add_mem' := fun {x y} hx hy m hm => by
        rw [add_apply', hx m hm, hy m hm, add_zero]
      zero_mem' := fun _ _ => rfl
      smul_mem' := fun c x hx m hm => by
        rw [smul_apply', hx m hm, smul_zero] }
  map_mem := by
    intro A B _ _ _ _ e x hx m hm
    show SymOperad.map (R := R) e (x m) = 0
    rw [hx m hm, map_zero]
  comp_mem_left := by
    intro A B _ _ _ _ i x y hx m hm
    show ∑ p ∈ antidiagonal m, ∑ q ∈ antidiagonal p.2, μ.μ p.1 i (x q.1) (y q.2) = 0
    refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => ?_
    have h1 := Finset.mem_antidiagonal.mp hp
    have h2 := Finset.mem_antidiagonal.mp hq
    rw [hx q.1 (by omega), map_zero, LinearMap.zero_apply]
  comp_mem_right := by
    intro A B _ _ _ _ i x y hy m hm
    show ∑ p ∈ antidiagonal m, ∑ q ∈ antidiagonal p.2, μ.μ p.1 i (x q.1) (y q.2) = 0
    refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => ?_
    have h1 := Finset.mem_antidiagonal.mp hp
    have h2 := Finset.mem_antidiagonal.mp hq
    rw [hy q.2 (by omega), map_zero]

lemma proj_eq_of_coeff {n : ℕ} {x y : μ.Series A} (h : ∀ m ≤ n, x m = y m) :
    (μ.truncIdeal n).proj A x = (μ.truncIdeal n).proj A y := by
  rw [← sub_eq_zero, ← map_sub, SymOperadIdeal.proj_eq_zero_iff]
  intro m hm
  show (x - y) m = 0
  rw [show (x - y) m = x m - y m from rfl, h m hm, sub_self]

/-! ### Trivializations, and the obstruction -/

/-- **`Φ = Σ t^k φ_k` carries the composition of `P` to `⋆` at order `n`**:
`φ_n(x ∘ y) = Σ_{a+b+c=n} μ_a(φ_b x, φ_c y)`. -/
def IsMorAt (φ : ℕ → SymEndo R P) (n : ℕ) : Prop :=
  ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A) (x : P A)
    (y : P B), (φ n).app _ (SymOperad.comp (R := R) i x y)
      = ∑ p ∈ antidiagonal n, ∑ q ∈ antidiagonal p.2, μ.μ p.1 i ((φ q.1).app A x) ((φ q.2).app B y)

/-- The terms of order `n` not involving the coefficients of order `n`. -/
def lowPairs (n : ℕ) (k : ℕ) : Finset (ℕ × ℕ) := (antidiagonal k).filter fun q => q.1 < n ∧ q.2 < n

/-- **The obstruction at order `n`**: the right side of `IsMorAt φ n` without the two terms
`φ_n x ∘ y` and `x ∘ φ_n y`. -/
def obstruction (φ : ℕ → SymEndo R P) (n : ℕ) : SymCochain R P := fun A B _ _ _ _ i =>
  ∑ p ∈ antidiagonal n, ∑ q ∈ lowPairs n p.2, (μ.μ p.1 i).compl₁₂ ((φ q.1).app A) ((φ q.2).app B)

lemma obstruction_apply (φ : ℕ → SymEndo R P) (n : ℕ) (i : A) (x : P A) (y : P B) :
    μ.obstruction φ n i x y
      = ∑ p ∈ antidiagonal n, ∑ q ∈ lowPairs n p.2,
          μ.μ p.1 i ((φ q.1).app A x) ((φ q.2).app B y) := by
  simp only [obstruction, LinearMap.coe_sum, Finset.sum_apply, LinearMap.compl₁₂_apply]

/-- **The sum at order `n ≥ 1` splits** into the two terms with an input of order `n` and those of
lower order. -/
lemma sum_split {n : ℕ} (hn : 1 ≤ n) (i : A) (X : ℕ → P A) (Y : ℕ → P B) :
    ∑ p ∈ antidiagonal n, ∑ q ∈ antidiagonal p.2, μ.μ p.1 i (X q.1) (Y q.2)
      = SymOperad.comp (R := R) i (X n) (Y 0) + SymOperad.comp (R := R) i (X 0) (Y n)
        + ∑ p ∈ antidiagonal n, ∑ q ∈ lowPairs n p.2, μ.μ p.1 i (X q.1) (Y q.2) := by
  have hsplit : ∀ p : ℕ × ℕ, ∑ q ∈ antidiagonal p.2, μ.μ p.1 i (X q.1) (Y q.2)
      = ∑ q ∈ lowPairs n p.2, μ.μ p.1 i (X q.1) (Y q.2)
        + ∑ q ∈ (antidiagonal p.2).filter (fun q => ¬ (q.1 < n ∧ q.2 < n)),
            μ.μ p.1 i (X q.1) (Y q.2) := fun p =>
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  simp only [hsplit, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  rw [Finset.sum_eq_single (0, n)]
  · have hf : (antidiagonal n).filter (fun q => ¬ (q.1 < n ∧ q.2 < n)) = {(n, 0), (0, n)} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_insert,
        Finset.mem_singleton, Prod.ext_iff]
      omega
    rw [hf, Finset.sum_pair (by simp; omega), μ.μ_zero, μ.μ_zero]
  · intro p hp hne
    rw [Finset.mem_antidiagonal] at hp
    have hp1 : p.1 ≠ 0 := fun h => hne (Prod.ext h (by simp; omega))
    refine Finset.sum_eq_zero fun q hq => absurd hq ?_
    rw [Finset.mem_filter, Finset.mem_antidiagonal]
    omega
  · intro h
    exact absurd (Finset.mem_antidiagonal.mpr (by simp)) h

/-- **`Φ` extends to order `n` exactly when the obstruction is the coboundary of `φ_n`.** -/
lemma isMorAt_iff (φ : ℕ → SymEndo R P)
    (hφ0 : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : P A), (φ 0).app A x = x) {n : ℕ}
    (hn : 1 ≤ n) :
    μ.IsMorAt φ n ↔ ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
      (i : A) (x : P A) (y : P B), μ.obstruction φ n i x y = (φ n).coboundary i x y := by
  constructor
  · intro h A B _ _ _ _ i x y
    rw [SymEndo.coboundary_apply, h, μ.sum_split hn i (fun k => (φ k).app A x)
      (fun k => (φ k).app B y), hφ0, hφ0, obstruction_apply]
    abel
  · intro h A B _ _ _ _ i x y
    have := h i x y
    rw [SymEndo.coboundary_apply, obstruction_apply] at this
    rw [μ.sum_split hn i (fun k => (φ k).app A x) (fun k => (φ k).app B y), hφ0, hφ0, this]
    abel

end FormalDeformation

/-! ## A cocycle from an embedding into an operad -/

namespace SymCochain

variable {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]

/-- **A cochain is a cocycle as soon as its deformed operations embed into an operad**: if
injective linear maps `P_ω(A) → Q(A)` carry the relabelling, the unit and the deformed composition
of `P_ω` to those of an operad `Q`, then `ω` is a cocycle. -/
theorem isCocycle_of_injective {ω : SymCochain R P}
    (Ψ : ∀ (A : Type) [Fintype A] [DecidableEq A], Deformed ω A →ₗ[R] Q A)
    (hinj : ∀ (A : Type) [Fintype A] [DecidableEq A], Function.Injective (Ψ A))
    (hmap : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
      (z : Deformed ω A), Ψ B (Deformed.map ω e z) = SymOperad.map (R := R) e (Ψ A z))
    (hone : Ψ Unit (Deformed.mk (SymOperad.one R) 0) = SymOperad.one R)
    (hcomp : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
      (z : Deformed ω A) (z' : Deformed ω B),
      Ψ _ (Deformed.comp ω i z z') = SymOperad.comp (R := R) i (Ψ A z) (Ψ B z')) :
    ω.IsCocycle := by
  let S : SymOperad R (Deformed ω) :=
    { map := fun e => Deformed.map ω e
      map_refl := fun z => hinj _ (by rw [hmap, SymOperad.map_refl])
      map_trans := fun e f z => hinj _ (by rw [hmap, hmap, hmap, SymOperad.map_trans])
      one := Deformed.mk (SymOperad.one R) 0
      comp := fun i => Deformed.comp ω i
      map_comp := fun σ τ i z z' => hinj _ (by
        rw [hmap, hcomp, hcomp, hmap, hmap, SymOperad.map_comp])
      comp_one := fun i z => hinj _ (by rw [hmap, hcomp, hone, SymOperad.comp_one])
      one_comp := fun z => hinj _ (by rw [hmap, hcomp, hone, SymOperad.one_comp])
      comp_assoc_seq := fun i j x y z => hinj _ (by
        simp only [hmap, hcomp]
        exact SymOperad.comp_assoc_seq (R := R) i j _ _ _)
      comp_assoc_par := fun hik x y z => hinj _ (by
        simp only [hmap, hcomp]
        exact SymOperad.comp_assoc_par (R := R) hik _ _ _) }
  exact Deformed.isCocycle_of_symOperad S (fun _ => rfl) rfl (fun _ => rfl)

end SymCochain

namespace FormalDeformation

variable (μ : FormalDeformation R P) {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
  [DecidableEq B]

/-- The series `Σ_{m < n} t^m φ_m(x) + t^n x'` of a pair `(x, x')`. -/
def ser (φ : ℕ → SymEndo R P) (n : ℕ) (ω : SymCochain R P) (A : Type) [Fintype A]
    [DecidableEq A] : Deformed ω A →ₗ[R] μ.Series A where
  toFun z m := if m < n then (φ m).app A (Deformed.fst z) else if m = n then Deformed.snd z else 0
  map_add' z z' := funext fun m => by
    rw [add_apply']
    simp only [Deformed.fst_add, Deformed.snd_add, map_add]
    split_ifs <;> simp
  map_smul' c z := funext fun m => by
    rw [RingHom.id_apply, smul_apply']
    simp only [Deformed.fst_smul, Deformed.snd_smul, map_smul]
    split_ifs <;> simp

lemma ser_apply (φ : ℕ → SymEndo R P) (n : ℕ) (ω : SymCochain R P) (z : Deformed ω A) (m : ℕ) :
    μ.ser φ n ω A z m
      = if m < n then (φ m).app A (Deformed.fst z) else if m = n then Deformed.snd z else 0 := rfl

lemma ser_lt (φ : ℕ → SymEndo R P) {n : ℕ} (ω : SymCochain R P) (z : Deformed ω A) {m : ℕ}
    (hm : m < n) : μ.ser φ n ω A z m = (φ m).app A (Deformed.fst z) := by
  rw [ser_apply, if_pos hm]

lemma ser_self (φ : ℕ → SymEndo R P) (n : ℕ) (ω : SymCochain R P) (z : Deformed ω A) :
    μ.ser φ n ω A z n = Deformed.snd z := by
  rw [ser_apply, if_neg (lt_irrefl n), if_pos rfl]

/-- **The obstruction is a cocycle**: if `Φ` is a morphism up to order `n - 1`, its obstruction at
order `n` is a two-cocycle. -/
theorem isCocycle_obstruction (φ : ℕ → SymEndo R P)
    (hφ0 : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : P A), (φ 0).app A x = x)
    (hφ1 : ∀ k, k ≠ 0 → (φ k).app Unit (SymOperad.one R) = 0) {n : ℕ} (hn : 1 ≤ n)
    (hmor : ∀ m < n, μ.IsMorAt φ m) : (μ.obstruction φ n).IsCocycle := by
  set ω := μ.obstruction φ n
  refine SymCochain.isCocycle_of_injective (Q := (μ.truncIdeal n).Quot)
    (fun A _ _ => ((μ.truncIdeal n).proj A).comp (μ.ser φ n ω A)) ?_ ?_ ?_ ?_
  · intro A _ _
    refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
    rw [LinearMap.comp_apply, SymOperadIdeal.proj_eq_zero_iff] at hz
    have h0 := hz 0 (Nat.zero_le _)
    have hn' := hz n le_rfl
    rw [ser_lt _ _ _ _ (by omega), hφ0] at h0
    rw [ser_self] at hn'
    exact Deformed.ext h0 hn'
  · intro A B _ _ _ _ e z
    simp only [LinearMap.comp_apply]
    rw [show SymOperad.map (R := R) e ((μ.truncIdeal n).proj A (μ.ser φ n ω A z))
        = (μ.truncIdeal n).proj B (μ.smap e (μ.ser φ n ω A z)) from rfl]
    refine μ.proj_eq_of_coeff fun m _ => ?_
    simp only [ser_apply, smap_apply, Deformed.fst_map, Deformed.snd_map, (φ m).app_map]
    split_ifs <;> simp
  · simp only [LinearMap.comp_apply]
    refine μ.proj_eq_of_coeff fun m hm => ?_
    simp only [ser_apply, Deformed.fst_mk, Deformed.snd_mk]
    show _ = μ.sone m
    simp only [sone]
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · rw [if_pos (show 0 < n by omega), hφ0, if_pos rfl]
    · rw [if_neg (show ¬ m = 0 by omega)]
      split_ifs with h
      · exact hφ1 m (by omega)
      · rfl
      · rfl
  · intro A B _ _ _ _ i z z'
    simp only [LinearMap.comp_apply]
    rw [show SymOperad.comp (R := R) i ((μ.truncIdeal n).proj A (μ.ser φ n ω A z))
        ((μ.truncIdeal n).proj B (μ.ser φ n ω B z'))
        = (μ.truncIdeal n).proj _ (μ.scomp i (μ.ser φ n ω A z) (μ.ser φ n ω B z')) from rfl]
    refine μ.proj_eq_of_coeff fun m hm => ?_
    rw [scomp_apply]
    rcases lt_or_eq_of_le hm with hlt | rfl
    · rw [ser_lt _ _ _ _ hlt, Deformed.fst_comp, hmor m hlt]
      refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
      have h1 := Finset.mem_antidiagonal.mp hp
      have h2 := Finset.mem_antidiagonal.mp hq
      rw [ser_lt _ _ _ _ (by omega), ser_lt _ _ _ _ (by omega)]
    · rw [ser_self, Deformed.snd_comp, μ.sum_split hn, ser_self, ser_self,
        ser_lt _ _ _ _ (show 0 < m by omega), ser_lt _ _ _ _ (show 0 < m by omega), hφ0, hφ0,
        obstruction_apply]
      congr 1
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q hq => ?_
      have := (Finset.mem_filter.mp hq).2
      rw [ser_lt _ _ _ _ this.1, ser_lt _ _ _ _ this.2]

/-! ### Rigidity -/

/-- The identity, as an equivariant family. -/
def idEndo : SymEndo R P := ⟨fun _ _ _ => LinearMap.id, fun _ _ => rfl⟩

/-- The zero equivariant family. -/
def zeroEndo : SymEndo R P := ⟨fun _ _ _ => 0, fun _ _ => by simp⟩

omit μ in
@[simp] lemma idEndo_app (x : P A) : (idEndo : SymEndo R P).app A x = x := rfl

omit μ in
@[simp] lemma zeroEndo_app (x : P A) : (zeroEndo : SymEndo R P).app A x = 0 := rfl

/-- The start of the trivializations: the identity in order zero, nothing above. -/
def triv0 : ℕ → SymEndo R P := fun k => if k = 0 then idEndo else zeroEndo

omit μ in
lemma triv0_zero (A : Type) [Fintype A] [DecidableEq A] (x : P A) :
    (triv0 0 : SymEndo R P).app A x = x := by
  simp [triv0]

omit μ in
lemma triv0_ne {k : ℕ} (hk : k ≠ 0) : (triv0 k : SymEndo R P) = zeroEndo := by
  simp [triv0, hk]

/-- **A trivialization up to order `N`.** -/
def PartialTriv (N : ℕ) (φ : ℕ → SymEndo R P) : Prop :=
  (∀ (A : Type) [Fintype A] [DecidableEq A] (x : P A), (φ 0).app A x = x) ∧
    (∀ k, k ≠ 0 → (φ k).app Unit (SymOperad.one R) = 0) ∧ ∀ n ≤ N, μ.IsMorAt φ n

lemma isMorAt_congr {φ ψ : ℕ → SymEndo R P} {n : ℕ} (h : ∀ k ≤ n, φ k = ψ k)
    (hφ : μ.IsMorAt φ n) : μ.IsMorAt ψ n := by
  intro A B _ _ _ _ i x y
  rw [← h n le_rfl, hφ]
  refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
  have h1 := Finset.mem_antidiagonal.mp hp
  have h2 := Finset.mem_antidiagonal.mp hq
  rw [h q.1 (by omega), h q.2 (by omega)]

lemma obstruction_congr {φ ψ : ℕ → SymEndo R P} {n : ℕ} (h : ∀ k < n, φ k = ψ k) (i : A)
    (x : P A) (y : P B) : μ.obstruction φ n i x y = μ.obstruction ψ n i x y := by
  rw [obstruction_apply, obstruction_apply]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q hq => ?_
  have := (Finset.mem_filter.mp hq).2
  rw [h q.1 this.1, h q.2 this.2]

lemma isMorAt_zero (φ : ℕ → SymEndo R P)
    (hφ0 : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : P A), (φ 0).app A x = x) :
    μ.IsMorAt φ 0 := by
  intro A B _ _ _ _ i x y
  simp [hφ0, μ.μ_zero]

/-- **One step**: if every cocycle is a coboundary, a trivialization up to order `N` extends to
order `N + 1` by choosing its coefficient of order `N + 1`. -/
theorem exists_step (hH2 : ∀ ω : SymCochain R P, ω.IsCocycle → ω.IsCoboundary) {N : ℕ}
    {φ : ℕ → SymEndo R P} (hφ : μ.PartialTriv N φ) :
    ∃ ψ : SymEndo R P, μ.PartialTriv (N + 1) (Function.update φ (N + 1) ψ) := by
  obtain ⟨hφ0, hφ1, hmor⟩ := hφ
  have hcoc := μ.isCocycle_obstruction φ hφ0 hφ1 (Nat.succ_pos N) fun m hm =>
    hmor m (by omega)
  obtain ⟨ψ, hψ⟩ := hH2 _ hcoc
  have hψ1 := SymCochain.app_one_eq_zero hcoc ψ hψ
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro A _ _ x
    rw [Function.update_of_ne (by omega)]
    exact hφ0 A x
  · intro k hk
    by_cases h : k = N + 1
    · subst h
      rw [Function.update_self]
      exact hψ1
    · rw [Function.update_of_ne h]
      exact hφ1 k hk
  · intro n hn
    rcases (show n ≤ N ∨ n = N + 1 by omega) with h | rfl
    · exact μ.isMorAt_congr
        (fun k hk => (Function.update_of_ne (show k ≠ N + 1 by omega) ψ φ).symm) (hmor n h)
    · have h0 : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : P A),
          (Function.update φ (N + 1) ψ 0).app A x = x := fun A _ _ x => by
        rw [Function.update_of_ne (by omega)]
        exact hφ0 A x
      rw [μ.isMorAt_iff _ h0 (Nat.succ_pos N)]
      intro A B _ _ _ _ i x y
      rw [μ.obstruction_congr (ψ := φ)
        (fun k hk => Function.update_of_ne (show k ≠ N + 1 by omega) ψ φ), Function.update_self]
      exact hψ i x y

/-- The trivializations up to each order, each extending the previous one. -/
noncomputable def build (hH2 : ∀ ω : SymCochain R P, ω.IsCocycle → ω.IsCoboundary) :
    (N : ℕ) → {φ : ℕ → SymEndo R P // μ.PartialTriv N φ}
  | 0 => ⟨triv0, triv0_zero, fun k hk => by rw [triv0_ne hk, zeroEndo_app],
      fun n hn => by
        obtain rfl : n = 0 := by omega
        exact μ.isMorAt_zero _ triv0_zero⟩
  | N + 1 => ⟨Function.update (build hH2 N).1 (N + 1)
      (Classical.choose (μ.exists_step hH2 (build hH2 N).2)),
      Classical.choose_spec (μ.exists_step hH2 (build hH2 N).2)⟩

lemma build_stable (hH2 : ∀ ω : SymCochain R P, ω.IsCocycle → ω.IsCoboundary) :
    ∀ N k, k ≤ N → (μ.build hH2 N).1 k = (μ.build hH2 k).1 k
  | 0, k, hk => by obtain rfl : k = 0 := by omega
                   rfl
  | N + 1, k, hk => by
      rcases (show k ≤ N ∨ k = N + 1 by omega) with h | rfl
      · show Function.update _ _ _ k = _
        rw [Function.update_of_ne (by omega)]
        exact build_stable hH2 N k h
      · rfl

/-- **Rigidity** (Bao, Wang, Xu, Ye, Zhang, and Zhao, Thm. 8.2, for the deformations with the
action and the unit fixed): if every two-cocycle of `P` is a coboundary, every formal deformation of
`P` has a trivialization, equivariant linear maps `φ_k` with `φ_0 = id`, `φ_k(1) = 0` for `k ≥ 1`
and `φ_n(x ∘ y) = Σ_{a+b+c=n} μ_a(φ_b x, φ_c y)` for every `n`. -/
theorem exists_trivialization (hH2 : ∀ ω : SymCochain R P, ω.IsCocycle → ω.IsCoboundary) :
    ∃ φ : ℕ → SymEndo R P, μ.PartialTriv 0 φ ∧ ∀ n, μ.IsMorAt φ n := by
  have hstab := μ.build_stable hH2
  refine ⟨fun k => (μ.build hH2 k).1 k, ⟨(μ.build hH2 0).2.1,
    fun k hk => (μ.build hH2 k).2.2.1 k hk, fun n hn => ?_⟩, fun n => ?_⟩
  · obtain rfl : n = 0 := by omega
    exact μ.isMorAt_zero _ (μ.build hH2 0).2.1
  · exact μ.isMorAt_congr (fun k hk => hstab n k hk) ((μ.build hH2 n).2.2.2 n le_rfl)

/-! ### The trivialization as an isomorphism of operads -/

omit μ in
lemma antidiagonal_ne_zero {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ antidiagonal (n + 1)) :
    p.1 ≠ 0 ∨ p.2 ≠ 0 := by
  have := Finset.mem_antidiagonal.mp hp
  omega

variable (R P) in
/-- **The trivial formal deformation**: `x ⋆ y = x ∘ y`. -/
def trivial : FormalDeformation R P where
  μ k := if k = 0 then fun _ _ _ _ _ _ i => SymOperad.comp (R := R) i else SymCochain.zero
  μ_zero := by
    intro A B _ _ _ _ i x y
    simp
  map_comp := by
    intro k A A' B B' _ _ _ _ _ _ _ _ σ τ i x y
    split_ifs
    · exact SymOperad.map_comp (R := R) σ τ i x y
    · simp
  comp_one := by
    intro k hk A _ _ i x
    simp [hk]
  one_comp := by
    intro k hk B _ _ y
    simp [hk]
  assoc_seq := by
    intro n A B D _ _ _ _ _ _ i j x y z
    rcases n with _ | n
    · simp [SymOperad.comp_assoc_seq]
    · rw [Finset.sum_eq_zero, Finset.sum_eq_zero, map_zero]
      · intro p hp
        rcases antidiagonal_ne_zero hp with h | h <;> simp [h]
      · intro p hp
        rcases antidiagonal_ne_zero hp with h | h <;> simp [h]
  assoc_par := by
    intro n A B D _ _ _ _ _ _ i k hik x y z
    rcases n with _ | n
    · simp [SymOperad.comp_assoc_par]
    · rw [Finset.sum_eq_zero, Finset.sum_eq_zero, map_zero]
      · intro p hp
        rcases antidiagonal_ne_zero hp with h | h <;> simp [h]
      · intro p hp
        rcases antidiagonal_ne_zero hp with h | h <;> simp [h]

omit μ in
lemma trivial_scomp (i : A) (x : (trivial R P).Series A) (y : (trivial R P).Series B) (m : ℕ) :
    (trivial R P).scomp i x y m
      = ∑ q ∈ antidiagonal m, SymOperad.comp (R := R) i (x q.1) (y q.2) := by
  rw [scomp_apply, sum_antidiagonal_fst_zero m
    (fun a b => ∑ q ∈ antidiagonal b, (trivial R P).μ a i (x q.1) (y q.2))
    (fun a b ha => Finset.sum_eq_zero fun q _ => by simp [trivial, ha])]
  simp [trivial]

omit μ in
/-- Regrouping the six indices of `Φ(x ∘ y)` and `Φx ⋆ Φy`. -/
lemma sum_antidiagonal_reidx_hom {β : Type*} [AddCommMonoid β] (m : ℕ)
    (G : ℕ → ℕ → ℕ → ℕ → ℕ → β) :
    ∑ p ∈ antidiagonal m, ∑ q ∈ antidiagonal p.2, ∑ r ∈ antidiagonal p.1,
      ∑ s ∈ antidiagonal r.2, G r.1 s.1 q.1 s.2 q.2
    = ∑ p ∈ antidiagonal m, ∑ q ∈ antidiagonal p.2, ∑ s ∈ antidiagonal q.2,
      ∑ r ∈ antidiagonal q.1, G p.1 r.1 r.2 s.1 s.2 := by
  simp only [Finset.sum_sigma']
  apply Finset.sum_nbij'
    (fun ⟨⟨_, _⟩, ⟨u, v⟩, ⟨c, _⟩, ⟨e, f⟩⟩ => ⟨⟨c, e + u + f + v⟩, ⟨e + u, f + v⟩, ⟨f, v⟩, ⟨e, u⟩⟩)
    (fun ⟨⟨c, _⟩, ⟨_, _⟩, ⟨f, v⟩, ⟨e, u⟩⟩ => ⟨⟨c + e + f, u + v⟩, ⟨u, v⟩, ⟨c, e + f⟩, ⟨e, f⟩⟩)
  all_goals aesop (add simp [Finset.mem_sigma, Finset.mem_antidiagonal]) (add safe (by omega))

/-- The series map `x ↦ Σ_k t^k φ_k(x)`. -/
def trivHomApp (φ : ℕ → SymEndo R P) (A : Type) [Fintype A] [DecidableEq A] :
    (trivial R P).Series A →ₗ[R] μ.Series A where
  toFun x m := ∑ p ∈ antidiagonal m, (φ p.1).app A (x p.2)
  map_add' x y := funext fun m => by
    rw [add_apply']
    simp only [add_apply', map_add, Finset.sum_add_distrib]
  map_smul' c x := funext fun m => by
    rw [RingHom.id_apply, smul_apply']
    simp only [smul_apply', map_smul, Finset.smul_sum]

lemma trivHomApp_apply (φ : ℕ → SymEndo R P) (x : (trivial R P).Series A) (m : ℕ) :
    μ.trivHomApp φ A x m = ∑ p ∈ antidiagonal m, (φ p.1).app A (x p.2) := rfl

/-- **A trivialization is a morphism of operads** `P[[t]] → P[[t]]_μ`. -/
def trivHom (φ : ℕ → SymEndo R P) (hφ : μ.PartialTriv 0 φ) (hmor : ∀ n, μ.IsMorAt φ n) :
    SymOperadHom R (trivial R P).Series μ.Series where
  app A _ _ := μ.trivHomApp φ A
  app_map e x := funext fun m => by
    show μ.trivHomApp φ _ ((trivial R P).smap e x) m = μ.smap e (μ.trivHomApp φ _ x) m
    simp only [trivHomApp_apply, smap_apply, map_sum, (φ _).app_map]
  app_one := funext fun m => by
    rw [trivHomApp_apply]
    show _ = μ.sone m
    rw [Finset.sum_eq_single (m, 0)]
    · show (φ m).app Unit ((trivial R P).sone 0) = if m = 0 then SymOperad.one R else 0
      rw [show (trivial R P).sone 0 = SymOperad.one R from if_pos rfl]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [hφ.1, if_pos rfl]
      · rw [hφ.2.1 m (by omega), if_neg (by omega)]
    · intro p hp hne
      have := Finset.mem_antidiagonal.mp hp
      have h2 : p.2 ≠ 0 := fun h => hne (Prod.ext (by simp; omega) h)
      show (φ p.1).app Unit ((trivial R P).sone p.2) = 0
      simp [sone, h2]
    · intro h
      exact absurd (Finset.mem_antidiagonal.mpr (by simp)) h
  app_comp i x y := funext fun m => by
    show μ.trivHomApp φ _ ((trivial R P).scomp i x y) m
      = μ.scomp i (μ.trivHomApp φ _ x) (μ.trivHomApp φ _ y) m
    have key : ∀ n {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
        (i : A) (x : P A) (y : P B), (φ n).app _ (SymOperad.comp (R := R) i x y)
          = ∑ p ∈ antidiagonal n, ∑ q ∈ antidiagonal p.2,
              μ.μ p.1 i ((φ q.1).app A x) ((φ q.2).app B y) := fun n => hmor n
    rw [trivHomApp_apply, scomp_apply]
    simp only [trivial_scomp, map_sum, key, trivHomApp_apply, LinearMap.sum_apply]
    exact sum_antidiagonal_reidx_hom m
      (fun c e u f v => μ.μ c i ((φ e).app _ (x u)) ((φ f).app _ (y v)))

/-- The coefficient `m` of `Φ x` is `x_m` plus terms in the lower coefficients of `x`. -/
lemma trivHomApp_eq (φ : ℕ → SymEndo R P) (hφ0 : ∀ (A : Type) [Fintype A] [DecidableEq A]
    (x : P A), (φ 0).app A x = x) (x : (trivial R P).Series A) (m : ℕ) :
    μ.trivHomApp φ A x m
      = x m + ∑ p ∈ (antidiagonal m).filter (fun p => p.1 ≠ 0), (φ p.1).app A (x p.2) := by
  rw [trivHomApp_apply, ← Finset.sum_filter_add_sum_filter_not (antidiagonal m) (fun p => p.1 ≠ 0),
    add_comm]
  congr 1
  rw [Finset.sum_eq_single (0, m)]
  · exact hφ0 A (x m)
  · intro p hp hne
    rw [Finset.mem_filter, Finset.mem_antidiagonal, not_not] at hp
    exact absurd (Prod.ext hp.2 (by simp; omega)) hne
  · intro h
    exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_antidiagonal.mpr (by simp), by simp⟩) h

/-- The preimage under `Φ`, coefficient by coefficient. -/
def pre (φ : ℕ → SymEndo R P) (y : μ.Series A) : ℕ → P A
  | m => y m - ∑ p ∈ (antidiagonal m).attach,
      if h : p.1.1 = 0 then 0 else (φ p.1.1).app A (pre φ y p.1.2)
termination_by m => m
decreasing_by
  have := Finset.mem_antidiagonal.mp p.2
  omega

/-- **A trivialization is an isomorphism of operads** `P[[t]] ≅ P[[t]]_μ`: its components are
bijective. -/
theorem trivHomApp_bijective (φ : ℕ → SymEndo R P) (hφ0 : ∀ (A : Type) [Fintype A]
    [DecidableEq A] (x : P A), (φ 0).app A x = x) (A : Type) [Fintype A] [DecidableEq A] :
    Function.Bijective (μ.trivHomApp φ A) := by
  have hsum : ∀ (x : ℕ → P A) (m : ℕ),
      ∑ p ∈ (antidiagonal m).filter (fun p => p.1 ≠ 0), (φ p.1).app A (x p.2)
        = ∑ p ∈ (antidiagonal m).attach,
          if h : p.1.1 = 0 then 0 else (φ p.1.1).app A (x p.1.2) := fun x m => by
    rw [Finset.sum_filter, ← Finset.sum_attach]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : p.1.1 = 0 <;> simp [h]
  constructor
  · refine (injective_iff_map_eq_zero _).mpr fun x hx => funext fun m => ?_
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      have := congrFun hx m
      rw [trivHomApp_eq μ φ hφ0, zero_apply'] at this
      rw [Finset.sum_eq_zero fun p hp => ?_, add_zero] at this
      · exact this
      · rw [Finset.mem_filter, Finset.mem_antidiagonal] at hp
        rw [ih p.2 (by omega), zero_apply', map_zero]
  · intro y
    refine ⟨fun m => μ.pre φ y m, funext fun m => ?_⟩
    rw [trivHomApp_eq μ φ hφ0, hsum, pre]
    abel

/-- **Rigidity, as an isomorphism**: if every two-cocycle of `P` is a coboundary, every formal
deformation of `P` is isomorphic to the trivial one by an isomorphism of operads
`P[[t]] → P[[t]]_μ` that is the identity modulo `t`. -/
theorem exists_iso_trivial (hH2 : ∀ ω : SymCochain R P, ω.IsCocycle → ω.IsCoboundary) :
    ∃ Φ : SymOperadHom R (trivial R P).Series μ.Series,
      (∀ (A : Type) [Fintype A] [DecidableEq A], Function.Bijective (Φ.app A)) ∧
        ∀ (A : Type) [Fintype A] [DecidableEq A] (x : (trivial R P).Series A),
          Φ.app A x 0 = x 0 := by
  obtain ⟨φ, hφ, hmor⟩ := μ.exists_trivialization hH2
  refine ⟨μ.trivHom φ hφ hmor, fun A _ _ => μ.trivHomApp_bijective φ hφ.1 A, fun A _ _ x => ?_⟩
  show μ.trivHomApp φ A x 0 = x 0
  rw [trivHomApp_apply, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
  exact hφ.1 A (x 0)

end FormalDeformation

end Operad
