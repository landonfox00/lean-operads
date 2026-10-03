/-
# The homotopy transfer theorem for dg algebras

Let `(V, ε)` be a super module with a dg algebra structure in the bar convention: an odd
differential `d` and an odd product `μ` with `d² = 0`, the Leibniz rule and associativity
(`HTT.DGA`, equivalently `AInf.IsAInf` of `AInf.dga`). A **retraction** (`HTT.Retract`) is an even
idempotent `e` commuting with `d` and an odd homotopy `h` with `h d + d h = e - 1`: the image of
`e` is a deformation retract of `V`.

**The homotopy transfer theorem** (Kadeishvili, Merkulov, Kontsevich–Soibelman;
`HTT.isAInf_transfer`): the operations
`b'₁ = e d e`, `b'ₙ = e ∘ λₙ` with `λₙ = ∑_{k + l = n} μ (fₖ, fₗ)`, `f₁ = e`, `fₙ = h ∘ λₙ`,
the sums over planar binary trees with the homotopy on the internal edges, form an A∞-structure.
They live on the image of `e`: for a retraction `ι π = e`, `π ι = 1` onto a complex `W`, they are
`π ∘ (…) ∘ ι^⊗`, the classical transferred structure on `W`.

The proof is the induction on the arity of Markl's argument: the family `f` satisfies the
equation of an ∞-morphism from `b'` to `(d, μ)`, `d ∘ f + λ = f ⋆ b'` (`HTT.morphism_eq`), which
follows from `d ∘ λ + λ ⋆ b' = 0` (`HTT.key_eq`) by the homotopy formula; that in turn follows
from the ∞-morphism equation in lower arities, the Leibniz rule (`HTT.comp_BIN`), the
associativity of `μ` (`HTT.BIN_assoc`), and the fact that inserting an operation into a binary
composite inserts it into one of the two factors (`HTT.tstar_BIN`). Then `b' ⋆ b' = e ∘ (d ∘ λ +
λ ⋆ b') = 0`. The side conditions `h e = e h = h h = 0` are not needed.
-/
import Operad.AInfinity

universe u v

namespace Operad

namespace HTT

open End AInf Finset

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

/-! ## Binary composites -/

omit [AddCommGroup V] in
lemma vec2_update_zero (x y z : V) : Function.update ![x, y] 0 z = ![z, y] := by
  ext i
  fin_cases i <;> simp

omit [AddCommGroup V] in
lemma vec2_update_one (x y z : V) : Function.update ![x, y] 1 z = ![x, z] := by
  ext i
  fin_cases i <;> simp

lemma mu_add_left (μ : End R V 2) (x x' y : V) : μ ![x + x', y] = μ ![x, y] + μ ![x', y] := by
  have := μ.map_update_add ![x, y] 0 x x'
  rwa [vec2_update_zero, vec2_update_zero, vec2_update_zero] at this

lemma mu_add_right (μ : End R V 2) (x y y' : V) : μ ![x, y + y'] = μ ![x, y] + μ ![x, y'] := by
  have := μ.map_update_add ![x, y] 1 y y'
  rwa [vec2_update_one, vec2_update_one, vec2_update_one] at this

lemma mu_smul_left (μ : End R V 2) (c : R) (x y : V) : μ ![c • x, y] = c • μ ![x, y] := by
  have := μ.map_update_smul ![x, y] 0 c x
  rwa [vec2_update_zero, vec2_update_zero] at this

lemma mu_smul_right (μ : End R V 2) (c : R) (x y : V) : μ ![x, c • y] = c • μ ![x, y] := by
  have := μ.map_update_smul ![x, y] 1 c y
  rwa [vec2_update_one, vec2_update_one] at this

/-- **The binary composite** `μ (A (x₁, …, xₐ), B (xₐ₊₁, …, xₐ₊ᵦ))`. -/
def bin (μ : End R V 2) {a b : ℕ} (A : End R V a) (B : End R V b) : End R V (a + b) where
  toFun v := μ ![A fun i => v (Fin.castAdd b i), B fun j => v (Fin.natAdd a j)]
  map_update_add' := by
    intro _ v k x y
    induction k using Fin.addCases with
    | left k =>
      have h1 : ∀ z, (fun i => Function.update v (Fin.castAdd b k) z (Fin.castAdd b i)) =
          Function.update (fun i => v (Fin.castAdd b i)) k z :=
        fun z => Function.update_comp_eq_of_injective v (Fin.castAdd_injective a b) k z
      have h2 : ∀ z, (fun j => Function.update v (Fin.castAdd b k) z (Fin.natAdd a j)) =
          fun j => v (Fin.natAdd a j) := fun z => funext fun j =>
        Function.update_of_ne (by simp [Fin.ext_iff]; omega) _ _
      simp only [h1, h2, MultilinearMap.map_update_add, mu_add_left]
    | right k =>
      have h1 : ∀ z, (fun j => Function.update v (Fin.natAdd a k) z (Fin.natAdd a j)) =
          Function.update (fun j => v (Fin.natAdd a j)) k z :=
        fun z => Function.update_comp_eq_of_injective v (Fin.natAdd_injective b a) k z
      have h2 : ∀ z, (fun i => Function.update v (Fin.natAdd a k) z (Fin.castAdd b i)) =
          fun i => v (Fin.castAdd b i) := fun z => funext fun i =>
        Function.update_of_ne (by simp [Fin.ext_iff]; omega) _ _
      simp only [h1, h2, MultilinearMap.map_update_add, mu_add_right]
  map_update_smul' := by
    intro _ v k c x
    induction k using Fin.addCases with
    | left k =>
      have h1 : ∀ z, (fun i => Function.update v (Fin.castAdd b k) z (Fin.castAdd b i)) =
          Function.update (fun i => v (Fin.castAdd b i)) k z :=
        fun z => Function.update_comp_eq_of_injective v (Fin.castAdd_injective a b) k z
      have h2 : ∀ z, (fun j => Function.update v (Fin.castAdd b k) z (Fin.natAdd a j)) =
          fun j => v (Fin.natAdd a j) := fun z => funext fun j =>
        Function.update_of_ne (by simp [Fin.ext_iff]; omega) _ _
      simp only [h1, h2, MultilinearMap.map_update_smul, mu_smul_left]
    | right k =>
      have h1 : ∀ z, (fun j => Function.update v (Fin.natAdd a k) z (Fin.natAdd a j)) =
          Function.update (fun j => v (Fin.natAdd a j)) k z :=
        fun z => Function.update_comp_eq_of_injective v (Fin.natAdd_injective b a) k z
      have h2 : ∀ z, (fun i => Function.update v (Fin.natAdd a k) z (Fin.castAdd b i)) =
          fun i => v (Fin.castAdd b i) := fun z => funext fun i =>
        Function.update_of_ne (by simp [Fin.ext_iff]; omega) _ _
      simp only [h1, h2, MultilinearMap.map_update_smul, mu_smul_right]

lemma bin_apply (μ : End R V 2) {a b : ℕ} (A : End R V a) (B : End R V b) (v : Fin (a + b) → V) :
    bin μ A B v = μ ![A fun i => v (Fin.castAdd b i), B fun j => v (Fin.natAdd a j)] := rfl

/-- **The binary composite is bilinear.** -/
def binL (μ : End R V 2) (a b : ℕ) : End R V a →ₗ[R] End R V b →ₗ[R] End R V (a + b) :=
  LinearMap.mk₂ R (bin μ)
    (fun A A' B => by ext v; simp only [bin_apply, MultilinearMap.add_apply, mu_add_left])
    (fun c A B => by ext v; simp only [bin_apply, MultilinearMap.smul_apply, mu_smul_left])
    (fun A B B' => by ext v; simp only [bin_apply, MultilinearMap.add_apply, mu_add_right])
    (fun c A B => by ext v; simp only [bin_apply, MultilinearMap.smul_apply, mu_smul_right])

lemma binL_apply (μ : End R V 2) {a b : ℕ} (A : End R V a) (B : End R V b) :
    binL μ a b A B = bin μ A B := rfl

lemma bin_sum_left (μ : End R V 2) {a b : ℕ} {ι : Type*} (s : Finset ι) (A : ι → End R V a)
    (B : End R V b) : bin μ (∑ x ∈ s, A x) B = ∑ x ∈ s, bin μ (A x) B := by
  rw [← binL_apply, map_sum, LinearMap.sum_apply]
  rfl

lemma bin_sum_right (μ : End R V 2) {a b : ℕ} {ι : Type*} (s : Finset ι) (A : End R V a)
    (B : ι → End R V b) : bin μ A (∑ x ∈ s, B x) = ∑ x ∈ s, bin μ A (B x) := by
  rw [← binL_apply, map_sum]
  rfl

lemma bin_sub_left (μ : End R V 2) {a b : ℕ} (A A' : End R V a) (B : End R V b) :
    bin μ (A - A') B = bin μ A B - bin μ A' B := by
  rw [← binL_apply, map_sub, LinearMap.sub_apply]
  rfl

lemma bin_sub_right (μ : End R V 2) {a b : ℕ} (A : End R V a) (B B' : End R V b) :
    bin μ A (B - B') = bin μ A B - bin μ A B' := by
  rw [← binL_apply, map_sub]
  rfl

@[simp] lemma bin_zero_left (μ : End R V 2) {a b : ℕ} (B : End R V b) :
    bin μ (0 : End R V a) B = 0 := by
  rw [← binL_apply, map_zero, LinearMap.zero_apply]

@[simp] lemma bin_zero_right (μ : End R V 2) {a b : ℕ} (A : End R V a) :
    bin μ A (0 : End R V b) = 0 := by
  rw [← binL_apply, map_zero]

lemma bin_acast_left (μ : End R V 2) {a a' b : ℕ} (A : End R V a) (B : End R V b) :
    bin μ (acast A : End R V a') B = acast (bin μ A B) := by
  by_cases h : a = a'
  · subst h
    simp
  · rw [acast, dif_neg h, bin_zero_left, acast, dif_neg (by omega)]

lemma bin_acast_right (μ : End R V 2) {a b b' : ℕ} (A : End R V a) (B : End R V b) :
    bin μ A (acast B : End R V b') = acast (bin μ A B) := by
  by_cases h : b = b'
  · subst h
    simp
  · rw [acast, dif_neg h, bin_zero_right, acast, dif_neg (by omega)]

/-! ## The Leibniz rule, associativity, and insertions into a binary composite -/

variable (ε : V →ₗ[R] V)

/-- **The Leibniz rule** for a binary composite. -/
lemma comp_bin (d : V →ₗ[R] V) (μ : End R V 2)
    (hL : ∀ x y, d (μ ![x, y]) + μ ![d x, y] + μ ![ε x, d y] = 0) {a b : ℕ}
    (A : End R V a) (B : End R V b) :
    d.compMultilinearMap (bin μ A B) =
      -bin μ (d.compMultilinearMap A) B -
        bin μ (ε.compMultilinearMap A) (d.compMultilinearMap B) := by
  ext v
  simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.sub_apply,
    MultilinearMap.neg_apply, bin_apply]
  linear_combination (norm := module) hL (A _) (B _)

/-- **Associativity** for binary composites. -/
lemma bin_assoc (μ : End R V 2) (hA : ∀ x y z, μ ![μ ![x, y], z] + μ ![ε x, μ ![y, z]] = 0)
    {a b c : ℕ} (A : End R V a) (B : End R V b) (C : End R V c) :
    bin μ (bin μ A B) C = -reindex R (End R V) (add_assoc a b c).symm
      (bin μ (ε.compMultilinearMap A) (bin μ B C)) := by
  ext v
  simp only [bin_apply, MultilinearMap.neg_apply, reindex_apply,
    LinearMap.compMultilinearMap_apply]
  have e1 : (fun i => v (Fin.cast (add_assoc a b c).symm (Fin.castAdd (b + c) i))) =
      fun i => v (Fin.castAdd c (Fin.castAdd b i)) := funext fun i => congrArg v (Fin.ext rfl)
  have e2 : (fun j => v (Fin.cast (add_assoc a b c).symm (Fin.natAdd a (Fin.castAdd c j)))) =
      fun j => v (Fin.castAdd c (Fin.natAdd a j)) := funext fun j => congrArg v (Fin.ext rfl)
  have e3 : (fun k => v (Fin.cast (add_assoc a b c).symm (Fin.natAdd a (Fin.natAdd b k)))) =
      fun k => v (Fin.natAdd (a + b) k) :=
    funext fun k => congrArg v (Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd]; omega))
  rw [e1, e2, e3]
  linear_combination (norm := module) hA _ _ _

/-- **Inserting into the left factor** of a binary composite. -/
lemma kcompFin_bin_left (μ : End R V 2) {j b l : ℕ} (A : End R V (j + 1)) (B : End R V b)
    (γ : End R V l) (i : Fin (j + 1)) :
    kcompFin ε 1 (Fin.castAdd b i) (bin μ A B) γ =
      reindex R (End R V) (by omega) (bin μ (kcompFin ε 1 i A γ) B) := by
  ext v
  simp only [kcompFin, compFin_apply, twist_apply, bin_apply, reindex_apply]
  congr 1
  refine congrArg₂ (fun x y => ![x, y]) (congrArg A (funext fun s => ?_))
    (congrArg B (funext fun s => ?_))
  · have hs := s.isLt
    have hi := i.isLt
    rcases lt_trichotomy (s : ℕ) i with h | h | h
    · rw [cfTuple_of_lt (Fin.castAdd b i) γ v (Fin.castAdd b s) h, cfTuple_of_lt i γ _ s h]
      rfl
    · rw [cfTuple_of_eq (Fin.castAdd b i) γ v (Fin.castAdd b s) h, cfTuple_of_eq i γ _ s h]
      rfl
    · rw [cfTuple_of_gt (Fin.castAdd b i) γ v (Fin.castAdd b s) h, cfTuple_of_gt i γ _ s h]
      rfl
  · have hs := s.isLt
    have hi := i.isLt
    rw [cfTuple_of_gt _ _ _ _ (by simp only [Fin.val_castAdd, Fin.val_natAdd]; omega),
      twistFn_of_ge _ _ _ _ (by simp only [Fin.val_castAdd, Fin.val_natAdd]; omega),
      LinearMap.id_apply]
    exact congrArg v (Fin.ext (by simp only [Fin.val_natAdd, Fin.val_cast]; omega))

/-- **Inserting into the right factor** of a binary composite, across an even left factor. -/
lemma kcompFin_bin_right (μ : End R V 2) {a k l : ℕ} (A : End R V a) (hA : IsHomog ε 0 A)
    (B : End R V (k + 1)) (γ : End R V l) (i : Fin (k + 1)) :
    kcompFin ε 1 (Fin.natAdd a i) (bin μ A B) γ =
      reindex R (End R V) (by omega) (bin μ (ε.compMultilinearMap A) (kcompFin ε 1 i B γ)) := by
  ext v
  simp only [kcompFin, compFin_apply, twist_apply, bin_apply, reindex_apply,
    LinearMap.compMultilinearMap_apply]
  congr 1
  have hεA : A (fun s => twistFn ε 1 (↑(Fin.natAdd a i)) (Fin.castAdd (k + 1) s)
      (cfTuple (Fin.natAdd a i) γ v (Fin.castAdd (k + 1) s))) =
      ε (A fun s => v (Fin.cast (by omega) (Fin.castAdd (k + 1 - 1 + l) s))) := by
    have key := hA fun s => v (Fin.cast (by omega) (Fin.castAdd (k + 1 - 1 + l) s))
    rw [pow_zero, one_smul] at key
    rw [← key]
    congr 1
    funext s
    have hs := s.isLt
    rw [twistFn_of_lt _ _ _ _ (by simp only [Fin.val_castAdd, Fin.val_natAdd]; omega),
      cfTuple_of_lt _ _ _ _ (by simp only [Fin.val_castAdd, Fin.val_natAdd]; omega), pow_one]
    rfl
  rw [hεA]
  refine congrArg (fun y => ![_, y]) (congrArg B (funext fun s => ?_))
  have hs := s.isLt
  have hi := i.isLt
  rcases lt_trichotomy (s : ℕ) i with h | h | h
  · rw [cfTuple_of_lt _ _ _ _ (by simp only [Fin.val_natAdd]; omega), cfTuple_of_lt _ _ _ _ h,
      twistFn_of_lt _ _ _ _ (by simp only [Fin.val_natAdd]; omega), twistFn_of_lt _ _ _ _ h]
    exact congrArg _ (congrArg v (Fin.ext rfl))
  · rw [cfTuple_of_eq _ _ _ _ (by simp only [Fin.val_natAdd]; omega), cfTuple_of_eq _ _ _ _ h,
      twistFn_of_ge _ _ _ _ (by simp only [Fin.val_natAdd]; omega), twistFn_of_ge _ _ _ _ h.ge]
    simp only [LinearMap.id_apply]
    congr 1
    funext t
    exact congrArg v (Fin.ext (by simp only [Fin.val_natAdd, Fin.val_cast]; omega))
  · rw [cfTuple_of_gt _ _ _ _ (by simp only [Fin.val_natAdd]; omega), cfTuple_of_gt _ _ _ _ h,
      twistFn_of_ge _ _ _ _ (by simp only [Fin.val_natAdd]; omega),
      twistFn_of_ge _ _ _ _ h.le]
    simp only [LinearMap.id_apply]
    exact congrArg v (Fin.ext (by simp only [Fin.val_natAdd, Fin.val_cast]; omega))

/-- **Inserting into a binary composite** inserts into one of the two factors. -/
lemma kstar_bin (μ : End R V 2) {j k l : ℕ} (A : End R V (j + 1)) (hA : IsHomog ε 0 A)
    (B : End R V (k + 1)) (γ : End R V (l + 1)) :
    kstar ε 1 (j := j + 1 + k) (bin (a := j + 1) (b := k + 1) μ A B) γ =
      acast (bin μ (kstar ε 1 A γ) B) +
      acast (bin μ (ε.compMultilinearMap A) (kstar ε 1 B γ)) := by
  show ∑ i : Fin ((j + 1) + (k + 1)), kcompFin ε 1 i (bin μ A B) γ = _
  rw [Fin.sum_univ_add]
  simp only [kcompFin_bin_left, kcompFin_bin_right ε μ A hA, ← map_sum, kstar,
    ← bin_sum_left, ← bin_sum_right,
    acast_of_eq (by omega : j + l + 1 + (k + 1) = j + 1 + k + l + 1),
    acast_of_eq (by omega : j + 1 + (k + l + 1) = j + 1 + k + l + 1)]
  rfl

/-! ## Reindexing double sums -/

section Sums

variable {M : Type*} [AddCommMonoid M]

lemma sum_T1 (m : ℕ) (F : ℕ → ℕ → ℕ → M) :
    ∑ j ∈ range (m + 1), ∑ k ∈ range j, F k (j - 1 - k) (m - j) =
      ∑ p ∈ range m, ∑ k ∈ range (p + 1), F k (m - 1 - p) (p - k) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => ⟨m - x.1 + x.2, x.2⟩) (fun y => ⟨m - y.1 + y.2, y.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨j, k⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
    omega
  · rintro ⟨p, k⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_range] at hy ⊢
    omega
  · rintro ⟨j, k⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    simp only [Sigma.mk.injEq, heq_iff_eq, and_true]
    omega
  · rintro ⟨p, k⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_range] at hy
    simp only [Sigma.mk.injEq, heq_iff_eq, and_true]
    omega
  · rintro ⟨j, k⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    dsimp only
    rw [show m - 1 - (m - j + k) = j - 1 - k by omega, show m - j + k - k = m - j by omega]

lemma sum_T2 (m : ℕ) (G : ℕ → ℕ → ℕ → M) :
    ∑ j ∈ range (m + 1), ∑ k ∈ range j, G k (j - 1 - k) (m - j) =
      ∑ p ∈ range m, ∑ l ∈ range (m - 1 - p + 1), G p l (m - 1 - p - l) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => ⟨x.2, x.1 - 1 - x.2⟩) (fun y => ⟨y.1 + y.2 + 1, y.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨j, k⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
    omega
  · rintro ⟨p, l⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_range] at hy ⊢
    omega
  · rintro ⟨j, k⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    simp only [Sigma.mk.injEq, heq_iff_eq, and_true]
    omega
  · rintro ⟨p, l⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_range] at hy
    simp only [Sigma.mk.injEq, heq_iff_eq, true_and]
    omega
  · rintro ⟨j, k⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    dsimp only
    rw [show m - 1 - k - (j - 1 - k) = m - j by omega]

lemma sum_T3 (m : ℕ) (F : ℕ → ℕ → ℕ → M) :
    ∑ p ∈ range m, ∑ k ∈ range p, F k (p - 1 - k) (m - 1 - p) =
      ∑ k ∈ range m, ∑ l ∈ range (m - 1 - k), F k l (m - 1 - k - 1 - l) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => ⟨x.2, x.1 - 1 - x.2⟩) (fun y => ⟨y.1 + y.2 + 1, y.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨p, k⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
    omega
  · rintro ⟨k, l⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_range] at hy ⊢
    omega
  · rintro ⟨p, k⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    simp only [Sigma.mk.injEq, heq_iff_eq, and_true]
    omega
  · rintro ⟨k, l⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_range] at hy
    simp only [Sigma.mk.injEq, heq_iff_eq, true_and]
    omega
  · rintro ⟨p, k⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    dsimp only
    rw [show m - 1 - k - 1 - (p - 1 - k) = m - 1 - p by omega]

end Sums

/-! ## Binary products of families -/

/-- **The post-composition** of a family with a linear map. -/
def fcomp (f : V →ₗ[R] V) (X : Fam R V) : Fam R V := fun n => f.compMultilinearMap (X n)

lemma comp_sum (f : V →ₗ[R] V) {n : ℕ} {ι : Type*} (s : Finset ι) (x : ι → End R V n) :
    f.compMultilinearMap (∑ i ∈ s, x i) = ∑ i ∈ s, f.compMultilinearMap (x i) := by
  ext v
  simp [map_sum]

lemma comp_acast (f : V →ₗ[R] V) {a b : ℕ} (x : End R V a) :
    f.compMultilinearMap (acast x : End R V b) = acast (f.compMultilinearMap x) := by
  by_cases h : a = b
  · subst h
    simp
  · rw [acast, dif_neg h, acast, dif_neg h]
    ext v
    simp

/-- **The binary product of two families**: `(X ⊙ Y)ₙ = ∑_{k + l + 1 = n} μ (Xₖ, Yₗ)`. -/
def BIN (μ : End R V 2) (X Y : Fam R V) : Fam R V := fun n =>
  ∑ k ∈ range n, acast (bin μ (X k) (Y (n - 1 - k)))

lemma BIN_apply (μ : End R V 2) (X Y : Fam R V) (n : ℕ) :
    BIN μ X Y n = ∑ k ∈ range n, acast (bin μ (X k) (Y (n - 1 - k))) := rfl

@[simp] lemma BIN_zero (μ : End R V 2) (X Y : Fam R V) : BIN μ X Y 0 = 0 := by
  simp [BIN_apply]

/-- **Locality**: the product in arity `n + 1` only involves the factors of smaller arities. -/
lemma BIN_congr (μ : End R V 2) {X X' Y Y' : Fam R V} {n : ℕ} (hX : ∀ k < n, X k = X' k)
    (hY : ∀ k < n, Y k = Y' k) : BIN μ X Y n = BIN μ X' Y' n := by
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [hX k hk, hY (n - 1 - k) (by omega)]

lemma BIN_sub_left (μ : End R V 2) (X X' Y : Fam R V) :
    BIN μ (X - X') Y = BIN μ X Y - BIN μ X' Y := by
  funext n
  simp only [BIN_apply, Pi.sub_apply, bin_sub_left, acast_sub, Finset.sum_sub_distrib]

lemma BIN_sub_right (μ : End R V 2) (X Y Y' : Fam R V) :
    BIN μ X (Y - Y') = BIN μ X Y - BIN μ X Y' := by
  funext n
  simp only [BIN_apply, Pi.sub_apply, bin_sub_right, acast_sub, Finset.sum_sub_distrib]

/-- **The Leibniz rule** for products of families. -/
lemma comp_BIN (d : V →ₗ[R] V) (μ : End R V 2)
    (hL : ∀ x y, d (μ ![x, y]) + μ ![d x, y] + μ ![ε x, d y] = 0) (X Y : Fam R V) :
    fcomp d (BIN μ X Y) = -BIN μ (fcomp d X) Y - BIN μ (fcomp ε X) (fcomp d Y) := by
  funext n
  simp only [fcomp, BIN_apply, Pi.sub_apply, Pi.neg_apply, comp_sum, comp_acast,
    comp_bin ε d μ hL, acast_sub, acast_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib]

/-- **Associativity** for products of families. -/
lemma BIN_assoc (μ : End R V 2) (hA : ∀ x y z, μ ![μ ![x, y], z] + μ ![ε x, μ ![y, z]] = 0)
    (X Y Z : Fam R V) : BIN μ (BIN μ X Y) Z + BIN μ (fcomp ε X) (BIN μ Y Z) = 0 := by
  funext m
  simp only [Pi.add_apply, Pi.zero_apply, BIN_apply, bin_sum_left, bin_sum_right,
    bin_acast_left, bin_acast_right, acast_sum, fcomp]
  have h1 : ∑ p ∈ range m, ∑ k ∈ range p,
      (acast (acast (bin μ (bin μ (X k) (Y (p - 1 - k))) (Z (m - 1 - p))) :
        End R V (p + 1 + (m - 1 - p + 1))) : End R V (m + 1)) =
      ∑ p ∈ range m, ∑ k ∈ range p, -(acast (bin μ (ε.compMultilinearMap (X k))
        (bin μ (Y (p - 1 - k)) (Z (m - 1 - p)))) : End R V (m + 1)) := by
    refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hp hk
    rw [acast_acast (by omega), bin_assoc ε μ hA, acast_neg, acast_reindex]
  have h2 : ∑ k ∈ range m, ∑ l ∈ range (m - 1 - k),
      (acast (acast (bin μ (ε.compMultilinearMap (X k)) (bin μ (Y l) (Z (m - 1 - k - 1 - l)))) :
        End R V (k + 1 + (m - 1 - k + 1))) : End R V (m + 1)) =
      ∑ k ∈ range m, ∑ l ∈ range (m - 1 - k),
        (acast (bin μ (ε.compMultilinearMap (X k)) (bin μ (Y l) (Z (m - 1 - k - 1 - l)))) :
          End R V (m + 1)) := by
    refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.mem_range] at hk hl
    rw [acast_acast (by omega)]
  rw [h1, h2, sum_T3 m (fun k l r => -(acast (bin μ (ε.compMultilinearMap (X k))
    (bin μ (Y l) (Z r))) : End R V (m + 1)))]
  simp only [Finset.sum_neg_distrib, neg_add_cancel]

lemma kstar_acast_bin (μ : End R V 2) {k l j r : ℕ} (hj : k + 1 + l = j) (A : End R V (k + 1))
    (hA : IsHomog ε 0 A) (B : End R V (l + 1)) (γ : End R V (r + 1)) :
    kstar ε 1 (acast (bin μ A B) : End R V (j + 1)) γ =
      acast (bin μ (kstar ε 1 A γ) B) + acast (bin μ (ε.compMultilinearMap A) (kstar ε 1 B γ)) := by
  subst hj
  rw [acast_of_eq (rfl : k + 1 + (l + 1) = k + 1 + l + 1), reindex_rfl]
  exact kstar_bin ε μ A hA B γ

/-- **Inserting into a product of families** inserts into one of the factors. -/
lemma tstar_BIN (μ : End R V 2) (X Y c : Fam R V) (hX : ∀ n, IsHomog ε 0 (X n)) :
    tstar ε 1 (BIN μ X Y) c = BIN μ (tstar ε 1 X c) Y + BIN μ (fcomp ε X) (tstar ε 1 Y c) := by
  funext m
  simp only [Pi.add_apply, tstar_apply, BIN_apply, fcomp, kstar_sum_left, acast_sum,
    bin_sum_left, bin_sum_right, bin_acast_left, bin_acast_right]
  have hL : ∀ j ∈ range (m + 1), ∑ k ∈ range j,
      (acast (kstar ε 1 (acast (bin μ (X k) (Y (j - 1 - k))) : End R V (j + 1)) (c (m - j))) :
        End R V (m + 1)) =
      ∑ k ∈ range j, ((acast (bin μ (kstar ε 1 (X k) (c (m - j))) (Y (j - 1 - k))) :
          End R V (m + 1)) +
        acast (bin μ (ε.compMultilinearMap (X k)) (kstar ε 1 (Y (j - 1 - k)) (c (m - j))))) := by
    intro j hj
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hj hk
    rw [kstar_acast_bin ε μ (by omega) (X k) (hX k), acast_add, acast_acast (by omega),
      acast_acast (by omega)]
  rw [Finset.sum_congr rfl hL]
  simp only [Finset.sum_add_distrib]
  rw [sum_T1 m (fun k l r => (acast (bin μ (kstar ε 1 (X k) (c r)) (Y l)) : End R V (m + 1))),
    sum_T2 m (fun k l r => (acast (bin μ (ε.compMultilinearMap (X k)) (kstar ε 1 (Y l) (c r))) :
      End R V (m + 1)))]
  congr 1
  · refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hp hk
    rw [acast_acast (by omega)]
  · refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.mem_range] at hp hl
    rw [acast_acast (by omega)]

/-! ## Operations of arity one, parities -/

/-- **The operation of arity one** of a linear map. -/
def op1 (f : V →ₗ[R] V) : End R V 1 := MultilinearMap.ofSubsingleton R V V 0 f

omit ε in
lemma op1_apply (f : V →ₗ[R] V) (v : Fin 1 → V) : op1 f v = f (v 0) := rfl

/-- **Inserting into an operation of arity one** is composing. -/
lemma kstar_op1 (q : ℕ) (f : V →ₗ[R] V) {k : ℕ} (β : End R V (k + 1)) :
    kstar ε q (op1 f) β = acast (f.compMultilinearMap β) := by
  rw [acast_of_eq (by omega)]
  ext v
  rw [kstar, Fin.sum_univ_one, kcompFin, compFin_apply, twist_apply, op1_apply,
    twistFn_of_ge _ _ _ _ (le_refl _), LinearMap.id_apply,
    cfTuple_of_eq _ _ _ _ rfl, reindex_apply, LinearMap.compMultilinearMap_apply]
  congr 2
  funext t
  exact congrArg v (Fin.ext (by simp))

lemma kcompFin_comp (q : ℕ) (f : V →ₗ[R] V) {m n : ℕ} (i : Fin m) (α : End R V m)
    (β : End R V n) :
    kcompFin ε q i (f.compMultilinearMap α) β = f.compMultilinearMap (kcompFin ε q i α β) := by
  ext v
  simp only [kcompFin, compFin_apply, twist_apply, LinearMap.compMultilinearMap_apply]

/-- **Inserting into a post-composite** is post-composing the insertion. -/
lemma kstar_comp (q : ℕ) (f : V →ₗ[R] V) {j k : ℕ} (α : End R V (j + 1)) (β : End R V (k + 1)) :
    kstar ε q (f.compMultilinearMap α) β = f.compMultilinearMap (kstar ε q α β) := by
  unfold kstar
  erw [comp_sum]
  exact Finset.sum_congr rfl fun i _ => kcompFin_comp ε q f i α β

lemma isHomog_sum {q n : ℕ} {ι : Type*} (s : Finset ι) {x : ι → End R V n}
    (h : ∀ i ∈ s, IsHomog ε q (x i)) : IsHomog ε q (∑ i ∈ s, x i) := by
  intro v
  simp only [MultilinearMap.sum_apply, map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i hi => h i hi v

lemma isHomog_acast {q a b : ℕ} {x : End R V a} (h : IsHomog ε q x) :
    IsHomog ε q (acast x : End R V b) := by
  by_cases hab : a = b
  · subst hab
    simpa using h
  · rw [acast, dif_neg hab]
    intro v
    simp

lemma isHomog_bin {μ : End R V 2} (hμ : IsHomog ε 1 μ) {a b : ℕ} {A : End R V a}
    {B : End R V b} (hA : IsHomog ε 0 A) (hB : IsHomog ε 0 B) : IsHomog ε 1 (bin μ A B) := by
  intro v
  rw [bin_apply, bin_apply]
  have h1 := hA fun i => v (Fin.castAdd b i)
  have h2 := hB fun j => v (Fin.natAdd a j)
  rw [pow_zero, one_smul] at h1 h2
  rw [h1, h2, ← hμ ![A fun i => v (Fin.castAdd b i), B fun j => v (Fin.natAdd a j)]]
  congr 1
  funext t
  fin_cases t <;> rfl

lemma isHomog_BIN {μ : End R V 2} (hμ : IsHomog ε 1 μ) {X Y : Fam R V} {n : ℕ}
    (hX : ∀ k < n, IsHomog ε 0 (X k)) (hY : ∀ k < n, IsHomog ε 0 (Y k)) :
    IsHomog ε 1 (BIN μ X Y n) :=
  isHomog_sum ε _ fun k hk => by
    rw [Finset.mem_range] at hk
    exact isHomog_acast ε (isHomog_bin ε hμ (hX k hk) (hY _ (by omega)))

lemma isHomog_comp {p q r : ℕ} {f : V →ₗ[R] V} (hf : ∀ x, f (ε x) = (-1 : R) ^ p • ε (f x))
    {n : ℕ} {α : End R V n} (hα : IsHomog ε q α) (hr : (-1 : R) ^ (q + p) = (-1) ^ r) :
    IsHomog ε r (f.compMultilinearMap α) := by
  intro v
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply, hα v, map_smul,
    hf, smul_smul, ← pow_add, hr]

/-! ## The transfer -/

/-- **A dg algebra** on a super module, in the bar convention: an odd differential and an odd
product with `d² = 0`, the Leibniz rule and associativity. -/
structure DGA (d : V →ₗ[R] V) (μ : End R V 2) : Prop where
  d_odd : ∀ x, d (ε x) = -ε (d x)
  μ_odd : IsHomog ε 1 μ
  dd : ∀ x, d (d x) = 0
  leibniz : ∀ x y, d (μ ![x, y]) + μ ![d x, y] + μ ![ε x, d y] = 0
  assoc : ∀ x y z, μ ![μ ![x, y], z] + μ ![ε x, μ ![y, z]] = 0

/-- **A retraction** of a complex onto the image of an even idempotent `e` commuting with the
differential, by an odd homotopy `h` with `h d + d h = e - 1`. -/
structure Retract (d e h : V →ₗ[R] V) : Prop where
  e_even : ∀ x, e (ε x) = ε (e x)
  h_odd : ∀ x, h (ε x) = -ε (h x)
  ee : ∀ x, e (e x) = e x
  de : ∀ x, d (e x) = e (d x)
  homotopy : ∀ x, h (d x) + d (h x) = e x - x

variable (μ : End R V 2) (e h : V →ₗ[R] V)

/-- **The trees of the transfer**: `f₀ = e`, `fₙ₊₁ = h ∘ ∑_{k + l = n} μ (fₖ, fₗ)`, the sums over
the planar binary trees with `e` on the leaves and `h` on the edges. -/
noncomputable def tf : (n : ℕ) → End R V (n + 1)
  | 0 => op1 e
  | n + 1 => h.compMultilinearMap
      (∑ k ∈ (range (n + 1)).attach, acast (bin μ (tf k) (tf (n - k))))
termination_by n => n
decreasing_by
  all_goals have := Finset.mem_range.1 k.2
  all_goals omega

omit ε in
lemma tf_zero : tf μ e h 0 = op1 e := by
  rw [tf]

omit ε in
lemma tf_succ (n : ℕ) :
    tf μ e h (n + 1) = h.compMultilinearMap (BIN μ (tf μ e h) (tf μ e h) (n + 1)) := by
  rw [tf, BIN_apply, Finset.sum_attach (range (n + 1))
    (fun k => (acast (bin μ (tf μ e h k) (tf μ e h (n - k))) : End R V (n + 1 + 1)))]
  rfl

/-- **The transferred structure**: `b'₀ = e d e` and `b'ₙ = e ∘ λₙ`, with
`λ = μ (f, f)` the products of the trees. -/
noncomputable def transfer (d : V →ₗ[R] V) : Fam R V
  | 0 => op1 (e ∘ₗ d ∘ₗ e)
  | n + 1 => e.compMultilinearMap (BIN μ (tf μ e h) (tf μ e h) (n + 1))

lemma tstar_succ (q : ℕ) (F c : Fam R V) (m : ℕ) :
    tstar ε q F c (m + 1) = (acast (kstar ε q (F 0) (c (m + 1))) : End R V (m + 1 + 1)) +
      ∑ j ∈ range (m + 1), (acast (kstar ε q (F (j + 1)) (c (m - j))) : End R V (m + 1 + 1)) := by
  rw [tstar_apply, Finset.sum_range_succ', Nat.sub_zero]
  rw [add_comm (∑ j ∈ range (m + 1), _)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show m + 1 - (j + 1) = m - j by omega]

/-! ## The transfer theorem -/

section Theorem

variable {ε μ e h} {d : V →ₗ[R] V} (hd : DGA ε d μ) (hr : Retract ε d e h)

include hd hr in
/-- **The trees are even.** -/
lemma tf_even (n : ℕ) : IsHomog ε 0 (tf μ e h n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases n with _ | n
  · rw [tf_zero]
    intro v
    rw [op1_apply, op1_apply, hr.e_even, pow_zero, one_smul]
  · rw [tf_succ]
    exact isHomog_comp ε (p := 1) (q := 1) (fun x => by rw [hr.h_odd, pow_one, neg_one_smul])
      (isHomog_BIN ε hd.μ_odd (fun k hk => ih k hk) (fun k hk => ih k hk)) (by norm_num)

include hd hr in
/-- **The key equation** in arity `n + 1`, from the ∞-morphism equation in lower arities. -/
lemma key_of_morph {n : ℕ}
    (hM : ∀ k < n, fcomp d (tf μ e h) k + BIN μ (tf μ e h) (tf μ e h) k =
      tstar ε 1 (tf μ e h) (transfer μ e h d) k) :
    fcomp d (BIN μ (tf μ e h) (tf μ e h)) n +
      tstar ε 1 (BIN μ (tf μ e h) (tf μ e h)) (transfer μ e h d) n = 0 := by
  set G := tf μ e h
  set b' := transfer μ e h d
  have hG : ∀ k < n, fcomp d G k = (tstar ε 1 G b' - BIN μ G G) k := fun k hk => by
    rw [Pi.sub_apply, ← hM k hk]
    abel
  have h1 := congrFun (comp_BIN ε d μ hd.leibniz G G) n
  simp only [Pi.sub_apply, Pi.neg_apply] at h1
  rw [BIN_congr μ (X' := tstar ε 1 G b' - BIN μ G G) (Y' := G) hG (fun _ _ => rfl),
    BIN_congr μ (X' := fcomp ε G) (Y' := tstar ε 1 G b' - BIN μ G G) (fun _ _ => rfl) hG,
    BIN_sub_left, BIN_sub_right] at h1
  simp only [Pi.sub_apply] at h1
  have h2 := congrFun (tstar_BIN ε μ G G b' (tf_even hd hr)) n
  have h3 := congrFun (BIN_assoc ε μ hd.assoc G G G) n
  simp only [Pi.add_apply, Pi.zero_apply] at h2 h3
  rw [h1, h2]
  linear_combination (norm := module) h3

include hr in
/-- **The ∞-morphism equation** in arity `n + 1`, from the key equation. -/
lemma morph_of_key {n : ℕ}
    (hK : fcomp d (BIN μ (tf μ e h) (tf μ e h)) n +
      tstar ε 1 (BIN μ (tf μ e h) (tf μ e h)) (transfer μ e h d) n = 0) :
    fcomp d (tf μ e h) n + BIN μ (tf μ e h) (tf μ e h) n =
      tstar ε 1 (tf μ e h) (transfer μ e h d) n := by
  rcases n with _ | m
  · rw [BIN_zero, add_zero, tstar_apply, Finset.sum_range_one, Nat.sub_zero,
      show fcomp d (tf μ e h) 0 = d.compMultilinearMap (tf μ e h 0) from rfl, tf_zero]
    show d.compMultilinearMap (op1 e) = acast (kstar ε 1 (op1 e) (op1 (e ∘ₗ d ∘ₗ e)))
    rw [kstar_op1, acast_acast (by omega), acast_self]
    ext v
    change d (e (v 0)) = e ((e ∘ₗ d ∘ₗ e) (v 0))
    simp only [LinearMap.comp_apply, hr.ee, hr.de]
  · rw [tstar_succ] at hK ⊢
    rw [BIN_zero, kstar_zero_left, acast_zero, zero_add] at hK
    have hsum : ∑ j ∈ range (m + 1), (acast (kstar ε 1 (tf μ e h (j + 1))
        (transfer μ e h d (m - j))) : End R V (m + 1 + 1)) =
        h.compMultilinearMap (∑ j ∈ range (m + 1), (acast (kstar ε 1
          (BIN μ (tf μ e h) (tf μ e h) (j + 1)) (transfer μ e h d (m - j))) :
            End R V (m + 1 + 1))) := by
      rw [comp_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [tf_succ, kstar_comp, comp_acast]
    rw [hsum, tf_zero, kstar_op1, acast_acast (by omega), acast_self,
      show fcomp d (tf μ e h) (m + 1) = d.compMultilinearMap (tf μ e h (m + 1)) from rfl, tf_succ,
      show transfer μ e h d (m + 1) =
        e.compMultilinearMap (BIN μ (tf μ e h) (tf μ e h) (m + 1)) from rfl]
    have hK' : ∑ j ∈ range (m + 1), (acast (kstar ε 1 (BIN μ (tf μ e h) (tf μ e h) (j + 1))
        (transfer μ e h d (m - j))) : End R V (m + 1 + 1)) =
        -fcomp d (BIN μ (tf μ e h) (tf μ e h)) (m + 1) := by
      linear_combination (norm := module) hK
    rw [hK']
    ext v
    simp only [fcomp, MultilinearMap.add_apply, LinearMap.compMultilinearMap_apply,
      MultilinearMap.neg_apply, map_neg]
    show d (h _) + _ = e (e _) + -h (d _)
    have := hr.homotopy (BIN μ (tf μ e h) (tf μ e h) (m + 1) v)
    rw [hr.ee]
    linear_combination (norm := module) this

include hd hr in
/-- **The trees form an ∞-morphism** from the transferred structure to the dg algebra:
`d ∘ f + μ (f, f) = f ⋆ b'`. -/
theorem morphism_eq (n : ℕ) :
    fcomp d (tf μ e h) n + BIN μ (tf μ e h) (tf μ e h) n =
      tstar ε 1 (tf μ e h) (transfer μ e h d) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih => exact morph_of_key hr (key_of_morph hd hr ih)

include hd hr in
/-- **The key equation** `d ∘ λ + λ ⋆ b' = 0`. -/
theorem key_eq (n : ℕ) :
    fcomp d (BIN μ (tf μ e h) (tf μ e h)) n +
      tstar ε 1 (BIN μ (tf μ e h) (tf μ e h)) (transfer μ e h d) n = 0 :=
  key_of_morph hd hr fun k _ => morphism_eq hd hr k

include hd hr in
/-- **The homotopy transfer theorem** for dg algebras: the transferred operations
`b'₁ = e d e`, `b'ₙ = e ∘ ∑_{trees}` form an A∞-structure. -/
theorem isAInf_transfer : IsAInf ε (transfer μ e h d) where
  odd n := by
    rcases n with _ | n
    · intro v
      show op1 (e ∘ₗ d ∘ₗ e) (fun t => ε (v t)) = (-1 : R) ^ 1 • ε (op1 (e ∘ₗ d ∘ₗ e) v)
      rw [op1_apply, op1_apply]
      simp only [LinearMap.coe_comp, Function.comp_apply, hr.e_even, hd.d_odd, map_neg,
        pow_one, neg_one_smul]
    · exact isHomog_comp ε (p := 0) (q := 1) (fun x => by rw [hr.e_even, pow_zero, one_smul])
        (isHomog_BIN ε hd.μ_odd (fun k _ => tf_even hd hr k) (fun k _ => tf_even hd hr k))
        (by norm_num)
  mc := by
    funext m
    rcases m with _ | m
    · rw [tstar_apply, Finset.sum_range_one, Nat.sub_zero]
      show (acast (kstar ε 1 (op1 (e ∘ₗ d ∘ₗ e)) (op1 (e ∘ₗ d ∘ₗ e))) : End R V 1) = 0
      rw [kstar_op1, acast_acast (by omega), acast_self]
      ext v
      change (e ∘ₗ d ∘ₗ e) ((e ∘ₗ d ∘ₗ e) (v 0)) = 0
      simp only [LinearMap.comp_apply, hr.ee, hr.de, hd.dd, map_zero]
    · rw [tstar_succ]
      have hsum : ∑ j ∈ range (m + 1), (acast (kstar ε 1 (transfer μ e h d (j + 1))
          (transfer μ e h d (m - j))) : End R V (m + 1 + 1)) =
          e.compMultilinearMap (∑ j ∈ range (m + 1), (acast (kstar ε 1
            (BIN μ (tf μ e h) (tf μ e h) (j + 1)) (transfer μ e h d (m - j))) :
              End R V (m + 1 + 1))) := by
        rw [comp_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show transfer μ e h d (j + 1) =
          e.compMultilinearMap (BIN μ (tf μ e h) (tf μ e h) (j + 1)) from rfl, kstar_comp,
          comp_acast]
      have hK := key_eq hd hr (m + 1)
      rw [tstar_succ, BIN_zero, kstar_zero_left, acast_zero, zero_add] at hK
      rw [hsum, show transfer μ e h d 0 = op1 (e ∘ₗ d ∘ₗ e) from rfl, kstar_op1,
        acast_acast (by omega), acast_self]
      ext v
      have hv := congrArg (fun F => e (F v)) hK
      simp only [fcomp, MultilinearMap.add_apply, LinearMap.compMultilinearMap_apply, map_add,
        MultilinearMap.zero_apply, map_zero] at hv
      simp only [Pi.zero_apply, MultilinearMap.zero_apply, MultilinearMap.add_apply,
        LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply]
      show e (d (e (e _))) + _ = 0
      rw [hr.ee, hr.de, hr.ee]
      exact hv

include hr in
/-- **Homotopy transfer** from a dg algebra given as an A∞-structure concentrated in arities one
and two (`AInf.dga`). -/
theorem isAInf_transfer_of_dga (hdo : ∀ x, d (ε x) = -ε (d x)) (hμ : IsHomog ε 1 μ)
    (hdga : IsAInf ε (AInf.dga R V (op1 d) μ)) : IsAInf ε (transfer μ e h d) := by
  have hd1 : IsHomog ε 1 (op1 d) := fun v => by
    change d (ε (v 0)) = (-1 : R) ^ 1 • ε (d (v 0))
    rw [hdo, pow_one, neg_one_smul]
  obtain ⟨h1, h2, h3⟩ := (isAInf_dga_iff ε hd1 hμ).1 hdga
  exact isAInf_transfer ⟨hdo, hμ, fun x => h1 x, fun x y => h2 x y, h3⟩ hr

end Theorem

end HTT

end Operad
