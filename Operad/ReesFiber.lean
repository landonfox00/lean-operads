/-
# The fibers of the Rees operad: the operad at `ħ = 1`, the associated graded at `ħ = 0`

For a filtered symmetric operad `(P, F)` over `R` (`SymOperadFiltration`), the Rees operad
`Rees = ⊕ₚ Fₚ ħᵖ` is an operad over `R[X]` (`Operad.PolyOperad`). This file computes its two
fibers, as operads over `R` (restriction of scalars, `Operad.ScalarRestriction`).

* **Evaluation** (`PolyOp.evalHom c`, `SymOperadFiltration.reesEval c`): `ħ ↦ c` is a morphism of
  operads over `R` from the polynomials with coefficients in `P`, and from the Rees operad, to
  `P`.
* **The quotients** `SymOperadFiltration.ReesMod q` of the Rees operad by the multiples of a
  polynomial `q` (`SymOperadFiltration.reesIdeal q`), operads over `R`.
* **The fiber at `ħ = 1`** (`SymOperadFiltration.reesModOneIso`): `Rees / (ħ - 1) ≅ P`. Evaluation
  at `1` is onto because the filtration is exhaustive (`reesEval_one_surjective`), and a
  polynomial of the Rees operad vanishing at `1` is `ħ - 1` times the polynomial of the partial
  sums of its coefficients, with a sign, which is in the Rees operad because the filtration
  increases (`exists_eq_X_sub_one_smul`).
* **The associated graded operad** (`SymOperadFiltration.Gr`): `Rees / ħ`. The multiples of `ħ`
  are the polynomials without constant term whose coefficient of `ħ^(p + 1)` is in `F p`
  (`mem_reesIdeal_X_iff`). The symbol `symb p : F p A → Gr A`, `x ↦ [x ħᵖ]`, is linear,
  multiplicative (`symb_comp`), injective for `p = 0` (`symb_zero_eq_zero_iff`), and has kernel
  `F p` in degree `p + 1` (`symb_succ_eq_zero_iff`); the symbols span (`exists_sum_symb`) and are
  independent across degrees (`symb_eq_zero_of_sum`). So `Gr A` is the direct sum of `F 0 A` and
  the quotients `F (p + 1) A / F p A`, with the composition induced by that of `P`.
-/
import Operad.PolyOperad
import Operad.ScalarRestriction

universe u v

namespace PolynomialModule

open Polynomial

variable {R : Type u} [CommRing R] {M : Type*} {N : Type*} {L : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup L] [Module R L]

/-- **Evaluation commutes with convolution.** -/
lemma eval_conv (c : R) (β : M →ₗ[R] N →ₗ[R] L) (f : PolynomialModule R M)
    (g : PolynomialModule R N) : eval c (conv β f g) = β (eval c f) (eval c g) := by
  induction f using induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add f f' hf hf' =>
    rw [map_add, LinearMap.add_apply, map_add, hf, hf', map_add, map_add, LinearMap.add_apply]
  | single p m =>
    induction g using induction_linear with
    | zero => rw [map_zero, map_zero, map_zero, map_zero]
    | add g g' hg hg' => rw [map_add, map_add, hg, hg', map_add, map_add]
    | single q n =>
      rw [conv_single, eval_single, eval_single, eval_single, LinearMap.map_smul,
        LinearMap.map_smul, LinearMap.smul_apply, smul_smul, pow_add, mul_comm]

/-- The coefficient of `ħⁿ` in a sum of monomials. -/
lemma sum_single_apply (N : ℕ) (a : ℕ → M) (n : ℕ) :
    (∑ k ∈ Finset.range N, single R k (a k)) n = if n < N then a n else 0 := by
  rw [show (∑ k ∈ Finset.range N, single R k (a k)) n =
    (∑ k ∈ Finset.range N, (Finsupp.single k (a k) : ℕ →₀ M)) n from rfl,
    Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_range]

/-- The coefficients of `X • f`. -/
lemma X_smul_apply (f : PolynomialModule R M) (n : ℕ) :
    ((X : R[X]) • f) n = if 1 ≤ n then f (n - 1) else 0 := by
  rw [← Polynomial.monomial_one_one_eq_X, monomial_smul_apply, one_smul]

/-- A polynomial vanishes above some degree, and its value at `1` is the sum of its
coefficients. -/
lemma exists_bound (f : PolynomialModule R M) :
    ∃ N : ℕ, (∀ n, N ≤ n → f n = 0) ∧ eval 1 f = ∑ p ∈ Finset.range N, f p := by
  refine ⟨(show ℕ →₀ M from f).support.sup id + 1, fun n hn => ?_, ?_⟩
  · by_contra h
    have h1 : n ≤ (show ℕ →₀ M from f).support.sup id :=
      Finset.le_sup (f := id) (Finsupp.mem_support_iff.2 h)
    exact absurd (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le h1) hn) (lt_irrefl _)
  · have hs : (show ℕ →₀ M from f).support ⊆
        Finset.range ((show ℕ →₀ M from f).support.sup id + 1) := fun p hp =>
      Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hp))
    show (show ℕ →₀ M from f).sum (fun i m => (1 : R) ^ i • m) = _
    rw [Finsupp.sum_of_support_subset _ hs _ (fun i _ => smul_zero _)]
    exact Finset.sum_congr rfl fun i _ => by rw [one_pow, one_smul]

end PolynomialModule

namespace Operad

open Polynomial

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]

namespace PolyOp

/-- **Evaluation at `ħ = c`**, on each component, linear over `R`. -/
noncomputable def evalL (c : R) (A : Type) [Fintype A] [DecidableEq A] :
    ResOp R R[X] (PolyOp R P) A →ₗ[R] P A where
  toFun f := PolynomialModule.eval c (show PolynomialModule R (P A) from f)
  map_add' f g := map_add (PolynomialModule.eval c) _ _
  map_smul' r f := by
    show PolynomialModule.eval c (algebraMap R R[X] r • (show PolynomialModule R (P A) from f))
      = r • PolynomialModule.eval c (show PolynomialModule R (P A) from f)
    rw [PolynomialModule.eval_smul, ← Polynomial.C_eq_algebraMap, Polynomial.eval_C]

omit [SymOperad R P] in
lemma evalL_single (c : R) {A : Type} [Fintype A] [DecidableEq A] (p : ℕ) (x : P A) :
    evalL c A (single (R := R) p x) = c ^ p • x :=
  PolynomialModule.eval_single c p x

/-- **Evaluation at `ħ = c`** is a morphism of operads over `R` from the polynomials with
coefficients in `P` to `P`. -/
noncomputable def evalHom (c : R) : SymOperadHom R (ResOp R R[X] (PolyOp R P)) P where
  app A _ _ := evalL c A
  app_map e f := PolynomialModule.eval_map (R' := R) (SymOperad.map (R := R) e)
    (show PolynomialModule R (P _) from f) c
  app_one := by
    show evalL c Unit (single (R := R) 0 (SymOperad.one R)) = _
    rw [evalL_single, pow_zero, one_smul]
  app_comp i f g := PolynomialModule.eval_conv c (SymOperad.comp (R := R) i)
    (show PolynomialModule R (P _) from f) (show PolynomialModule R (P _) from g)

@[simp] lemma evalHom_app (c : R) {A : Type} [Fintype A] [DecidableEq A]
    (f : ResOp R R[X] (PolyOp R P) A) : (evalHom c).app A f = evalL c A f := rfl

end PolyOp

namespace SymOperadFiltration

variable (Φ : SymOperadFiltration R P)

/-- **Specialization of the Rees operad at `ħ = c`**, a morphism of operads over `R`. -/
noncomputable def reesEval (c : R) : SymOperadHom R (ResOp R R[X] Φ.Rees) P :=
  (PolyOp.evalHom c).comp (Φ.rees.incl.res R)

lemma reesEval_app (c : R) {A : Type} [Fintype A] [DecidableEq A] (f : Φ.Rees A) :
    (Φ.reesEval c).app A f = PolyOp.evalL c A f.1 := rfl

/-- **Specialization at `ħ = 1` is onto**: the filtration is exhaustive. -/
theorem reesEval_one_surjective (A : Type) [Fintype A] [DecidableEq A] :
    Function.Surjective ((Φ.reesEval 1).app A) := fun x => by
  obtain ⟨p, hp⟩ := Φ.exhaustive x
  refine ⟨⟨PolyOp.single (R := R) p x, Φ.single_mem_reesSub hp⟩, ?_⟩
  rw [reesEval_app, PolyOp.evalL_single, one_pow, one_smul]

/-- **A polynomial of the Rees operad vanishing at `ħ = 1` is a multiple of `ħ - 1`** in the
Rees operad: the quotient has the partial sums of the coefficients, with a sign. -/
theorem exists_eq_X_sub_one_smul {A : Type} [Fintype A] [DecidableEq A] {f : PolyOp R P A}
    (hf : f ∈ Φ.reesSub A)
    (h0 : PolynomialModule.eval (1 : R) (show PolynomialModule R (P A) from f) = 0) :
    ∃ g ∈ Φ.reesSub A, f = ((X : R[X]) - 1) • g := by
  obtain ⟨N, hN, hev⟩ := PolynomialModule.exists_bound (show PolynomialModule R (P A) from f)
  rw [h0] at hev
  set σ : ℕ → P A := fun n => ∑ p ∈ Finset.range (n + 1), PolyOp.coeff f p with hσ
  have hσN : ∀ n, N ≤ n → σ n = 0 := fun n hn => by
    rw [hev]
    refine (Finset.sum_subset (Finset.range_mono (Nat.le_succ_of_le hn))
      fun p _ hp => hN p (not_lt.1 fun h => hp (Finset.mem_range.2 h))).symm
  set g : PolyOp R P A := ∑ k ∈ Finset.range N, PolynomialModule.single R k (-σ k) with hg
  have hcoeff : ∀ n, PolyOp.coeff g n = -σ n := fun n => by
    show (∑ k ∈ Finset.range N, PolynomialModule.single R k (-σ k)) n = _
    rw [PolynomialModule.sum_single_apply]
    split_ifs with h
    · rfl
    · rw [hσN n (not_lt.1 h), neg_zero]
  refine ⟨g, fun n => ?_, ?_⟩
  · rw [hcoeff]
    exact (Φ.F n A).neg_mem ((Φ.F n A).sum_mem fun p hp =>
      Φ.mono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)) A (hf p))
  · refine PolyOp.ext fun n => ?_
    show PolyOp.coeff f n = (((X : R[X]) - 1) • (show PolynomialModule R (P A) from g)) n
    rw [sub_smul, one_smul]
    show _ = ((X : R[X]) • (show PolynomialModule R (P A) from g)) n - PolyOp.coeff g n
    rw [PolynomialModule.X_smul_apply, hcoeff]
    rcases n with _ | n
    · rw [if_neg (by norm_num), zero_sub, neg_neg, hσ]
      simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    · rw [if_pos (Nat.succ_le_succ (Nat.zero_le n)), Nat.add_sub_cancel]
      show _ = PolyOp.coeff g n - -σ (n + 1)
      rw [hcoeff, hσ]
      simp only
      rw [Finset.sum_range_succ (fun p => PolyOp.coeff f p) (n + 1)]
      abel

/-! ## The quotients of the Rees operad by a polynomial -/

/-- **The multiples of a polynomial `q` in the Rees operad**, as an ideal over `R`. -/
noncomputable def reesIdeal (q : R[X]) : SymOperadIdeal R (ResOp R R[X] Φ.Rees) :=
  (SymOperadIdeal.smulTop Φ.Rees q).res R

lemma mem_reesIdeal {q : R[X]} {A : Type} [Fintype A] [DecidableEq A] {f : Φ.Rees A} :
    f ∈ (Φ.reesIdeal q).sub A ↔ ∃ g : Φ.Rees A, f = q • g := by
  show f ∈ (SymOperadIdeal.smulTop Φ.Rees q).sub A ↔ _
  exact SymOperadIdeal.mem_smulTop

/-- **The Rees operad modulo a polynomial** `q`, an operad over `R`. For `q = ħ - 1` it is `P`
(`reesModOneIso`), for `q = ħ` it is the associated graded operad (`Gr`). -/
abbrev ReesMod (q : R[X]) := (Φ.reesIdeal q).Quot

/-- **The kernel of the specialization at `ħ = 1`** is `(ħ - 1)` times the Rees operad. -/
theorem reesEval_one_eq_zero_iff {A : Type} [Fintype A] [DecidableEq A] (f : Φ.Rees A) :
    (Φ.reesEval 1).app A f = 0 ↔ f ∈ (Φ.reesIdeal (X - 1)).sub A := by
  constructor
  · intro h
    obtain ⟨g, hg, hfg⟩ := Φ.exists_eq_X_sub_one_smul f.2 h
    exact Φ.mem_reesIdeal.2 ⟨⟨g, hg⟩, Subtype.ext hfg⟩
  · intro h
    obtain ⟨g, rfl⟩ := Φ.mem_reesIdeal.1 h
    show PolynomialModule.eval (1 : R) (((X : R[X]) - 1) •
      (show PolynomialModule R (P A) from g.1)) = 0
    rw [PolynomialModule.eval_smul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one,
      sub_self, zero_smul]

/-- **The fiber of the Rees operad at `ħ = 1` is the operad**: `Rees / (ħ - 1) ≅ P`, an
isomorphism of operads over `R`. -/
noncomputable def reesModOneIso : SymOperadIso R (Φ.ReesMod (X - 1)) P :=
  SymOperadIso.ofBijective
    ((Φ.reesIdeal (X - 1)).liftHom (Φ.reesEval 1)
      fun _ _ _ f hf => (Φ.reesEval_one_eq_zero_iff f).2 hf)
    fun A _ _ => ⟨(injective_iff_map_eq_zero _).2 fun z hz => by
        obtain ⟨f, rfl⟩ := (Φ.reesIdeal (X - 1)).proj_surjective A z
        exact ((Φ.reesIdeal (X - 1)).proj_eq_zero_iff f).2
          ((Φ.reesEval_one_eq_zero_iff f).1 hz),
      fun x => by
        obtain ⟨f, hf⟩ := Φ.reesEval_one_surjective A x
        exact ⟨(Φ.reesIdeal (X - 1)).proj A f, hf⟩⟩

/-- **The isomorphism at `ħ = 1` on classes**: the sum of the coefficients. -/
lemma reesModOneIso_proj {A : Type} [Fintype A] [DecidableEq A] (f : Φ.Rees A) :
    Φ.reesModOneIso.hom.app A ((Φ.reesIdeal (X - 1)).proj A f) = (Φ.reesEval 1).app A f := rfl

/-! ## The associated graded operad -/

/-- **The associated graded operad** of a filtered operad: the fiber of the Rees operad at
`ħ = 0`, an operad over `R`. Its component on `A` is the direct sum of the quotients
`F p A / F (p - 1) A`, through the symbols (`symb`, `symb_succ_eq_zero_iff`, `exists_sum_symb`,
`symb_eq_zero_of_sum`). -/
abbrev Gr := Φ.ReesMod X

/-- **The multiples of `ħ` in the Rees operad**: the polynomials without constant term whose
coefficient of `ħ^(p + 1)` has filtration degree at most `p`. -/
theorem mem_reesIdeal_X_iff {A : Type} [Fintype A] [DecidableEq A] (f : Φ.Rees A) :
    f ∈ (Φ.reesIdeal X).sub A ↔
      PolyOp.coeff f.1 0 = 0 ∧ ∀ p, PolyOp.coeff f.1 (p + 1) ∈ Φ.F p A := by
  constructor
  · intro h
    obtain ⟨g, rfl⟩ := Φ.mem_reesIdeal.1 h
    refine ⟨?_, fun p => ?_⟩
    · show ((X : R[X]) • (show PolynomialModule R (P A) from g.1)) 0 = 0
      rw [PolynomialModule.X_smul_apply, if_neg (by norm_num)]
    · show ((X : R[X]) • (show PolynomialModule R (P A) from g.1)) (p + 1) ∈ _
      rw [PolynomialModule.X_smul_apply, if_pos (Nat.succ_le_succ (Nat.zero_le p)),
        Nat.add_sub_cancel]
      exact g.2 p
  · rintro ⟨h0, h1⟩
    set g : PolyOp R P A :=
      Finsupp.comapDomain Nat.succ (show ℕ →₀ P A from f.1) Nat.succ_injective.injOn with hg
    have hcoeff : ∀ p, PolyOp.coeff g p = PolyOp.coeff f.1 (p + 1) := fun p =>
      Finsupp.comapDomain_apply _ _ _ p
    refine Φ.mem_reesIdeal.2 ⟨⟨g, fun p => by rw [hcoeff]; exact h1 p⟩, Subtype.ext ?_⟩
    refine PolyOp.ext fun n => ?_
    show PolyOp.coeff f.1 n = ((X : R[X]) • (show PolynomialModule R (P A) from g)) n
    rw [PolynomialModule.X_smul_apply]
    rcases n with _ | n
    · rw [if_neg (by norm_num), h0]
    · rw [if_pos (Nat.succ_le_succ (Nat.zero_le n)), Nat.add_sub_cancel]
      exact (hcoeff n).symm

/-- The monomial `x ħᵖ` of the Rees operad, for `x` of filtration degree at most `p`. -/
noncomputable def reesSingle (p : ℕ) {A : Type} [Fintype A] [DecidableEq A] (x : Φ.F p A) :
    Φ.Rees A :=
  ⟨PolyOp.single (R := R) p x.1, Φ.single_mem_reesSub x.2⟩

/-- **The symbol** of an operation of filtration degree at most `p`: the class of `x ħᵖ` in the
associated graded operad. -/
noncomputable def symb (p : ℕ) (A : Type) [Fintype A] [DecidableEq A] : Φ.F p A →ₗ[R] Φ.Gr A where
  toFun x := (Φ.reesIdeal X).proj A (Φ.reesSingle p x)
  map_add' x y := by
    rw [← map_add]
    exact congrArg _ (Subtype.ext (map_add (PolynomialModule.single R p) x.1 y.1))
  map_smul' r x := by
    rw [RingHom.id_apply, ← map_smul]
    refine congrArg _ (Subtype.ext ?_)
    show PolynomialModule.single R p (r • x.1) =
      algebraMap R R[X] r • PolynomialModule.single R p x.1
    rw [← Polynomial.C_eq_algebraMap, ← Polynomial.monomial_zero_left,
      PolynomialModule.monomial_smul_single, zero_add]

lemma symb_apply (p : ℕ) {A : Type} [Fintype A] [DecidableEq A] (x : Φ.F p A) :
    Φ.symb p A x = (Φ.reesIdeal X).proj A (Φ.reesSingle p x) := rfl

/-- **Symbols multiply**: the composite of the symbols of `x` and `y` is the symbol of `x ∘ᵢ y`
in degree `p + q`. -/
theorem symb_comp {p q : ℕ} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (i : A) (x : Φ.F p A) (y : Φ.F q B) :
    SymOperad.comp (R := R) i (Φ.symb p A x) (Φ.symb q B y) =
      Φ.symb (p + q) _ ⟨SymOperad.comp (R := R) i x.1 y.1, Φ.comp_mem i x.2 y.2⟩ := by
  show (Φ.reesIdeal X).compQ i ((Φ.reesIdeal X).proj A _) ((Φ.reesIdeal X).proj B _) = _
  rw [SymOperadIdeal.compQ_proj]
  exact congrArg _ (Subtype.ext (PolyOp.comp_single i p q x.1 y.1))

/-- **The symbol of degree zero is injective.** -/
theorem symb_zero_eq_zero_iff {A : Type} [Fintype A] [DecidableEq A] (x : Φ.F 0 A) :
    Φ.symb 0 A x = 0 ↔ x = 0 := by
  refine ((Φ.reesIdeal X).proj_eq_zero_iff _).trans ((Φ.mem_reesIdeal_X_iff _).trans ?_)
  constructor
  · rintro ⟨h0, -⟩
    refine Subtype.ext ?_
    rw [reesSingle, PolyOp.coeff_single, if_pos rfl] at h0
    exact h0
  · rintro rfl
    refine ⟨?_, fun p => ?_⟩
    · rw [reesSingle, PolyOp.coeff_single, if_pos rfl]
      rfl
    · rw [reesSingle, PolyOp.coeff_single, if_neg (Nat.succ_ne_zero p).symm]
      exact (Φ.F p A).zero_mem

/-- **The kernel of the symbol of degree `p + 1`** is the filtration degree `p`: the component
of degree `p + 1` of the associated graded operad is `F (p + 1) / F p`. -/
theorem symb_succ_eq_zero_iff {p : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (x : Φ.F (p + 1) A) : Φ.symb (p + 1) A x = 0 ↔ x.1 ∈ Φ.F p A := by
  refine ((Φ.reesIdeal X).proj_eq_zero_iff _).trans ((Φ.mem_reesIdeal_X_iff _).trans ?_)
  constructor
  · rintro ⟨-, h1⟩
    have := h1 p
    rwa [reesSingle, PolyOp.coeff_single, if_pos rfl] at this
  · intro hx
    refine ⟨?_, fun q => ?_⟩
    · rw [reesSingle, PolyOp.coeff_single, if_neg (Nat.succ_ne_zero p)]
    · rw [reesSingle, PolyOp.coeff_single]
      split_ifs with h
      · rw [← Nat.succ_injective h]
        exact hx
      · exact (Φ.F q A).zero_mem

/-- **Every operation of the associated graded operad is a sum of symbols.** -/
theorem exists_sum_symb {A : Type} [Fintype A] [DecidableEq A] (z : Φ.Gr A) :
    ∃ (s : Finset ℕ) (x : ∀ p, Φ.F p A), z = ∑ p ∈ s, Φ.symb p A (x p) := by
  obtain ⟨f, rfl⟩ := (Φ.reesIdeal X).proj_surjective A z
  obtain ⟨s, hs⟩ := PolyOp.sum_single f.1
  refine ⟨s, fun p => ⟨PolyOp.coeff f.1 p, f.2 p⟩, ?_⟩
  have hf : f = ∑ p ∈ s, Φ.reesSingle p ⟨PolyOp.coeff f.1 p, f.2 p⟩ := by
    refine Subtype.ext ?_
    rw [Submodule.coe_sum]
    exact hs
  exact (congrArg ((Φ.reesIdeal X).proj A) hf).trans (map_sum ((Φ.reesIdeal X).proj A) _ s)

/-- **Symbols of different degrees are independent**: a sum of symbols, one in each degree,
vanishes only if each does. With `exists_sum_symb` and the kernels of the symbols, the component
of the associated graded operad on `A` is the direct sum of `F 0 A` and the quotients
`F (p + 1) A / F p A`. -/
theorem symb_eq_zero_of_sum {A : Type} [Fintype A] [DecidableEq A] (s : Finset ℕ)
    (x : ∀ p, Φ.F p A) (h : ∑ p ∈ s, Φ.symb p A (x p) = 0) : ∀ p ∈ s, Φ.symb p A (x p) = 0 := by
  have h' : (Φ.reesIdeal X).proj A (∑ p ∈ s, Φ.reesSingle p (x p)) = 0 :=
    (map_sum ((Φ.reesIdeal X).proj A) _ s).trans h
  have hm := (Φ.mem_reesIdeal_X_iff _).1 (((Φ.reesIdeal X).proj_eq_zero_iff _).1 h')
  have hc : ∀ n, PolyOp.coeff (∑ p ∈ s, Φ.reesSingle p (x p)).1 n =
      if n ∈ s then (x n).1 else 0 := fun n => by
    rw [Submodule.coe_sum]
    show (∑ p ∈ s, (Finsupp.single p (x p).1 : ℕ →₀ P A)) n = _
    rw [Finsupp.finsetSum_apply]
    simp only [Finsupp.single_apply, Finset.sum_ite_eq']
  intro p hp
  rcases p with _ | p
  · refine (Φ.symb_zero_eq_zero_iff _).2 (Subtype.ext ?_)
    have h0 : (if 0 ∈ s then (x 0).1 else 0) = 0 := (hc 0).symm.trans hm.1
    rwa [if_pos hp] at h0
  · refine (Φ.symb_succ_eq_zero_iff _).2 ?_
    have h1 : (if p + 1 ∈ s then (x (p + 1)).1 else 0) ∈ Φ.F p A :=
      Eq.mp (congrArg (· ∈ Φ.F p A) (hc (p + 1))) (hm.2 p)
    rwa [if_pos hp] at h1

end SymOperadFiltration

end Operad
