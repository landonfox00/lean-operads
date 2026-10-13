/-
# Coaugmented and conilpotent cooperads

A **coaugmentation** of a cooperad `C` is a cooperation `1` of arity one with counit one whose
relabellings span a subcooperad: every decomposition of a relabelling of `1` lies in the tensor
product of their spans (`SymCooperad.Coaug`). Write `R·1` for that span in each arity
(`SymCooperad.coaugSpan`).

**The coradical filtration** (`SymCooperad.filt`) starts from `F₀ = R·1`, and `F_{n+1}` consists of
the cooperations each of whose infinitesimal decompositions, after any relabelling, lies in

  `R·1 ⊗ C + C ⊗ R·1 + Fₙ ⊗ Fₙ`:

up to the coaugmentation, every decomposition of a cooperation in `F_{n+1}` has both pieces in
`Fₙ`. The filtration is increasing (`filt_mono`), starts with `R·1` in every stage
(`coaugSpan_le_filt`), and is stable under relabelling (`map_mem_filt`). The cooperad is
**conilpotent** when the filtration is exhaustive (`SymCooperad.Conilpotent`): iterating reduced
decompositions on any cooperation ends in finitely many steps.

**Decomposition cooperads of connected weighted operads are conilpotent.** A *connected weight* on a
set operad is a morphism to the natural numbers under addition (`WtOp`) whose operations of weight
zero are the relabellings of the identity (`SetOperad.ConnectedWeight`). Then the identity is a
coaugmentation of the decomposition cooperad (`Lin.instCoaug`), an operation of weight `n` lies in
`Fₙ` (`Lin.single_mem_filt`), and the decomposition cooperad is conilpotent
(`Lin.conilpotent`).
-/
import Operad.DecCooperad

universe u v w

namespace Operad

open scoped TensorProduct

open Sym

namespace SymCooperad

variable (R : Type u) [CommRing R] (C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [SymCooperad R C]

/-- The span of the relabellings of a cooperation of arity one. -/
def unitSpan (one : C Unit) (A : Type) [Fintype A] [DecidableEq A] : Submodule R (C A) :=
  Submodule.span R (Set.range fun e : Unit ≃ A => map (R := R) e one)

/-- The tensor product of two submodules, as the span of their pure tensors. -/
abbrev tensSub {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (M : Submodule R X) (N : Submodule R Y) : Submodule R (X ⊗[R] Y) :=
  Submodule.map₂ (TensorProduct.mk R X Y) M N

/-- **A coaugmentation**: a cooperation of arity one with counit one, whose relabellings span a
subcooperad. -/
class Coaug where
  /-- The coaugmentation, the cooperation `1` of arity one. -/
  one : C Unit
  /-- The counit of the coaugmentation is one. -/
  counit_one : counit (R := R) (C := C) one = 1
  /-- The decompositions of the relabellings of `1` are tensors of relabellings of `1`. -/
  decomp_mem {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (e : Unit ≃ Without A i ⊕ B) :
    decomp (R := R) i (map (R := R) e one) ∈ tensSub R (unitSpan R C one A) (unitSpan R C one B)

variable [Coaug R C]

/-- The span `R·1` of the relabellings of the coaugmentation. -/
abbrev coaugSpan (A : Type) [Fintype A] [DecidableEq A] : Submodule R (C A) :=
  unitSpan R C (Coaug.one (R := R) (C := C)) A

/-- The decompositions allowed in the stage after `F` of the coradical filtration:
`R·1 ⊗ C + C ⊗ R·1 + F ⊗ F`. -/
def filtTarget (F : ∀ (A : Type) [Fintype A] [DecidableEq A], Submodule R (C A)) (A B : Type)
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] : Submodule R (C A ⊗[R] C B) :=
  tensSub R (coaugSpan R C A) ⊤ ⊔ tensSub R ⊤ (coaugSpan R C B) ⊔ tensSub R (F A) (F B)

/-- **The coradical filtration**: `F₀ = R·1`, and `F_{n+1}` consists of the cooperations all of
whose relabelled decompositions lie in `R·1 ⊗ C + C ⊗ R·1 + Fₙ ⊗ Fₙ`. -/
def filt : ℕ → ∀ (A : Type) [Fintype A] [DecidableEq A], Submodule R (C A)
  | 0 => fun A _ _ => coaugSpan R C A
  | n + 1 => fun A _ _ =>
    { carrier := {c | ∀ (B D : Type) [Fintype B] [DecidableEq B] [Fintype D] [DecidableEq D]
          (i : B) (e : Without B i ⊕ D ≃ A),
          decomp (R := R) i (map (R := R) e.symm c) ∈ filtTarget R C (filt n) B D}
      add_mem' := fun ha hb B D _ _ _ _ i e => by
        simpa only [map_add] using add_mem (ha B D i e) (hb B D i e)
      zero_mem' := fun B D _ _ _ _ i e => by simp only [map_zero, zero_mem]
      smul_mem' := fun r c hc B D _ _ _ _ i e => by
        simpa only [map_smul] using Submodule.smul_mem _ r (hc B D i e) }

/-- **A conilpotent cooperad**: its coradical filtration is exhaustive. -/
def Conilpotent : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (c : C A), ∃ n, c ∈ filt R C n A

variable {R C}
variable {A A' B D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  [Fintype B] [DecidableEq B] [Fintype D] [DecidableEq D]

lemma mem_filt_succ {n : ℕ} {c : C A} :
    c ∈ filt R C (n + 1) A ↔ ∀ (B D : Type) [Fintype B] [DecidableEq B] [Fintype D]
      [DecidableEq D] (i : B) (e : Without B i ⊕ D ≃ A),
      decomp (R := R) i (map (R := R) e.symm c) ∈ filtTarget R C (filt R C n) B D :=
  Iff.rfl

lemma filt_zero : filt R C 0 A = coaugSpan R C A :=
  rfl

omit [Coaug R C] in
/-- Relabellings of the generators of a span of relabellings stay in it. -/
lemma map_mem_unitSpan (one : C Unit) (e : A ≃ A') {c : C A} (hc : c ∈ unitSpan R C one A) :
    map (R := R) e c ∈ unitSpan R C one A' := by
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e', rfl⟩ := hx
    exact Submodule.subset_span ⟨e'.trans e, map_trans (R := R) (C := C) e' e one⟩
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
  | smul r x _ hx => simpa only [map_smul] using Submodule.smul_mem _ r hx

/-- The coaugmentation span is a subcooperad. -/
lemma decomp_mem_coaugSpan (i : A) {c : C (Without A i ⊕ B)}
    (hc : c ∈ coaugSpan R C (Without A i ⊕ B)) :
    decomp (R := R) i c ∈ tensSub R (coaugSpan R C A) (coaugSpan R C B) := by
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, rfl⟩ := hx
    exact Coaug.decomp_mem i e
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
  | smul r x _ hx => simpa only [map_smul] using Submodule.smul_mem _ r hx

lemma filtTarget_mono {F G : ∀ (A : Type) [Fintype A] [DecidableEq A], Submodule R (C A)}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A], F A ≤ G A) :
    filtTarget R C F B D ≤ filtTarget R C G B D :=
  sup_le_sup_left (Submodule.map₂_le_map₂ (h B) (h D)) _

/-- The filtration is stable under relabelling. -/
lemma map_mem_filt (n : ℕ) (e : A ≃ A') {c : C A} (hc : c ∈ filt R C n A) :
    map (R := R) e c ∈ filt R C n A' := by
  cases n with
  | zero => exact map_mem_unitSpan _ e hc
  | succ n =>
    intro B D _ _ _ _ i e'
    have h := hc B D i (e'.trans e.symm)
    rwa [← map_trans, show e.trans e'.symm = (e'.trans e.symm).symm by ext; simp]

/-- Every stage of the filtration contains the coaugmentation. -/
lemma coaugSpan_le_filt (n : ℕ) (A : Type) [Fintype A] [DecidableEq A] :
    coaugSpan R C A ≤ filt R C n A := by
  induction n generalizing A with
  | zero => exact le_rfl
  | succ n ih =>
    intro c hc B D _ _ _ _ i e
    have := decomp_mem_coaugSpan (R := R) (C := C) i (map_mem_unitSpan _ e.symm hc)
    exact Submodule.mem_sup_right ((Submodule.map₂_le_map₂ (ih B) (ih D)) this)

/-- **The coradical filtration is increasing.** -/
lemma filt_mono (n : ℕ) (A : Type) [Fintype A] [DecidableEq A] :
    filt R C n A ≤ filt R C (n + 1) A := by
  induction n generalizing A with
  | zero => exact coaugSpan_le_filt 1 A
  | succ n ih =>
    intro c hc B D _ _ _ _ i e
    exact filtTarget_mono (fun A _ _ => ih A) (hc B D i e)

lemma filt_le_filt {m n : ℕ} (h : m ≤ n) (A : Type) [Fintype A] [DecidableEq A] :
    filt R C m A ≤ filt R C n A := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (filt_mono _ A)

end SymCooperad

/-! ## Connected weights -/

/-- The set operad of weights: `ℕ` in every arity, composing by addition. -/
@[nolint unusedArguments]
abbrev WtOp : (A : Type) → [Fintype A] → [DecidableEq A] → Type := fun _ _ _ => ℕ

instance instSetOperadWtOp : SetOperad WtOp where
  map _ := id
  map_refl _ := rfl
  map_trans _ _ _ := rfl
  one := (0 : ℕ)
  comp _ x y := (x + y : ℕ)
  map_comp _ _ _ _ _ := rfl
  comp_one _ x := Nat.add_zero x
  one_comp y := Nat.zero_add y
  comp_assoc_seq _ _ x y z := Nat.add_assoc x y z
  comp_assoc_par _ x y z := Nat.add_right_comm x y z

/-- **A connected weight** on a set operad: a morphism to the weights whose operations of weight
zero are the relabellings of the identity. -/
class SetOperad.ConnectedWeight (S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    [SetOperad S] where
  /-- The weight of an operation. -/
  wt : SetOperadHom S WtOp
  /-- The operations of weight zero are the relabellings of the identity. -/
  eq_unit {A : Type} [Fintype A] [DecidableEq A] (t : S A) :
    wt.app A t = 0 → ∃ e : Unit ≃ A, t = SetOperad.map e SetOperad.one

namespace SetOperad.ConnectedWeight

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  [ConnectedWeight S] {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The weight of an operation, as a natural number. -/
abbrev w (t : S A) : ℕ := (wt (S := S)).app A t

lemma w_map (e : A ≃ B) (t : S A) : w (SetOperad.map e t) = w t :=
  (wt (S := S)).app_map e t

lemma w_one : w (SetOperad.one : S Unit) = 0 :=
  (wt (S := S)).app_one

lemma w_comp (i : A) (p : S A) (q : S B) : w (SetOperad.comp i p q) = w p + w q :=
  (wt (S := S)).app_comp i p q

lemma w_eq_zero_iff (t : S A) : w t = 0 ↔ ∃ e : Unit ≃ A, t = SetOperad.map e SetOperad.one :=
  ⟨eq_unit t, fun ⟨e, he⟩ => by rw [he, w_map, w_one]⟩

end SetOperad.ConnectedWeight

namespace Lin

open SymCooperad SetOperad.ConnectedWeight

variable {R : Type u} [CommRing R]
  {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  [SetOperad.FiniteFact S]
variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- A decomposition lies in a submodule as soon as the tensor of every factorization it involves
does. -/
lemma decompL_mem (i : A) (x : S (Without A i ⊕ B) →₀ R)
    (P : Submodule R ((S A →₀ R) ⊗[R] (S B →₀ R)))
    (h : ∀ p q, x (SetOperad.comp i p q) ≠ 0 →
      Finsupp.single p (1 : R) ⊗ₜ Finsupp.single q (1 : R) ∈ P) :
    decompL R i x ∈ P := by
  set y := finComap (R := R) (fun pq : S A × S B => SetOperad.comp i pq.1 pq.2)
    (SetOperad.FiniteFact.finite i) x with hy
  have hdec : decompL R i x = (tens R (S A) (S B)).symm y := rfl
  rw [hdec, ← Finsupp.sum_single y, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun pq hpq => ?_
  rw [finsuppTensorFinsupp'_symm_single_eq_tmul_single_one, ← mul_one (y pq), ← smul_eq_mul,
    ← Finsupp.smul_single, ← TensorProduct.smul_tmul']
  exact Submodule.smul_mem _ _ (h _ _ (show y pq ≠ 0 from Finsupp.mem_support_iff.1 hpq))

variable [SetOperad.ConnectedWeight S]

omit [SetOperad.ConnectedWeight S] in
lemma single_unit_mem (one : S Unit →₀ R) (hone : one = Finsupp.single SetOperad.one 1)
    (e : Unit ≃ A) :
    Finsupp.single (SetOperad.map e SetOperad.one : S A) (1 : R)
      ∈ unitSpan R (Lin R S) one A := by
  refine Submodule.subset_span ⟨e, ?_⟩
  rw [hone]
  exact mapL_single e _ _

variable (R S) in
/-- **The identity is a coaugmentation of the decomposition cooperad** of a set operad with a
connected weight: the identity only factors through relabelled identities. -/
noncomputable instance instCoaug : Coaug R (Lin R S) where
  one := Finsupp.single SetOperad.one 1
  counit_one := Finsupp.single_eq_same
  decomp_mem {A B} _ _ _ _ i e := by
    refine decompL_mem i _ _ fun p q hpq => ?_
    have hx : SetOperad.comp i p q = SetOperad.map e SetOperad.one := by
      by_contra hne
      apply hpq
      show mapL R e (Finsupp.single SetOperad.one 1) (SetOperad.comp i p q) = 0
      rw [mapL_single, Finsupp.single_eq_of_ne hne]
    have hw := congrArg w hx
    rw [w_comp, w_map, w_one, Nat.add_eq_zero_iff] at hw
    obtain ⟨e₁, rfl⟩ := eq_unit p hw.1
    obtain ⟨e₂, rfl⟩ := eq_unit q hw.2
    exact Submodule.apply_mem_map₂ _ (single_unit_mem _ rfl e₁) (single_unit_mem _ rfl e₂)

lemma one_eq : Coaug.one (R := R) (C := Lin R S) = Finsupp.single SetOperad.one 1 :=
  rfl

/-- **An operation of weight `n` lies in the `n`-th stage of the coradical filtration.** -/
theorem single_mem_filt (t : S A) : Finsupp.single t (1 : R) ∈ filt R (Lin R S) (w t) A := by
  suffices h : ∀ n (A : Type) [Fintype A] [DecidableEq A] (t : S A), w t = n →
      Finsupp.single t (1 : R) ∈ filt R (Lin R S) n A from h _ A t rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A _ _ t ht
    cases n with
    | zero =>
      obtain ⟨e, rfl⟩ := eq_unit t ht
      exact single_unit_mem _ rfl e
    | succ m =>
      intro B D _ _ _ _ i e
      show decompL R i (mapL R e.symm (Finsupp.single t 1)) ∈ _
      rw [mapL_single]
      refine decompL_mem i _ _ fun p q hpq => ?_
      have hx : SetOperad.comp i p q = SetOperad.map e.symm t := by
        by_contra hne
        exact hpq (Finsupp.single_eq_of_ne hne)
      have hw := congrArg w hx
      rw [w_comp, w_map, ht] at hw
      by_cases hp : w p = 0
      · obtain ⟨e₁, rfl⟩ := eq_unit p hp
        exact Submodule.mem_sup_left (Submodule.mem_sup_left
          (Submodule.apply_mem_map₂ _ (single_unit_mem _ rfl e₁) Submodule.mem_top))
      by_cases hq : w q = 0
      · obtain ⟨e₂, rfl⟩ := eq_unit q hq
        exact Submodule.mem_sup_left (Submodule.mem_sup_right
          (Submodule.apply_mem_map₂ _ Submodule.mem_top (single_unit_mem _ rfl e₂)))
      refine Submodule.mem_sup_right (Submodule.apply_mem_map₂ _ ?_ ?_)
      · exact filt_le_filt (by omega) B (ih _ (by omega) B p rfl)
      · exact filt_le_filt (by omega) D (ih _ (by omega) D q rfl)

/-- **The decomposition cooperad of a set operad with a connected weight is conilpotent.** -/
theorem conilpotent : Conilpotent R (Lin R S) := by
  intro A _ _ x
  refine ⟨x.support.sup w, ?_⟩
  have key : ∀ t ∈ x.support, Finsupp.single t (x t) ∈ filt R (Lin R S) (x.support.sup w) A :=
    fun t ht => by
      rw [← mul_one (x t), ← smul_eq_mul, ← Finsupp.smul_single]
      exact Submodule.smul_mem _ _
        (filt_le_filt (Finset.le_sup (f := w) ht) A (single_mem_filt t))
  generalize x.support.sup w = n at key ⊢
  have hx : x = ∑ t ∈ x.support, Finsupp.single t (x t) := (Finsupp.sum_single x).symm
  rw [hx]
  exact Submodule.sum_mem _ key

end Lin

end Operad
