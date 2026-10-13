/-
# The Schur functor of an operad

The Schur functor of a linear species `P` at a module `V` is
`S(P, V) = ⊕ₙ P(n) ⊗_{Σₙ} V^{⊗n}`: an operation with `n` inputs, together with `n` elements of
`V`, up to linearity in the operation, multilinearity in the elements, and the action of the
permutations, which moves the inputs of the operation and the elements together. It is presented
here as a module (`Schur`): the free module on generators `(p, v)` of each arity `n`
(`SchurGen`), modulo the five kinds of relations (`schurRelSet`).

* `Schur.mk R n p v` is the class of a generator; it is linear in `p`, multilinear in `v`
  (`Schur.mkML`), and `mk R n (σ · p) v = mk R n p (v ∘ σ)` (`Schur.mk_map`).
* `Schur.mkA R p v` is the class of an operation with any finite type of inputs `A`, through a
  numbering of `A`; it does not depend on the numbering (`Schur.mkA_chart`), and
  `mkA R (e · p) v = mkA R p (v ∘ e)` (`Schur.mkA_map`).
* **Linear maps out of the Schur functor** are the families of maps `P(n) → Mult(V^n, W)`, linear
  in the operation and compatible with the permutations (`Schur.lift`, `Schur.lift_mk`), and are
  determined by their values on generators (`Schur.hom_ext`).
-/
import Operad.MultilinearQuot
import Operad.SpeciesOp

universe u v w x

namespace Operad

open DirectSum Function

section Schur

variable (R : Type u) [CommRing R]
  (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymSpecies R P]
  (V : Type v) [AddCommGroup V] [Module R V]

/-- The generators of the Schur functor in arity `n`: an operation with inputs `Fin n` and `n`
elements of `V`. -/
abbrev SchurGen (n : ℕ) := P (Fin n) × (Fin n → V)

/-- The free module on the generators, arity by arity. -/
noncomputable abbrev SchurPre := ⨁ n : ℕ, (SchurGen P V n →₀ R)

-- Declared directly: the search for the quotient does not find them through the direct sum.
noncomputable instance SchurPre.instAddCommGroup : AddCommGroup (SchurPre R P V) :=
  DirectSum.instAddCommGroup _

noncomputable instance SchurPre.instModule : Module R (SchurPre R P V) :=
  DirectSum.instModule

/-- **The relations of the Schur functor** in arity `n`: linearity in the operation,
multilinearity in the elements, and the action of the permutations. -/
def schurRelSet (n : ℕ) : Set (SchurGen P V n →₀ R) :=
  {x | ∃ (p p' : P (Fin n)) (v : Fin n → V), x = Finsupp.single (p + p', v) 1
      - Finsupp.single (p, v) 1 - Finsupp.single (p', v) 1} ∪
  {x | ∃ (c : R) (p : P (Fin n)) (v : Fin n → V), x = Finsupp.single (c • p, v) 1
      - c • Finsupp.single (p, v) 1} ∪
  {x | ∃ (p : P (Fin n)) (v : Fin n → V) (i : Fin n) (a b : V),
      x = Finsupp.single (p, update v i (a + b)) 1 - Finsupp.single (p, update v i a) 1
        - Finsupp.single (p, update v i b) 1} ∪
  {x | ∃ (p : P (Fin n)) (v : Fin n → V) (i : Fin n) (c : R) (a : V),
      x = Finsupp.single (p, update v i (c • a)) 1 - c • Finsupp.single (p, update v i a) 1} ∪
  {x | ∃ (σ : Fin n ≃ Fin n) (p : P (Fin n)) (v : Fin n → V),
      x = Finsupp.single (SymSpecies.map (R := R) σ p, v) 1 - Finsupp.single (p, v ∘ σ) 1}

/-- The submodule of relations. -/
noncomputable def schurRel : Submodule R (SchurPre R P V) :=
  Submodule.span R (⋃ n, lof R ℕ (fun n => SchurGen P V n →₀ R) n '' schurRelSet R P V n)

/-- **The Schur functor** of `P` at `V`: `⊕ₙ P(n) ⊗_{Σₙ} V^{⊗n}`. -/
noncomputable abbrev Schur := SchurPre R P V ⧸ schurRel R P V

namespace Schur

variable {R P V}

variable (R) in
/-- **The class of a generator**: an operation with inputs `Fin n` and `n` elements. -/
noncomputable def mk (n : ℕ) (p : P (Fin n)) (v : Fin n → V) : Schur R P V :=
  (schurRel R P V).mkQ (lof R ℕ (fun n => SchurGen P V n →₀ R) n (Finsupp.single (p, v) 1))

lemma rel_mem {n : ℕ} {x : SchurGen P V n →₀ R} (hx : x ∈ schurRelSet R P V n) :
    lof R ℕ (fun n => SchurGen P V n →₀ R) n x ∈ schurRel R P V :=
  Submodule.subset_span (Set.mem_iUnion.2 ⟨n, x, hx, rfl⟩)

lemma mk_sub_eq {n : ℕ} {x : SchurGen P V n →₀ R} (hx : x ∈ schurRelSet R P V n) :
    (schurRel R P V).mkQ (lof R ℕ (fun n => SchurGen P V n →₀ R) n x) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 (rel_mem hx)

lemma mk_add (n : ℕ) (p p' : P (Fin n)) (v : Fin n → V) :
    mk R n (p + p') v = mk R n p v + mk R n p' v := by
  have := mk_sub_eq (R := R) (Or.inl (Or.inl (Or.inl (Or.inl ⟨p, p', v, rfl⟩))))
  rw [map_sub, map_sub, map_sub, map_sub, sub_sub, sub_eq_zero] at this
  exact this

lemma mk_smul (n : ℕ) (c : R) (p : P (Fin n)) (v : Fin n → V) :
    mk R n (c • p) v = c • mk R n p v := by
  have := mk_sub_eq (R := R) (Or.inl (Or.inl (Or.inl (Or.inr ⟨c, p, v, rfl⟩))))
  rw [map_sub, map_sub, map_smul, map_smul, sub_eq_zero] at this
  exact this

lemma mk_update_add (n : ℕ) (p : P (Fin n)) (v : Fin n → V) (i : Fin n) (a b : V) :
    mk R n p (update v i (a + b)) = mk R n p (update v i a) + mk R n p (update v i b) := by
  have := mk_sub_eq (R := R) (Or.inl (Or.inl (Or.inr ⟨p, v, i, a, b, rfl⟩)))
  rw [map_sub, map_sub, map_sub, map_sub, sub_sub, sub_eq_zero] at this
  exact this

lemma mk_update_smul (n : ℕ) (p : P (Fin n)) (v : Fin n → V) (i : Fin n) (c : R) (a : V) :
    mk R n p (update v i (c • a)) = c • mk R n p (update v i a) := by
  have := mk_sub_eq (R := R) (Or.inl (Or.inr ⟨p, v, i, c, a, rfl⟩))
  rw [map_sub, map_sub, map_smul, map_smul, sub_eq_zero] at this
  exact this

/-- **Permutations move the inputs and the elements together.** -/
lemma mk_map (n : ℕ) (σ : Fin n ≃ Fin n) (p : P (Fin n)) (v : Fin n → V) :
    mk R n (SymSpecies.map (R := R) σ p) v = mk R n p (v ∘ σ) := by
  have := mk_sub_eq (R := R) (Or.inr ⟨σ, p, v, rfl⟩)
  rw [map_sub, map_sub, sub_eq_zero] at this
  exact this

variable (R) in
/-- The class of a generator, multilinear in the elements. -/
noncomputable def mkML (n : ℕ) (p : P (Fin n)) :
    MultilinearMap R (fun _ : Fin n => V) (Schur R P V)
    where
  toFun := mk R n p
  map_update_add' v i a b := by
    convert mk_update_add n p v i a b
  map_update_smul' v i c a := by
    convert mk_update_smul n p v i c a

/-! ### Operations with any finite type of inputs -/

variable (R) in
/-- **The class of an operation with inputs `A`** and a family of elements, through a numbering
of `A`. -/
noncomputable def mkA {A : Type} [Fintype A] [DecidableEq A] (p : P A) (v : A → V) :
    Schur R P V :=
  mk R (Fintype.card A) (SymSpecies.map (R := R) (Fintype.equivFin A) p)
    (v ∘ (Fintype.equivFin A).symm)

/-- **The class does not depend on the numbering.** -/
lemma mkA_chart {A : Type} [Fintype A] [DecidableEq A] {n : ℕ} (φ : A ≃ Fin n) (p : P A)
    (v : A → V) : mkA R p v = mk R n (SymSpecies.map (R := R) φ p) (v ∘ φ.symm) := by
  have hn : n = Fintype.card A := by simpa using (Fintype.card_congr φ).symm
  subst hn
  set ψ := Fintype.equivFin A
  have : SymSpecies.map (R := R) φ p = SymSpecies.map (R := R) (ψ.symm.trans φ)
      (SymSpecies.map (R := R) ψ p) := by
    rw [← SymSpecies.map_trans (R := R), ← Equiv.trans_assoc, Equiv.self_trans_symm,
      Equiv.refl_trans]
  rw [mkA, this, mk_map]
  congr 1
  funext k
  simp [ψ]

lemma mkA_fin {n : ℕ} (p : P (Fin n)) (v : Fin n → V) : mkA R p v = mk R n p v := by
  rw [mkA_chart (Equiv.refl _), SymSpecies.map_refl (R := R)]
  rfl

/-- **Relabelling the inputs** of the operation relabels the elements. -/
lemma mkA_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    (p : P A) (v : B → V) : mkA R (SymSpecies.map (R := R) e p) v = mkA R p (v ∘ e) := by
  rw [mkA, ← SymSpecies.map_trans (R := R), mkA_chart (e.trans (Fintype.equivFin B))]
  congr 1
  funext k
  simp

lemma mkA_add {A : Type} [Fintype A] [DecidableEq A] (p p' : P A) (v : A → V) :
    mkA R (p + p') v = mkA R p v + mkA R p' v := by
  rw [mkA, mkA, mkA, map_add, mk_add]

lemma mkA_smul {A : Type} [Fintype A] [DecidableEq A] (c : R) (p : P A) (v : A → V) :
    mkA R (c • p) v = c • mkA R p v := by
  rw [mkA, mkA, map_smul, mk_smul]

lemma mkA_update_add {A : Type} [Fintype A] [DecidableEq A] (p : P A) (v : A → V) (a : A)
    (x y : V) : mkA R p (update v a (x + y)) = mkA R p (update v a x) + mkA R p (update v a y) := by
  have e : ∀ z : V, update v a z ∘ (Fintype.equivFin A).symm
      = update (v ∘ (Fintype.equivFin A).symm) (Fintype.equivFin A a) z := fun z => by
    funext k
    by_cases hk : k = Fintype.equivFin A a
    · subst hk
      rw [comp_apply, Equiv.symm_apply_apply, update_self, update_self]
    · rw [comp_apply, update_of_ne hk, update_of_ne (fun h => hk (by rw [← h]; simp))]
      rfl
  rw [mkA, mkA, mkA, e, e, e, mk_update_add]

lemma mkA_update_smul {A : Type} [Fintype A] [DecidableEq A] (p : P A) (v : A → V) (a : A)
    (c : R) (x : V) : mkA R p (update v a (c • x)) = c • mkA R p (update v a x) := by
  have e : ∀ z : V, update v a z ∘ (Fintype.equivFin A).symm
      = update (v ∘ (Fintype.equivFin A).symm) (Fintype.equivFin A a) z := fun z => by
    funext k
    by_cases hk : k = Fintype.equivFin A a
    · subst hk
      rw [comp_apply, Equiv.symm_apply_apply, update_self, update_self]
    · rw [comp_apply, update_of_ne hk, update_of_ne (fun h => hk (by rw [← h]; simp))]
      rfl
  rw [mkA, mkA, e, e, mk_update_smul]

/-! ### Linear maps out of the Schur functor -/

variable {W : Type x} [AddCommGroup W] [Module R W]

/-- The condition on a family of maps to define a linear map out of the Schur functor:
compatibility with the permutations. -/
def Compatible (f : ∀ n : ℕ, P (Fin n) →ₗ[R] MultilinearMap R (fun _ : Fin n => V) W) : Prop :=
  ∀ (n : ℕ) (σ : Fin n ≃ Fin n) (p : P (Fin n)) (v : Fin n → V),
    f n (SymSpecies.map (R := R) σ p) v = f n p (v ∘ σ)

/-- The linear map on the free module of generators. -/
noncomputable def liftPre (f : ∀ n : ℕ, P (Fin n) →ₗ[R] MultilinearMap R (fun _ : Fin n => V) W) :
    SchurPre R P V →ₗ[R] W :=
  toModule R ℕ W fun n => Finsupp.lift W R (SchurGen P V n) fun g => f n g.1 g.2

omit [SymSpecies R P] in
lemma liftPre_gen (f : ∀ n : ℕ, P (Fin n) →ₗ[R] MultilinearMap R (fun _ : Fin n => V) W)
    (n : ℕ) (p : P (Fin n)) (v : Fin n → V) (c : R) :
    liftPre f (lof R ℕ (fun n => SchurGen P V n →₀ R) n (Finsupp.single (p, v) c))
      = c • f n p v := by
  simp [liftPre]

/-- **The linear map out of the Schur functor** defined by a compatible family. -/
noncomputable def lift (f : ∀ n : ℕ, P (Fin n) →ₗ[R] MultilinearMap R (fun _ : Fin n => V) W)
    (hf : Compatible f) : Schur R P V →ₗ[R] W :=
  (schurRel R P V).liftQ (liftPre f) <| (Submodule.span_le).2 fun x hx => by
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
    obtain ⟨y, hy, rfl⟩ := hn
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    rcases hy with ((((⟨p, p', v, rfl⟩ | ⟨c, p, v, rfl⟩) | ⟨p, v, i, a, b, rfl⟩) |
      ⟨p, v, i, c, a, rfl⟩) | ⟨σ, p, v, rfl⟩)
    · simp only [map_sub, liftPre_gen, one_smul, map_add, MultilinearMap.add_apply]
      abel
    · simp only [map_sub, map_smul, liftPre_gen, one_smul, MultilinearMap.smul_apply, sub_self]
    · simp only [map_sub, liftPre_gen, one_smul, MultilinearMap.map_update_add]
      abel
    · simp only [map_sub, map_smul, liftPre_gen, one_smul, MultilinearMap.map_update_smul,
        sub_self]
    · simp only [map_sub, liftPre_gen, one_smul, hf n σ p v, sub_self]

@[simp] lemma lift_mk (f : ∀ n : ℕ, P (Fin n) →ₗ[R] MultilinearMap R (fun _ : Fin n => V) W)
    (hf : Compatible f) (n : ℕ) (p : P (Fin n)) (v : Fin n → V) :
    lift f hf (mk R n p v) = f n p v := by
  simp [lift, mk, liftPre]

/-- **Linear maps out of the Schur functor agree when they agree on generators.** -/
theorem hom_ext {φ ψ : Schur R P V →ₗ[R] W} (h : ∀ (n : ℕ) (p : P (Fin n)) (v : Fin n → V),
    φ (mk R n p v) = ψ (mk R n p v)) : φ = ψ := by
  refine Submodule.linearMap_qext _ (DirectSum.linearMap_ext R fun n => ?_)
  exact Finsupp.lhom_ext fun g c => by
    have := h n g.1 g.2
    simp only [mk, Submodule.mkQ_apply] at this
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [← mul_one c, ← smul_eq_mul, ← Finsupp.smul_single, map_smul,
      Submodule.Quotient.mk_smul, map_smul, map_smul, this]

end Schur

end Schur

end Operad
