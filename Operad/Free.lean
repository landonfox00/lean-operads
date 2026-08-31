/-
# The free non-symmetric operad on a collection of generators

`Operad.Tree` proved the four operad laws for planar trees under grafting. This file linearises:
`Free R E n` is the free `R`-module on trees of arity `n`, and grafting extends bilinearly to
the operadic composition.

Carrying the arity as a *proof* rather than an index pays off here. Grafting at the positional
slot `a` produces a tree of arity `(a + 1 + b) - 1 + n`, which is not syntactically `a + n + b`;
because the arity sits in a `Subtype` proof field rather than in the type, the two are reconciled
by supplying a different proof, with no transport at all.
-/
import Operad.Tree
import Operad.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Span.Basic

universe u v

namespace Operad

/-- A planar tree together with a proof that it has arity `n`. -/
def TreeOfArity (E : ℕ → Type v) (n : ℕ) : Type v := {t : Tree E // t.arity = n}

namespace TreeOfArity

variable {E : ℕ → Type v}

@[ext] lemma ext {n : ℕ} {s t : TreeOfArity E n} (h : s.val = t.val) : s = t := Subtype.ext h

/-- The operadic identity: the bare leaf. -/
def one : TreeOfArity E 1 := ⟨.leaf, rfl⟩

/-- Grafting at the positional slot `a`: the slot sits after `a` leaves and before `b`. -/
def graft (a b : ℕ) {n : ℕ} (t : TreeOfArity E (a + 1 + b)) (s : TreeOfArity E n) :
    TreeOfArity E (a + n + b) :=
  ⟨t.val.graft a s.val, by
    have ht := t.property
    have hs := s.property
    rw [Tree.arity_graft t.val a s.val (by omega), ht, hs]
    omega⟩

@[simp] lemma graft_val (a b : ℕ) {n : ℕ} (t : TreeOfArity E (a + 1 + b)) (s : TreeOfArity E n) :
    (graft a b t s).val = t.val.graft a s.val := rfl

end TreeOfArity

/-- The free non-symmetric operad on the collection `E`: the free `R`-module on planar trees
of each arity, with vertices labelled by `E`. -/
abbrev Free (R : Type u) [CommRing R] (E : ℕ → Type v) (n : ℕ) : Type (max u v) :=
  TreeOfArity E n →₀ R

namespace Free

variable {R : Type u} [CommRing R] {E : ℕ → Type v}

/-- The basis element attached to a tree. -/
noncomputable def gen {n : ℕ} (t : TreeOfArity E n) : Free R E n := Finsupp.single t 1

lemma smul_gen {n : ℕ} (t : TreeOfArity E n) (r : R) :
    r • gen (R := R) t = Finsupp.single t r := by
  rw [gen, Finsupp.smul_single, smul_eq_mul, mul_one]

lemma gen_def {n : ℕ} (t : TreeOfArity E n) : gen (R := R) t = Finsupp.single t 1 := rfl

/-- Grafting, extended bilinearly. -/
noncomputable def compL (a b : ℕ) {n : ℕ} :
    Free R E (a + 1 + b) →ₗ[R] Free R E n →ₗ[R] Free R E (a + n + b) :=
  Finsupp.lsum R fun t =>
    LinearMap.toSpanSingleton R _ <|
      Finsupp.lsum R fun s =>
        LinearMap.toSpanSingleton R _ (gen (R := R) (TreeOfArity.graft a b t s))

@[simp] lemma compL_gen (a b : ℕ) {n : ℕ} (t : TreeOfArity E (a + 1 + b))
    (s : TreeOfArity E n) :
    compL (R := R) a b (gen t) (gen s) = gen (TreeOfArity.graft a b t s) := by
  simp only [compL, gen, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply_one]

/-- Reindexing a generator only changes the arity proof it carries. -/
lemma reindex_gen {m n : ℕ} (h : m = n) (x : TreeOfArity E m) :
    reindex R (Free R E) h (gen x) = gen ⟨x.val, by rw [x.property, h]⟩ := by
  subst h
  rw [reindex_self]
  exact congrArg gen (Subtype.ext rfl)


lemma compL_single (a b : ℕ) {n : ℕ} (t : TreeOfArity E (a + 1 + b)) (r : R)
    (s : TreeOfArity E n) (r' : R) :
    compL (R := R) a b (Finsupp.single t r) (Finsupp.single s r')
      = Finsupp.single (TreeOfArity.graft a b t s) (r * r') := by
  rw [← smul_gen, ← smul_gen, map_smul, map_smul, LinearMap.smul_apply, compL_gen, smul_smul,
    smul_gen, mul_comm]

/-- Reindexing a `single` only changes the arity proof the tree carries. -/
lemma reindex_single {m n : ℕ} (h : m = n) (x : TreeOfArity E m) (r : R) :
    reindex R (Free R E) h (Finsupp.single x r)
      = Finsupp.single ⟨x.val, by rw [x.property, h]⟩ r := by
  subst h
  rw [reindex_self]
  exact congrArg (fun y => Finsupp.single y r) (Subtype.ext rfl)

/-- **The free non-symmetric operad on `E`.** Each axiom is the corresponding tree-level law of
`Operad.Tree`, extended from generators by linearity. -/
noncomputable instance : NSOperad R (Free R E) where
  one := gen TreeOfArity.one
  comp a b := compL a b
  comp_one_right := by
    intro a b α
    induction α using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]
    | single t r =>
        rw [show (gen TreeOfArity.one : Free R E 1) = Finsupp.single TreeOfArity.one 1 from rfl,
          compL_single, mul_one]
        exact congrArg (fun y => Finsupp.single y r) (Subtype.ext (Tree.graft_leaf_right t.val a))
  comp_one_left := by
    intro n α
    induction α using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add, hf, hg]
    | single s r =>
        rw [show (gen TreeOfArity.one : Free R E 1) = Finsupp.single TreeOfArity.one 1 from rfl,
          compL_single, one_mul, reindex_single]
        exact congrArg (fun y => Finsupp.single y r) (Subtype.ext rfl)
  comp_assoc_seq := by
    intro a b c d p α β γ
    induction α using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]
    | single t r =>
      induction β using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]
      | single s r' =>
        induction γ using Finsupp.induction_linear with
        | zero => simp
        | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]
        | single w r'' =>
          simp only [compL_single, reindex_single]
          congr 1
          · exact Subtype.ext
              (Tree.graft_graft_seq t.val a s.val c w.val (by have := t.property; omega)
                (by have := s.property; omega))
          · ring
  comp_assoc_par := by
    intro a b c n p α β γ
    induction α using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]
    | single t r =>
      induction β using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]
      | single s r' =>
        induction γ using Finsupp.induction_linear with
        | zero => simp
        | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]
        | single w r'' =>
          simp only [compL_single, reindex_single]
          congr 1
          · have ht := t.property
            have hs := s.property
            have key := Tree.graft_graft_par t.val a s.val (a + 1 + b) w.val (by omega)
              (by omega)
            rw [hs, show a + 1 + b - 1 + n = a + n + b by omega] at key
            exact Subtype.ext key
          · ring

end Free

end Operad
