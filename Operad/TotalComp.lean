/-
# Substituting a forest, and extending a map of generators over trees

The universal property of the free operad needs to evaluate a tree in an arbitrary operad `Q`:
a vertex labelled by a `k`-ary generator becomes an element of `Q k`, and the extensions of its
`k` subtrees are substituted into its `k` slots at once. That is total composition, which the
positional convention builds from iterated partial composition.

`substF a α fo` substitutes the forest `fo` into the **last** `k` slots of `α : Q (a + k)`,
leaving the first `a` alone. Carrying the offset `a` is what makes the recursion structural:
after substituting the head tree, the remaining forest goes into the slots after it, and the
offset grows by that tree's arity.
-/
import Operad.Tree
import Operad.Constructions

universe u v w

namespace Operad

open NSOperad

variable {R : Type u} [CommRing R] {E : ℕ → Type w}
  {Q : ℕ → Type v} [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)] [NSOperad R Q]

mutual

/-- Evaluate a tree in `Q`, given values for the generators. -/
def extend (f : ∀ k, E k → Q k) : (t : Tree E) → Q t.arity
  | .leaf => one (R := R) (P := Q)
  | .node (k := k) e fo =>
      reindex R Q (show 0 + fo.arityF = (Tree.node e fo).arity by rw [Tree.arity_node]; omega)
        (substF f 0 (reindex R Q (show k = 0 + k by omega) (f k e)) fo)

/-- Substitute a forest into the last `k` slots of an operation of arity `a + k`. -/
def substF (f : ∀ k, E k → Q k) : ∀ {k : ℕ} (a : ℕ), Q (a + k) → (fo : Forest E k) →
    Q (a + fo.arityF)
  | _, _, α, .nil => α
  | _, a, α, .cons t fo =>
      reindex R Q (show a + t.arity + fo.arityF = a + (Forest.cons t fo).arityF by
          rw [Tree.arityF_cons]; omega)
        (substF f (a + t.arity)
          (comp (R := R) a _ (reindex R Q (by omega) α) (extend f t)) fo)

end

@[simp] lemma extend_leaf (f : ∀ k, E k → Q k) :
    extend (R := R) f .leaf = one (R := R) (P := Q) := rfl

/-! ### Corollas

A corolla is a single vertex with `k` leaves — the tree corresponding to a bare generator.
Evaluating one returns the generator itself, since substituting a leaf does nothing. This is the
base case of the universal property: `extend f` agrees with `f` on generators. -/

/-- The forest of `k` bare leaves. -/
def corollaF (E : ℕ → Type w) : (k : ℕ) → Forest E k
  | 0 => .nil
  | (k + 1) => .cons .leaf (corollaF E k)

/-- The corolla on a `k`-ary generator: one vertex, `k` leaves. -/
def corolla {k : ℕ} (e : E k) : Tree E := .node e (corollaF E k)

@[simp] lemma arityF_corollaF (k : ℕ) : (corollaF E k).arityF = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [corollaF, Tree.arityF_cons, Tree.arity_leaf, ih]
      omega

@[simp] lemma arity_corolla {k : ℕ} (e : E k) : (corolla e).arity = k := by
  simp only [corolla, Tree.arity_node, arityF_corollaF]

/-- Substituting bare leaves changes nothing. -/
lemma substF_corollaF (f : ∀ k, E k → Q k) : ∀ (k a : ℕ) (α : Q (a + k)),
    substF (R := R) f a α (corollaF E k)
      = reindex R Q (by rw [arityF_corollaF]) α
  | 0, a, α => by
      simp only [corollaF, substF]
      exact (reindex_self (R := R) (P := Q) _ _).symm
  | (k + 1), a, α => by
      simp only [corollaF, substF, Tree.arity_leaf]
      rw [substF_corollaF f k (a + 1)]
      have h : (comp (R := R) a k
            ((reindex R Q (show a + (k + 1) = a + 1 + k by omega)) α))
              (extend (R := R) f Tree.leaf)
          = (reindex R Q (show a + (k + 1) = a + 1 + k by omega)) α :=
        comp_one_right a k _
      refine (congrArg _ (congrArg _ h)).trans ?_
      refine (congrArg _ (reindex_reindex (R := R) (P := Q) _ _ α)).trans ?_
      exact reindex_reindex (R := R) (P := Q) _ _ α

/-- **Evaluating a corolla returns the generator.** This is the base case of the universal
property: `extend f` agrees with `f` on generators. -/
theorem extend_corolla (f : ∀ k, E k → Q k) {k : ℕ} (e : E k) :
    extend (R := R) f (corolla e) = reindex R Q (arity_corolla e).symm (f k e) := by
  simp only [corolla, extend]
  rw [substF_corollaF]
  simp only [reindex_reindex]
  rfl

end Operad
