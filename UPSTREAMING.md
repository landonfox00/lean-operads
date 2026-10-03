# Upstreaming guide

How the foundations of this library could move to Mathlib, and in which order. Nothing here has
been submitted; the guide records what is self-contained, what Mathlib already has, and what would
have to change to meet Mathlib's conventions.

## Self-contained candidates, needing only Mathlib

These files import nothing from the library and can be proposed as they stand, after the usual
renaming and generalization.

| file | content | Mathlib home | changes to make |
|---|---|---|---|
| `Operad/Perturbation.lean` | homology of a square-zero endomorphism, chain homotopies, contractions, the homological perturbation lemma | `Mathlib/Algebra/Homology/` | state for `HomologicalComplex` (or for a differential of a fixed degree on a graded object), and recover the present statements as the ungraded case; the key identity `d A + A d + A ι π A = 0` and the five contraction identities transfer unchanged |
| `Operad/MultilinearQuot.lean` | multilinear maps out of quotients of direct sums of `Finsupp`s | `Mathlib/LinearAlgebra/Multilinear/` | the lemmas are about `MultilinearMap` and `Submodule.Quotient` only |
| `Operad/Diamond.lean`, `Operad/DiamondCtx.lean`, `Operad/DiamondWords.lean`, `Operad/PBW.lean` | Bergman's diamond lemma (linear rewriting, rules in contexts, free algebras) and **the Poincaré–Birkhoff–Witt theorem** for Lie algebras with a basis, with the injectivity of `g → U g` for free `g` | `Mathlib/Algebra/Lie/UniversalEnveloping.lean`, new `Mathlib/Algebra/FreeAlgebra/Diamond.lean` | Mathlib's `Lie/Free.lean` and `Lie/SerreConstruction.lean` note that PBW is missing; state the words lemma for `FreeAlgebra R I` through `FreeAlgebra.equivMonoidAlgebraFreeMonoid` and the degree-lexicographic order from Mathlib's monomial orders; `PBW.lean` depends only on the three diamond files and on `STree.DegLex` (to be moved next to the words) |
| `Operad/GerBV.lean` | BV algebras and Koszul's theorem (the derived bracket is a Gerstenhaber bracket) | new `Mathlib/Algebra/BV.lean` | replace the involution and `Bool` parities by a `ZMod 2`-grading (`DirectSum.Decomposition`) or a `SuperModule` class if one lands; the proofs are case analyses on parities followed by `linear_combination (norm := module)` and port directly |

## Operads

The rest depends on the operad classes. Before any of it can move, Mathlib needs to settle the
definition of an operad. The choices made here, and the reasons for them, are in `ROADMAP.md`
("Four design decisions"); the points a Mathlib review would raise:

* **Species-style symmetric operads** (`Operad/Sym.lean`): operations indexed by finite types with
  partial compositions `P A → P B → P (Without A i ⊕ B)` and relabellings along bijections. This
  avoids `Fin` arithmetic and makes equivariance a naturality statement. The alternative, a
  monoid in symmetric sequences for the composition product, is the categorical definition; the
  equivalence with total (May) composition is `Operad/MayOperad.lean` and `Operad/MayClass.lean`.
* **Non-symmetric operads** (`Operad/Basic.lean`): positional compositions with `reindex`; the
  endomorphism operad `End` is built so that its compositions are definitionally transparent.
  Mathlib's `MultilinearMap.compMultilinearMap` already gives total composition and is the natural
  basis for an upstream `End`.
* **Instances on families**: the library repeatedly needs instances on type families such as
  `Shuf`, `OneCol`, `CycOperad.Und` and `DGOperad.HomologyOp`; these are definitions with explicit
  instances rather than abbreviations, because type class resolution does not unify through
  abbreviations whose instance arguments are themselves derived instances.

## A suggested order of pull requests

1. The homological perturbation lemma (no dependencies); the diamond lemma and the
   Poincaré–Birkhoff–Witt theorem (no dependencies beyond the degree-lexicographic order).
2. Multilinear maps out of quotients (no dependencies).
3. BV and Gerstenhaber algebras (no dependencies once a parity convention is chosen).
4. Non-symmetric operads, the endomorphism operad, algebras over operads; `Ass`-algebras are
   associative algebras.
5. Symmetric operads in the species convention, morphisms, ideals, quotients and presentations;
   `Com`-algebras are commutative algebras and the free `Com`-algebra is `SymmetricAlgebra`
   (`Operad/ComAlgebra.lean`, which only uses Mathlib's `SymmetricAlgebra` API).
6. The Schur functor and free algebras over an operad, with their universal property.
7. Graded and dg operads, the homology operad; the Koszul-sign calculus of multilinear maps and
   A∞-structures with their Hochschild differential.
8. Shuffle operads and the Gröbner-basis machinery, which is the largest and most specialised
   part and should come last.

## Conventions already followed

Mathlib's linters pass on the whole library (`lake exe runLinter Operad`), lines are at most 100
characters, every definition has a docstring, and the axiom audit `Audit.lean` reports
only `propext`, `Classical.choice` and `Quot.sound`. A scheduled CI job builds against Mathlib
master to catch drift.
