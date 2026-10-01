# Roadmap

Written 2026-09-28. This replaces the "Roadmap" section of the README as the plan of record; the
README keeps the status table. The goal is a general library of the common tools of algebraic
operad theory, built so that each layer is usable on its own.

## Where the library stands

Updated 2026-10-01. Non-symmetric operads in the positional convention, with `Ass`, `End`, `Mag`,
`Perm`, free operads on planar trees, ideals, quotients, presentations, the weight grading,
cooperads, the total space as a pre-Lie, Lie and graded Lie algebra, cohomology, and the
convolution algebra with its pre-Lie identity. Symmetric operads by partial composition over finite
types: morphisms, isomorphisms, ideals, quotients, generated ideals and presentations by relators;
set operads, their linearization, presented and free set operads; Hadamard products; regular
operads (the symmetrization of planar set operads, left adjoint to the underlying planar operad,
with transfer of presentations). Classical operads with their presentations and their algebras:
`Com`, `Ass`, `Perm`, `Dias`, `Trias`, `ComTrias`. Infinitesimal bimodules; filtered operads and
Rees families; the endomorphism operad. Convolution operads of cochains on planar binary trees with
values in any operad, the Koszul dual of a binary quadratic presentation, twisting, and symmetric
(swap-equivariant) cochains. Shuffle tree monomials, their count, normality for quadratic leading
terms and right-comb normal forms; leading monomials of kernels. Sorry-free, 476 audited
declarations.

## Four design decisions

**1. Symmetric operads by partial composition over finite types.** A symmetric operad is a
family `P A` of modules indexed by finite types, functorial in bijections, with

    comp : P A → (i : A) → P B → P (Without A i ⊕ B)       -- Without A i = {a // a ≠ i}

a unit in `P Unit`, and associativity, units and equivariance stated as identities of `Equiv`s.
This keeps the README's choice of species indexing, where equivariance is naturality and not an
axiom about block permutations, but drops the substitution product over partitions: partial
composition needs no partitions, no direct sums over a transported index, and no arithmetic. The
positional `NSOperad` stays as the planar and computational layer, and every symmetric operad has
an underlying one, `n ↦ P (Fin n)`, through the order-preserving
`Without (Fin (a+1+b)) a ⊕ Fin n ≃ Fin (a+n+b)`.

**2. Set operads as the combinatorial layer.** Many operads in practice are linearizations of set
operads — `Com`, `Ass`, `Perm`, `NAP`, the operads of Loday and Ronco's trialgebras and of
Vallette's commutative trialgebras, and many from Giraudo's book — and their relations are
identifications of monomials. The library gets set operads, their linearization into linear
operads with the adjunction `Hom(Lin S, Q) ≅ Hom_set(S, U Q)`, free set operads on set species
(a rooted tree with labelled leaves and no unary vertices is a hierarchy on its leaves, and has no
automorphisms, so the free object needs no coinvariants), congruences, and presentations. Normal
forms then become bijections of sets, provable by induction on trees.

**3. Deformation theory in low weight before general Koszul duality.** The convolution algebra
first ungraded, then graded with Koszul signs; Koszul dual cooperads of binary quadratic data
through weight three; twisted complexes and their first cohomology groups. General-weight Koszul
duality, bar–cobar and Gröbner bases come after, on top of the same objects.

**4. Finite computations by certificates.** Explicit ranks and relator evaluations are proved by
kernel-checked certificates (explicit kernel vectors, left inverses on complements), never by
`native_decide`.

## Work packages

### Phase 1 — foundations

| | content | status |
|---|---|---|
| L1 | Convolution: the pre-Lie identity for `⋆c`, Jacobi, `LieRing` and `LieAlgebra` on `Conv` | **done** (`ConvolutionPreLie.lean`) |
| L2 | Symmetric operads by partial composition: the class, morphisms, `Com`, `Perm`, `Ass`, `End`; the underlying non-symmetric operad, and its agreement with the existing `Perm` | **class, morphisms, `Com`, `Perm`, the underlying non-symmetric operad and the `Perm` comparison done** (`Sym.lean`, `SymNS.lean`); **the endomorphism operad of a module and algebras over a symmetric operad done** (`EndOperad.lean`); **`Ass` done**: the linearization of the set operad of linear orders, its augmentation to `Com`, and the planar `Ass` as the standard orders (`SymAss.lean`) |
| L3 | Set operads (symmetric and planar), linearization and its adjunction, free set operads on set species, congruences, presentations and their universal property, a normal-form toolkit | **symmetric part done**: set operads, `Lin` and the adjunction (`SetOperad.lean`); presented and free set operads with their universal properties, also into operads in modules (`SetPresentation.lean`); the binary calculus and the step from arity-three relators to generic identities (`SetBinary.lean`); generalized associativity and commutativity, `ComSet` presented by one commutative associative generator (`ComSet.lean`); `Perm` has no nonzero commutative associative element (`PermSet.lean`). **Planar part done**: planar set operads, their linearization, the underlying planar set operad of a symmetric one, and bijective morphisms as isomorphisms (`NSSet.lean`); presentations with their universal property (`NSSetPresentation.lean`); a calculus of operations of all arities without reindexing, the step from arity-three relators to generic identities, and right-comb normal forms for presentations closed under rotation (`NSSetArr.lean`); isomorphisms of non-symmetric operads, the underlying non-symmetric set operad and the linearization adjunction, linearization of morphisms, and the underlying non-symmetric operad of a linearization (`NSLinear.lean`) |
| L4 | Suboperads, ideals, quotients and kernels for symmetric operads | **done**: ideals and kernels (`SymIdeal.lean`: `SymOperadIdeal`, `SymOperadHom.ker`, `ker Σ` in `Perm`); quotients, their universal property, and the first isomorphism theorem (`SymQuot.lean`); generated ideals and operads presented by relators (`SymPresentation.lean`); suboperads and images (`Filtration.lean`) |
| L5 | Infinitesimal bimodules over an operad | **done** (`InfBimodule.lean`): the class, `self`, restriction along a morphism, morphisms |
| L6 | Filtered operads, the associated graded, base change and specialization over `R[ħ]` | **started**: symmetric suboperads, images of morphisms, filtered symmetric operads, the degree-zero suboperad, transport along surjective morphisms, and the filtration of a linearization by a subadditive weight (`Filtration.lean`); **for a weighted set operad, the twisted linearizations `TwLin R W h` (composites scaled by `h` to the weight they drop), with the fiber `h = 1` the linearization, the fiber `h = 0` the associated graded `Gr` (sign automorphism, weight-zero evaluation), and the Rees family over `R[X]` with its specializations, surjective with kernel `(X - c)` (`Rees.lean`)**; isomorphisms of symmetric operads (`SymIso.lean`) |

### Phase 2 — convolution and Koszul duality in low weight

| | content | status |
|---|---|---|
| L7 | The graded convolution algebra of a weight-graded cooperad: graded pre-Lie, graded Jacobi, twisting, `d_f² = [f ⋆ f, −]`, Maurer–Cartan elements, coefficients in an ideal | **binary case done by reduction to the total space**: planar binary trees with unique factorization (`BinaryTree.lean`), and the cochains on trees with values in any non-symmetric operad form a non-symmetric operad, the convolution operad of the cofree cooperad (`TreeConv.lean`); its signed total space is the convolution graded pre-Lie algebra, so graded Jacobi, twisting and the cohomology of `Cohomology.lean` apply to it; cochains with values in an ideal form an ideal (`TConv.valuedIn`) |
| L8 | Binary quadratic data; the Koszul dual cooperad (planar), through weight three and then in every weight | **started**: evaluation of cochains on chains, slices, and the annihilator of a slice-closed collection as an operad ideal; the Koszul dual of a binary quadratic presentation in every arity, slice-closed (`KoszulDual.lean`); the low-weight calculus — the trees of arity two to four by name (told apart by `simp`), `⋆ₛ` and the bracket on them, and the weight-(1,2) bracket evaluated along slices (`LowWeight.lean`), with `Perm`'s compositions in arities up to four as vectors and its sum-zero ideal (`PermLow.lean`); **twisting on the Koszul dual**: morphisms preserve `⋆ₛ` and the bracket (`DGHom.lean`), so at a binary cochain whose square vanishes on the Koszul dual the twisted differential squares to zero there (`KoszulTwist.lean`); mirror images of planar trees (`Mirror.lean`) |
| L9 | The symmetric version, with equivariant cochains | **done for binary generators**: symmetric cochains on planar binary trees, equivariant under swaps at vertices (`TConv.IsSymm`), are closed under the signed convolution product and the bracket (`isSymm_sstar`, `isSymm_gbracket`), so the symmetric convolution algebra is a graded sub-pre-Lie algebra of the planar one; the twisting identity `⁅T, ⁅T, x⁆⁆ = ⁅T ⋆ₛ T, x⁆` and coefficients in an ideal of a symmetric operad (`SymTreeConv.lean`) |
| L10 | The twisted complex of a morphism out of a quadratic operad; `H¹`, `H²` | planned |

### Phase 3 — the classical operads and their algebras

`Lie` (as the suboperad of `Ass` generated by the commutator, and by its presentation), `PreLie`
(rooted trees), `Pois`, `Dias`, `Dend`, `Trias`; algebras over symmetric operads, with the
theorems that `Com`-, `Perm`-, `Lie`-algebras are what they should be; the Koszul dual operad
`P^!` of a quadratic operad and the classical pairs (`Com`/`Lie`, `Ass`/`Ass`, `Perm`/`PreLie`).

**Started** (`SetHadamard.lean`): Hadamard products of set operads, with their universal property;
`Perm` as the linearization of the pointed sets; `ComTrias`; `Dias` and `Trias` as linearized
Hadamard products with the linear orders, with their defining relations, their dimensions
`n · n!` and `(2ⁿ - 1) · n!`, and the morphism `Dias → Trias`. **Regular operads**
(`Regular.lean`): the symmetrization of a planar set operad, left adjoint to the underlying planar
operad, the Hadamard product with the linear orders as a symmetrization, and the transfer of planar
presentations to symmetric ones. **Presentations of `Dias` and `Trias`** (`DiasTrias.lean`):
Loday's five relations and Loday–Ronco's eleven, through planar right-comb normal forms; their
universal properties as operads in modules. **The presentation of `Perm`** (`PermPres.lean`), by
one binary operation and the two permutative relations; **of `Ass`** (`AssPres.lean`), as a
regular operad; **of `ComTrias`** (`ComTriasPres.lean`), Vallette's. **Algebras**
(`Algebras.lean`): `Com`-, `Perm`-, `Ass`-, `Dias`-, `Trias`- and `ComTrias`-algebras are what they
should be. **Binary quadratic operads** (`BinaryQuadratic.lean`): the free operad on binary
generators, its two-fold monomials and their values in endomorphism operads, the operad presented by
relators of arity two and three and its algebras; `Lie`, `PreLie`, `Leib`, `Zinb`, `Dend`, `Pois`
with their algebras. Still to do: bases of the free operad (tree monomials) and the Koszul dual
operad.

### Phase 4 — general theory

| | content |
|---|---|
| L11 | Shuffle operads and the forgetful functor from symmetric operads; tree monomials, admissible orders, Gröbner bases; the Dotsenko–Khoroshkin criterion. **Started**: shuffle tree monomials, their count `(2n - 3)!! \|E\|ⁿ⁻¹`, windows and normality for quadratic leading terms, the path-lexicographic key, right-comb normal forms (`ShuffleTree.lean`); leading monomials of the kernel of a linearized map (`LeadingTerm.lean`); substitution at a window and its compatibility with the path-lexicographic key (`ShuffleSubst.lean`); the division algorithm and a Gröbner criterion through a model of the quotient (`LeadingTerm.lean`) |
| L12 | Differential graded operads, bar and cobar constructions, Koszulness, the deformation complex of a morphism and of an operad |
| L13 | `L∞`-algebras and the homotopy transfer theorem |
| L14 | The general free symmetric operad on a linear species, and its comparison with the set-operad construction |

### Continuing

Mathlib's linters, a scheduled build against Mathlib master, `doc-gen4` documentation, and the
audit kept current: every headline declaration in `Audit.lean`, reporting a sublist of
`propext`, `Classical.choice`, `Quot.sound`.
