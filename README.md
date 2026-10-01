# A Lean 4 operad library

Mathlib has **no operad theory** — as of master `b87b4e8924` (2026-08-30) the string "operad"
occurs exactly twice in the whole library, both times in a bibliography entry. Five earlier
attempts to add operads were opened and closed (mathlib4 #20133, #20134, #20138, #20141, #23459),
with maintainers noting that "operads will be a challenge to get working in the right generality."

This is a local library, so it is free to make a definite choice and build on it.

## Build

Toolchain `leanprover/lean4:v4.30.0`, pinned in `lean-toolchain`.

```bash
lake exe cache get
lake build
```

`Audit.lean` is not part of the library target; run it separately to reproduce the axiom audit.

## The design decision that makes this tractable

The textbook partial composition is

    ∘ᵢ : P m ⊗ P n → P (m + n - 1),    i : Fin m

Formalising it directly means truncated subtraction plus heavy `Fin` bookkeeping to track how
slot indices shift after a composition. That bookkeeping is what makes operads unpleasant to
formalise, and the closed mathlib PRs went this way (`Fin.hAdd : Fin n → Fin m → Fin (n+m-1)`,
`PermFinPadAt`, ...).

Here the slot is instead recorded **positionally in the arity**. An operation with a
distinguished input slot has type `P (a + 1 + b)` — `a` inputs before the slot, `b` after — and

    comp a b : P (a + 1 + b) →ₗ[R] P n →ₗ[R] P (a + n + b)

Three consequences:

* **no subtraction anywhere;**
* the **right unit law is definitional** (`n = 1` returns `P (a + 1 + b)` on the nose);
* **every coherence condition is a pure `Nat` identity**, discharged by `omega`. There is no `Fin`
  index arithmetic at all — including in parallel associativity, normally the worst part, which
  here is just rearranging `a + n + b + p + c`.

The cost is that `a` and `b` must be *explicit* arguments: from `α : P 3` alone Lean cannot tell
whether the slot sits at position 0, 1 or 2. `Operad.compFin` bridges back to the familiar
`Fin`-indexed form for users.

## Status

Roughly 7,000 lines, **`sorry`-free**. `Audit.lean` runs `#print axioms` on 157 headline results
and confirms every one rests only on Lean's three standard axioms — `propext`, `Quot.sound`, and
(wherever mathlib's multilinear machinery is involved) `Classical.choice`. Never `sorryAx`.

| Item | Where | Status |
|---|---|---|
| `reindex` transport along arity equalities, + simp API | `Basic.lean` | proved |
| `NSOperad` class (unit, both associativities) | `Basic.lean` | defined |
| Bilinearity consequences (`comp_add/smul/zero_*`) | `Basic.lean` | proved |
| `Ass`, the associative operad | `Basic.lean` | **all four axioms proved** |
| `compFin`, `Fin`-indexed composition + bridge, linearity | `Constructions.lean` | proved |
| `NSOperadHom`, `ext`, identity, composition | `Constructions.lean` | proved |
| `End R V`, the endomorphism operad | `Endomorphism.lean` | **all four axioms proved** |
| `Algebra`, `act`, `self`, `comap` | `Algebra.lean` | proved |
| `star` (`⋆`), bilinearity, both unit laws | `Total.lean` | proved |
| `bracket`, antisymmetry, `[α,α] = 0`, biadditivity | `Total.lean` | proved |
| **Algebras over `Ass` are associative algebras** | `AssAlgebra.lean` | **proved** |
| `Suboperad`, inherits all four axioms; inclusion morphism | `Suboperad.lean` | proved |
| `compFin_assoc_seq` — sequential associativity in `∘ᵢ` form | `Associativity.lean` | proved |
| `compFin_assoc_par` — parallel associativity in `∘ᵢ` form | `Associativity.lean` | proved |
| `compFin` distributes over `Finset.sum`; both bracketings as double sums | `PreLie.lean` | proved |
| `star_star_left_split` — the associator equals `disjointPart` | `PreLie.lean` | **proved** |
| `disjointPart_symm` — `disjointPart` is symmetric in `β, γ` | `PreLie.lean` | **proved** |
| **`star_assoc_symm` — the pre-Lie identity** | `PreLie.lean` | **proved** |
| `Tot`, the total space `⨁ k, P (k+1)`, as a graded ring | `TotalSpace.lean` | proved |
| **`RightPreLieRing (Tot R P)`** — a mathlib instance | `TotalSpace.lean` | **proved** |
| **`jacobi` — the commutator is a Lie bracket** | `TotalSpace.lean` | **proved** |
| **`LieRing` and `LieAlgebra R` on `Tot R P`** — mathlib instances | `TotalSpace.lean` | **proved** |
| `Gerstenhaber R V` — the bracket on `End R V` | `TotalSpace.lean` | proved |
| Planar trees and forests, grafting, arity of a graft | `Tree.lean` | proved |
| The four operad laws for grafting, at tree level | `Tree.lean` | **proved** |
| **`NSOperad R (Free R E)`** — the operad of planar trees | `Free.lean` | **proved** |
| `sstar` — the signed circle product of the suspension | `DG.lean` | proved |
| **`maurerCartan_iff` — `Θ ⋆ₛ Θ = 0` is associativity** | `DG.lean` | **proved** |
| `ass_maurerCartan` — `Ass` solves Maurer–Cartan | `DG.lean` | proved |
| **`sstar_assoc_symm` — the graded pre-Lie identity** | `GradedPreLie.lean` | **proved** |
| `disjointPartS_symm` — the signed disjoint part | `GradedPreLie.lean` | proved |
| `TotS`, the signed total space | `TotalSpaceS.lean` | proved |
| **`jacobiS` — the graded Jacobi identity** | `TotalSpaceS.lean` | **proved** |
| `two_smul_associator_odd` — the obstruction at 2 | `TotalSpaceS.lean` | proved |
| **`dsq_eq_zero` — `d² = 0` (with `2` invertible)** | `TotalSpaceS.lean` | **proved** |
| `dLin`, cocycles, coboundaries, `cohomology` | `Cohomology.lean` | proved |
| `NSOperadHom.app_sstar`, `app_gbracket` — morphisms preserve `⋆ₛ` and the bracket | `DGHom.lean` | proved |
| **`TConv.eval_gbracket_gbracket_eq_zero` — twisting at a Koszul-dual Maurer–Cartan element squares to zero on the Koszul dual** | `KoszulTwist.lean` | **proved** |
| `TConv.eval_gbracket_congr` — the bracket respects agreement on a slice-closed collection | `KoszulTwist.lean` | proved |
| `BTree.mirror`, `OfArity.mirrorEquiv` — mirror images of planar trees; the named trees of arity three and four | `Mirror.lean` | proved |
| `substF`, `extend` — total composition, tree evaluation | `TotalComp.lean` | proved |
| **`extend_corolla` — evaluation returns the generator** | `TotalComp.lean` | **proved** |
| `genOf`; **`Mag`, the magmatic operad** | `Magmatic.lean` | **proved** |
| `OperadIdeal`, `Quot`, **the quotient is an operad** | `Ideal.lean` | **proved** |
| `generated` — the ideal generated by relations | `Ideal.lean` | proved |
| **`AssPres` — associativity by a presentation** | `Magmatic.lean` | **proved** |
| `Species`, the `Σₙ`-actions via functoriality | `Species.lean` | proved |
| **`endSpecies`; its arity `n` is `End`'s** | `Species.lean` | **proved** |
| `unitSpecies` — the unit for the substitution product | `Species.lean` | defined |
| `partMap` — partitions transport along bijections, functorially | `Partition.lean` | proved |
| `NSCooperad`, dualising the positional convention; `Ass` as a cooperad | `Cooperad.lean` | **proved** |
| **`Presentation`** — operads by generators and relations | `Presentation.lean` | **proved** |
| `Presentation.lift`, `lift_gen`, `hom_ext` — its universal property | `Presentation.lean` | **proved** |
| `assPresToAssOfRep_eq` — the API reproduces the hand-built comparison map | `Presentation.lean` | **proved** |
| **`Conv R C P`** — the convolution algebra of a cooperad into an operad | `Convolution.lean` | defined |
| `Conv.star` (`⋆c`), bilinearity in both arguments | `Convolution.lean` | **proved** |
| `Conv.bracket`, antisymmetry, `[f,f] = 0`, biadditivity | `Convolution.lean` | proved |
| `Conv.convTerm_ass` — the encoding check, in closed form | `Convolution.lean` | **proved** |
| **`Conv.star_assoc_symm` — the pre-Lie identity for `⋆c`** | `ConvolutionPreLie.lean` | **proved** |
| `nested_term`, `parallel_term` — the two associativities, termwise | `ConvolutionPreLie.lean` | proved |
| **`ConvAlg`: `RightPreLieRing`, `RightPreLieAlgebra`, `LieRing`, `LieAlgebra R`** | `ConvolutionPreLie.lean` | **proved** |
| `RightPreLieRing.toLieRing`, `toLieAlgebra` — any right pre-Lie ring is Lie | `PreLieLie.lean` | proved |
| **`Perm`**, Chapoton's operad, `Perm R n = Fin n → R` | `Perm.lean` | **all four axioms proved** |
| **`SymOperad`** — symmetric operads by partial composition over finite types | `Sym.lean` | defined |
| `seqEquiv`, `parEquiv`, `compEquiv`, the unit equivalences | `Sym.lean` | defined |
| `SymOperadHom`, `ext`, identity, composition | `Sym.lean` | proved |
| **`Sym.Com`, `Sym.Perm`** as symmetric operads; `Perm.sumHom : Perm → Com` | `Sym.lean` | **all axioms proved** |
| `insertEquiv` — the positional order of a composite's inputs | `SymNS.lean` | proved |
| **`instNSOperadToNS`** — the underlying non-symmetric operad `n ↦ P (Fin n)` | `SymNS.lean` | **all four axioms proved** |
| `SymOperadHom.toNS` — morphisms restrict | `SymNS.lean` | proved |
| `Sym.Perm.toNSHom` — the restriction of symmetric `Perm` is the planar `Perm` | `SymNS.lean` | **proved** |
| **`Sym.Ass`** — the symmetric associative operad, the linearization of the set operad of linear orders | `SymAss.lean` | **all axioms proved** |
| `Sym.Ass.toCom` — the augmentation `Ass → Com` | `SymAss.lean` | proved |
| `Sym.Ass.ofNS` — the planar `Ass` as the standard orders inside the underlying planar operad of `Ass` | `SymAss.lean` | **proved** |
| **`SymOperadIdeal.Quot` — the quotient of a symmetric operad by an ideal is a symmetric operad** | `SymQuot.lean` | **proved** |
| `SymOperadIdeal.liftHom`, `liftHom_unique` — its universal property; `mem_ker_projHom` | `SymQuot.lean` | proved |
| `SymOperadHom.kerLift`, `kerLift_injective`, `kerLift_bijective` — the first isomorphism theorem | `SymQuot.lean` | proved |
| `SymOperadIdeal.span` — the ideal generated by relators, `span_le`; **`presHomEquiv`, `presLinHomEquiv`** — the universal property of an operad presented by relators (on a linearized set presentation: generators, set relations, linear relators) | `SymPresentation.lean` | **proved** |
| **`TConv.IsSymm` — symmetric cochains on binary trees** (the symmetric convolution algebra, in planar representatives: equivariance under swaps at vertices with the sign `-(-1)^(a b)`); `isSymm_two_iff` — in weight one, the equivariant generator data | `SymTreeConv.lean` | defined, proved |
| **`TConv.isSymm_sstar`, `isSymm_gbracket` — symmetric cochains are closed under `⋆ₛ` and the bracket**, so they form a graded sub-pre-Lie algebra (graded pre-Lie and Jacobi inherited); `sstar_apply_paths` — the product as a sum over the vertices and leaves of a tree | `SymTreeConv.lean` | **proved** |
| `gbracket_gbracket_eq` — the twisting identity `⁅T, ⁅T, x⁆⁆ = ⁅T ⋆ₛ T, x⁆` (`2` invertible); `OperadIdeal.sstar_mem_*`, `gbracket_mem_*` — coefficients in an ideal; `SymOperadIdeal.toNS` | `SymTreeConv.lean` | **proved** |
| **`Reg N` — the symmetrization of a planar set operad** (a linear order on the inputs and a planar operation of that arity), a set operad; **`Reg.homEquiv` — left adjoint to the underlying planar operad**; `Reg.hadamardIso` — `LinOrd ×_H S ≅ Reg (toNSSet S)` (regular operads) | `Regular.lean` | **proved** |
| **`Reg.presIso` — the symmetrization of a planar presentation is presented by the same generators and relations** (`symRel`, `respects_symRel_iff`); `Reg.mapIso`, `SetOperadIso.ofBijective`, `trans`, `precompEquiv` | `Regular.lean` | **proved** |
| **`PDias.presIso`, `PTrias.presIso` — the planar operads of pointed inputs and of nonempty subsets are presented by `⊣`, `⊢` (`⊥`) and the five (eleven) relations of dialgebras (trialgebras)**, by right-comb normal forms; **`DiasSet.presIso`, `TriasSet.presIso` — Loday's and Loday–Ronco's presentations of `Dias` and `Trias`**; `Dias.homEquiv`, `Trias.homEquiv` — morphisms out of them are dialgebra (trialgebra) data | `DiasTrias.lean` | **proved** |
| **`PermElt` — a permutative binary element** (`ν(ν(x, y), z) = ν(x, ν(y, z)) = ν(x, ν(z, y))`) and its adjoining calculus (`adj_perm`, `adjN`, `bin_nu_adjN`); **`PointedSet.homEquiv`, `Perm.homEquiv` — the presentation of `Perm`**: morphisms out of it are permutative elements | `PermPres.lean` | **proved** |
| **`AssSet.presIso`, `Ass.homEquiv` — the presentation of the (non-unital) associative operad** by one binary operation and associativity, as a regular operad (`PAss.presIso`) | `AssPres.lean` | **proved** |
| **`NonemptySubset.presIso`, `ComTrias.homEquiv` — Vallette's presentation of `ComTrias`** by `⊥` commutative, `⊣`, and the relations of commutative trialgebras, through normal forms `⊣(⊥_S, ⊥_{A∖S})` (`ComTriasData.lift`, `psi_comp`) | `ComTriasPres.lean` | **proved** |
| **Algebras over presented operads**: `Com.algebraEquiv`, `Perm.algebraEquiv`, `Ass.algebraEquiv`, `Dias.algebraEquiv`, `Trias.algebraEquiv` — algebras are commutative associative, permutative, associative algebras, dialgebras, trialgebras, commutative trialgebras (`ComAlg`, `PermAlg`, `AssAlg`, `DiAlg`, `TriAlg`, `ComTriAlg`; `ComTrias.algebraEquiv`); binary composites in the endomorphism operad (`EndOp.ap_bin`, `leftComb_eq_rightComb_iff`) | `Algebras.lean` | **proved** |
| **Binary quadratic operads**: `FreeBin R G`, the monomials `bin2`, `binL`, `binR` and their values `binHom_bin2`, `binHom_binL`, `binHom_binR`; `BinPres R r₂ r₃` and **`BinPres.algebraEquiv`** (algebras are binary operations killing the relators); **`Lie`, `PreLie`, `Leib`, `Zinb`, `Dend`, `Pois`** and their algebras (`Lie.algebraEquiv`, …, `Pois.algebraEquiv`: `LieAlg`, `PreLieAlg`, `LeibAlg`, `ZinbAlg`, `DendAlg`, `PoisAlg`) | `BinaryQuadratic.lean` | **proved** |
| **The free operad on binary generators**: planar binary trees under grafting are the free non-symmetric set operad (`BTree.OfArity.instNSSetOperad`, `BTree.OfArity.homEquiv`, values `BTree.evalArr`); **the free symmetric set operad on binary generators is the regular operad of planar trees**, `FreeBin.regIso : FreeSet (BinGen E) ≅ Reg (OfArity E)`; a basis of `FreeBin R G` in every arity (`FreeBin.basis`) and its dimension `n! · #trees` (`FreeBin.finrank_eq`) | `FreeBinary.lean` | **proved** |
| **Koszul duality of binary quadratic operads** (one or several generators, no relators of arity two, over a field): the basis of `12 \|G\|²` monomials of arity three (`basis3`); the relations of arity three are the span of the relabelled relators (`span_sub_three`); the Koszul pairing `pair3`, nondegenerate and equivariant up to the signature; the Koszul dual relations `dualRel` of complementary dimension (`finrank_dualRel`), **duality is an involution** (`dualRel_dualRel`, `dual_dual`); **the classical dualities `Ass^! = Ass`, `PreLie^! = Perm`, `Perm^! = PreLie`, `Leib^! = Zinb`, `Zinb^! = Leib`, `Dend^! = Dias`, `Dias^! = Dend`** (`BinAss.dual`, `PreLie.dual`, …, `BinDias.dual`); `BinAss`, `BinPerm`, `BinDias` and their algebras | `BinaryKoszul.lean`, `BinaryQuadratic.lean` | **proved** |
| **Koszul duality with commutative and anticommutative generators**: the relations of arity three of relators of arity two (`FreeBin.ideal3Of`) and the arity-three part of the ideal of relators of arities two and three (`FreeBin.span_sub_three_23`, `FreeBin.span_le_23`); the basis of monomials of arity two (`FreeBin.basis2`) and the signature twist (`FreeBin.twist2`); composites of monomials computed in the free model of labelled trees (`FreeBin.evalW_injective`, `FreeBin.comp_e0_bin2`, `FreeBin.comp_e1_bin2`); the Koszul dual `BinPres.dual23` (`FreeBin.dualRel23`), which without relators of arity two is that of `BinaryKoszul.lean` (`FreeBin.BinPres.dual23_empty`); **`Com^! = Lie`** in characteristic other than two (`FreeBin.BinCom.dual`, via the antisymmetrized associator `FreeBin.asym3`) | `BinaryKoszulSym.lean` | **proved** |
| **Infinitesimal deformations of a symmetric operad**: two-cochains `ω` and the deformed operad on pairs `x + εx'` (`Deformed`), **an operad exactly when `ω` is an `𝔖`-cocycle** (`Deformed.instSymOperad`, `Deformed.isCocycle_of_symOperad`); coboundaries of equivariant families, and **a cocycle is a coboundary exactly when `P → P_ω` lifts the identity** (`isCoboundary_iff_exists_lift`); derivations are the lifts `P → P[ε]` of the identity (`SymDerivation.liftEquiv`), the Euler and inner derivations with `ad_1 = -euler` (`ad_one`); transport along isomorphisms (`SymOperadIso.forall_isCoboundary`) | `Deformation.lean` | **proved** |
| **The bar construction of a shuffle operad and the criterion of Dotsenko and Khoroshkin**: bar trees (monomials with cut edges) and the bar differential of the free shuffle operad, **`d² = 0`** (`ShuffleBar.d_dTree`); the relators substituted at uncut edges span a subcomplex `J R` (`ShuffleBar.d_mem_J`), the kernel onto the bar construction of the presented operad; quadratic Gröbner bases (`LTree.IsGroebner`), the normal monomials as a complement of the ideal (`IsGroebner.isCompl`) and normal forms on any set of labels (`IsGroebner.nf`); **a shuffle operad with a quadratic Gröbner basis is Koszul**: its bar homology vanishes below the diagonal (`ShuffleBar.isKoszul`), by components normalization (`ShuffleBar.Φ`), reduction modulo the relators (`ShuffleBar.reduce`) and a contracting homotopy for the leading part (`ShuffleBar.d₀_hTree_add`) | `ShuffleNormal.lean`, `ShuffleBar.lean`, `ShuffleKoszul.lean` | **proved** |
| **The dimension of the Koszul dual cooperad from a quadratic Gröbner basis**: the Koszul dual cooperad of a shuffle operad presented by relators of arity three, in arity `n`, as the top homology of its bar construction (`ShuffleBar.KD`); the normal bar trees are a basis of the bar construction modulo the relators (`ShuffleBar.normalized_eq`, `ShuffleBar.normalized_injective`), on which the complex is exact below the diagonal (`ShuffleBar.exact_dN`); **its Euler characteristic gives `dim KD(n)` as an alternating sum of numbers of normal bar trees** (`ShuffleBar.finrank_KD`), so **two quadratic Gröbner bases with the same leading monomials have Koszul dual cooperads of the same dimension in every arity** (`ShuffleBar.finrank_KD_eq`); by inclusion and exclusion over the cut edges, **that dimension is the number of monomials all of whose windows are leading** (`ShuffleBar.sum_ncard_nrm`, `ShuffleBar.finrank_KD_eq_ncard`) | `ShuffleKoszulDual.lean` | **proved** |
| **Shuffle monomials at the root**: a monomial of arity `n` is a root vertex over two standardized monomials, the left one on a set of labels containing `0` (`LTree.joinAt`, `LTree.joinAt_mem`, `LTree.eq_joinAt`, `LTree.joinAt_injective`); so a property of the root and of the standardized subtrees is counted by the binomial convolution `Σ C(n - 1, i - 1) · #{(e, a, b)}` (`LTree.card_filter_rootP`) | `ShuffleRoot.lean` | **proved** |
| **`LTree` — shuffle tree monomials** (planar binary trees with labelled leaves, least labels increasing at every vertex); **`monomials`, `mem_monomials`, `card_monomials` — there are `(2n - 3)!! \|E\|ⁿ⁻¹` of arity `n`**, by grafting the largest leaf (`graft`, `prune`, `graft_inj`, `exists_graft`) | `ShuffleTree.lean` | **proved** |
| `windows`, `IsNormal` — two-vertex submonomials and normality for arity-three leading monomials; `pathKey` — the path-lexicographic key; **`isNormal_iff` — when every first-slot window leads, the normal monomials are the right combs whose consecutive decorations avoid the leading right combs** | `ShuffleTree.lean` | **proved** |
| `IsLeadingOf`, `IsLeading`, `fiberKer` — leading monomials, and the kernel of a linearized map to a basis or zero; **`isLeading_fiberKer_iff` — its leading monomials are those sent to zero or not least in their fiber** | `LeadingTerm.lean` | **proved** |
| **Substitution at a window** of a shuffle monomial (`LTree.substAt`): it keeps the labels and the shuffle condition (`perm_labels_substAt`, `isShuffle_substAt`, `substAt_mem_monomials`), gives back the monomial for its own window (`substAt_windowAt`), and **is compatible with the path-lexicographic key** (`pathKey_substAt_lt`); non-normal monomials are those with an edge whose window is a leading monomial (`not_isNormal_iff`). **A Gröbner criterion** (`exists_reduction`, `isLeading_iff_of_supportedOn`, `isCompl_supportedOn`): the division algorithm, and leading monomials of an ideal from a model injective on normal monomials | `ShuffleSubst.lean`, `LeadingTerm.lean` | **proved** |
| **`Hadamard S T`** — the Hadamard product of set operads, componentwise; the projections, `lift`, `lift_unique` (it is the product of set operads), `prodMap`, `commIso` | `SetHadamard.lean` | **proved** |
| `PointedSet`, `NonemptySubset` — the set operads of pointed inputs and of nonempty sets of inputs; **`PointedSet.linPermIso : Lin R PointedSet ≅ Perm R`**; singletons `PointedSet → NonemptySubset`; `ComTrias R` | `SetHadamard.lean` | **proved** |
| `LinOrd.equivRank` — a linear order is a ranking; `LinOrd.card` (`n!` orders), `Ass.finrank` | `SetHadamard.lean` | proved |
| **`Dias R`, `Trias R`** — Loday's dialgebras and Loday–Ronco's trialgebras as linearized Hadamard products with `LinOrd`; the five and eleven relations (`DiasSet.relations`, `TriasSet.relations`); dimensions `n · n!` and `(2ⁿ - 1) · n!` (`Dias.finrank`, `Trias.finrank`); the injective morphism `Dias → Trias` | `SetHadamard.lean` | **proved** |
| `sum_split3`, `permComp_apply_lt/mid/ge` — the three ranges | `Perm.lean` | proved |
| **`sum_permComp`** — the total of a composite is the product of the totals | `Perm.lean` | **proved** |
| **`evHom` — summing is a morphism `Perm → Ass`** | `Perm.lean` | **proved** |

`Ass` is not decoration: it is the smallest instance that exercises every axiom, so proving it
confirms the axiom set is consistent and the reindexings line up.

Note it is `Ass`, **not** `Com`. As a *non-symmetric* operad, one generator per arity means one
planar way to combine `n` inputs in order — associative algebras. `Ass` and `Com` only separate
once symmetric group actions exist.

### The endomorphism operad

`End R V n = MultilinearMap R (fun _ : Fin n => V) V`, with `comp` built by hand rather than
assembled from mathlib combinators, so that it is *definitionally* transparent — which is what
makes the four axiom proofs tractable.

The organising trick is that the inputs `Fin (a + n + b)` split into just **two** kinds: those
consumed by the inserted operation (`midIdx`) and those surviving into the outer one (`outIdx`).
Because `outIdx` covers the blocks before *and* after the slot uniformly, multilinearity is a
two-case argument rather than three, and each associativity proof bottoms out at
`v ⟨X, _⟩ = v ⟨Y, _⟩` with `X = Y` by `omega`. Sequential associativity needs a 3-way split on
the input position; parallel needs 5 (before slot 1, slot 1, between, slot 2, after).

### The total space and `⋆`

Grade by **arity minus one**: `α : P (j + 1)` has degree `j`. Then

    α ⋆ β = ∑ i, α ∘ᵢ β

is degree-additive, and — a real payoff of the positional convention — the sum needs **no
reindexing at all**: every summand `compFin i α β` already lands in `P ((j+1)-1+(k+1))`, which
Lean reduces definitionally to `P (j+k+1)`, independently of which slot `i` was used.

Both unit laws are proved. They are not symmetric, and the asymmetry is real rather than
cosmetic: `α ⋆ 1 = (arity) • α` holds on the nose because `j + 0` *is* definitionally `j`,
whereas `1 ⋆ β = β` needs a reindexing because `0 + k` is *not* definitionally `k` — `Nat.add`
recurses on its second argument. The statement in the file records this honestly rather than
hiding it.

The commutator `⁅α, β⁆ = α ⋆ β - β ⋆ α` is defined and proved antisymmetric.

### Capstone: algebras over `Ass` are associative algebras

`AssAlgebra.mul_assoc` derives a classical theorem from the abstract machinery. The proof is the
intended use of an operad in miniature:

1. In `Ass` the two ternary operations built from the binary generator are equal — both are
   `1 * 1` — and this is true by `rfl` (`ass_comp_eq`).
2. Pushing that one equation through the algebra morphism turns it into an equation between two
   elements of `End R V 3`.
3. Evaluating on `![x, y, z]` and computing the two tuples gives
   `mul (mul x y) z = mul x (mul y z)`.

Associativity is *derived*; nothing about it is assumed. This exercises the entire stack —
operad axioms, `End`'s explicit composition, morphisms, algebras — end to end.

## The symmetric spine: settled

**Decision: index by finite sets and bijections (species), not by `ℕ` with `Σₙ`-actions.**

The positional convention cannot carry symmetric operads. Applying `σ ∈ Σ_(a+1+b)` moves the
distinguished slot from `a` to `σ a`, so left equivariance is only *stateable* as

    comp a b (σ • α) β = blockPerm σ a b n • reindex _ (comp (σ a) (a + b - σ a) (reindex _ α) β)

which reintroduces the subtraction the convention exists to avoid, and requires constructing the
block permutation `blockPerm σ a b n : Perm (Fin (a + n + b))` explicitly, with inverse proofs.
Right equivariance stays clean; left does not.

The three candidates, judged against what this session actually cost:

1. **`ℕ`-indexed + `Σₙ`-actions.** Rejected, as above.
2. **Total composition** `γ : P k ⊗ P n₁ ⊗ ⋯ ⊗ P n_k → P (∑ nᵢ)`, with the standard
   block-permutation equivariance axiom. Stateable, but every coherence condition then lives over
   `Fin (∑ i, n i)`. That is the decisive objection: the whole reason the current spine is
   pleasant is that `omega` discharges every coherence goal, and **`omega` cannot reason about
   `Finset.sum`**. Adopting this trades linear arithmetic for `Finset` reindexing lemmas.
3. **Species.** `P S → ((s : S) → P (T s)) → P (Σ s, T s)`, indexed by finite types and functorial
   in bijections. Associativity is `Equiv.sigmaAssoc`; the unit laws are the `Σ`-unit
   equivalences; **there is no arithmetic at all**, and crucially **equivariance is free** — it is
   functoriality on the groupoid of bijections, not an extra axiom, so no block permutation ever
   has to be constructed.

The empirical evidence from building `End` is what settles it. The expensive part of this session
was not the algebra but constructing explicit `Fin` maps and proving their properties — `outIdx`,
`insTuple`, injectivity, case coverage — roughly 300 lines for a *single* construction. Block
permutations for option 1, or `Finset.sum` reindexing for option 2, are that same cost again and
worse. Option 3 pays it exactly once, in mathlib's existing `Equiv` API.

**Encoding plan.** `Species R` as a family `(S : Type) → [Fintype S] → ModuleCat R` together with
`map : (S ≃ T) → (obj S ≅ obj T)` and functoriality; `SymOperad` extends it with a unit in
`obj PUnit` and the sigma-indexed composition. The two open encoding questions, deliberately not
guessed at here, are whether to bundle via `ModuleCat` or carry `AddCommGroup`/`Module` instances
as separate fields, and where the universe of `obj` sits relative to the index types.

The `ℕ`-indexed non-symmetric spine in `Operad/Basic.lean` is **kept**, not replaced: it stays the
computational layer (it is the one that evaluates on concrete small cases), and the skeletal
equivalence to the species picture is a later bridge.

## Roadmap

**The plan of record is now [`ROADMAP.md`](ROADMAP.md)** (2026-09-28), which settles the
symmetric spine as species-style partial composition and adds a set-operad layer. The items below
are kept as the history of how the library got here.

1. **The substitution product on species.** Two layers of it are in. The *unit* is
   `unitSpecies`, the free module on the bijections `S ≃ Fin 1`. The *indexing* is `Partition.lean`:
   partitions of a finite type transport along a bijection, functorially — `partMap_refl` and
   `partMap_trans` are the two laws the eventual `map` field will rest on.

   The product itself is still to build:
   `(F ∘ G)(S) = ⊕_π F(blocks π) ⊗ ⨂_{B ∈ π} G(B)`. The remaining work is to decorate each
   partition with `F` of its block type and a `PiTensorProduct` of `G` over the blocks, sum over
   `Finpartition univ` (a `Fintype`), and prove the functor laws for that sum — the last being the
   hard part, since it means transporting a direct sum over a *transported* index. Symmetric
   operads as monoids for the product then follow.

   Worth weighing first: symmetric operads can instead be defined Markl-style, as our `NSOperad`
   plus `Σₙ`-actions and an equivariance axiom for partial composition. That is a much cheaper
   route to `Com`, `Lie` and `Pois`, which is what item 4 actually wants from this.
2. **`AssPres R ≅ Ass R`.** The comparison map exists now: `OperadIdeal.liftHom` is the
   universal property of the quotient, and combining it with `extendHom` gives
   `assPresToAss : NSOperadHom R (AssPres R) (Ass R)`. Proving it an isomorphism is the remaining
   half, and it is a genuine theorem rather than plumbing: it amounts to a normal-form result,
   that every planar tree is congruent modulo the associator to a fixed comb, so that
   `AssPres R n` is spanned by one element. Surjectivity is easy; injectivity is that argument.

   **Presentations are now packaged.** `Presentation.lean` turns "generators plus relations" into
   an operad and, more to the point, makes mapping *out* of one ask for exactly the mathematics:
   a `Rep` is a choice of image for each generator plus a proof that the relations die, and
   `lift` turns one into a morphism, with `lift_gen` and `hom_ext` as the two halves of the
   universal property. `assPresToAssOfRep_eq` checks the API against the map above.

2a. **The convolution algebra.** `Convolution.lean` defines `Conv R C P`, the degreewise linear
   maps from a cooperad to an operad, with the product that decomposes in `C`, applies the two
   maps, and recomposes in `P`. Bilinearity in both arguments is proved, as is the encoding check
   `convTerm_ass`, which computes a term in closed form for `C = P = Ass` — a mis-ordered
   composite would still typecheck but would fail that.

   **Done 2026-09-28:** `ConvolutionPreLie.lean` proves the pre-Lie identity and makes `ConvAlg`
   a Lie algebra; the paragraph below is the plan it followed. **What was missing was the pre-Lie
   identity for `⋆c`**, and it is a theorem of the size of
   `star_assoc_symm`, not plumbing. The route is the one `PreLie.lean` already walks: the
   associator splits into a nested part and a disjoint part, the nested part cancels by
   `decomp_assoc_seq` against `comp_assoc_seq`, and the disjoint part is symmetric in the last two
   arguments by `decomp_assoc_par` against `comp_assoc_par`. The one new difficulty is that the
   cooperad axioms are equalities of *linear maps* rather than of elements, so the bookkeeping
   cannot be done pointwise, and `swapLast` is what the parallel case will need. With it, the
   Maurer–Cartan elements of `Conv` are twisting morphisms `C → P`, which is what the whole dg
   layer of this library was built to say.
3. **The common operads.** `Ass`, `End`, `Mag`, `AssPres` and now **`Perm`** are in. `Lie` and
   `Pois` are *symmetric*, so they are blocked on item 1 rather than on effort. `Com` is **not** a
   gap: non-symmetrically it *is* `Ass`, since one generator per arity is one planar way to combine
   `n` ordered inputs, and the two separate only once `Σₙ`-actions exist.

   `Perm` is worth a note, because it is the exception to the library's design. Every other operad
   here keeps index data out of its types; `Perm`'s elements *are* indexed by the inputs, so its
   composition is a three-way case split on the index and its axioms are genuine `Fin`-sum
   bookkeeping. Three things make that tractable and are the shape to copy for any future operad
   of the same kind: `sum_split3` splits a sum over `Fin (a + n + b)` into the three ranges once,
   so no later proof mentions `Fin.castAdd`; the three value lemmas take the index bounds as
   explicit arguments rather than rebuilding them; and `sum_permComp` is proved *before* the
   associativity axioms, because both need it. It is also the statement that `evHom` is a
   morphism — in the game-theoretic reading, efficiency.

   One trap, recorded because it cost the most time: **`omega` does not know `Fin.isLt`**. Every
   arithmetic goal in `Perm.lean` is preceded by `have := i.isLt`, and every goal mentioning a
   `Fin.mk` is preceded by `simp only [val_mk']`; without those `omega` sees an unconstrained
   natural, or an atom, and fails.
4. **Derived operadic frameworks and their algebras.** Bar–cobar, Koszul duality, model
   structures, ∞-operads. The first prerequisite is now in: `Weight.lean` gives the weight
   grading — the number of internal vertices of a tree — with `Free.comp_mem_weightSpan` saying
   composition adds weights, and `assocRel_mem_weightSpan` showing the presentation of `Ass` is
   *quadratic*, which is exactly Koszul duality's hypothesis. Note the contrast with arity:
   composition changes arity in a way that depends on the slot, and weight not at all.

   **Cooperads now exist.** `NSCooperad` dualises the positional convention: infinitesimal
   decomposition `decomp a b n : C (a + n + b) →ₗ C (a + 1 + b) ⊗ C n` in place of `comp`, with
   each axiom the corresponding operad axiom reversed. Unlike the operad axioms these cannot be
   stated elementwise — a tensor product has no description by elements — so each is an equality
   of linear maps, and parallel coassociativity needs a braiding (`swapLast`) because the two
   orders of decomposing produce the same three pieces transposed. `instNSCooperadAss` is the
   first example and doubles as validation: a mis-stated coassociativity would have shown up
   there as an unprovable goal.

   What bar–cobar still needs on top of this is the bar construction itself — the cofree cooperad
   on the suspension of an augmented operad's ideal, with the differential induced by composition
   — which in turn wants augmentations and a suspension. Model structures need limits and
   colimits in the category of operads, a separate and larger gap; ∞-operads need dendroidal
   machinery and are far off.

5. **A more thorough CI**, deliberately last. Today's workflow builds, greps for `sorry`, and
   runs the axiom audit. The additions worth making are mathlib's own linters, a scheduled build
   against Mathlib master to catch upstream drift early, `doc-gen4` output published to Pages,
   and a badge row.

### A note for anyone taking the mathlib route later

Mathlib turns out to have more relevant API than the closed PRs suggest.
`MultilinearMap.compMultilinearMap` is *already* total (May-style) operadic composition over
`Σ i, β i` with multilinearity proved; `curryMid`, `currySum`/`uncurrySum` and `domDomCongr`
handle slot extraction; `Fin.insertNth` comes with `update_insertNth`/`insertNth_update`. That
route was not taken here — building `comp` by hand keeps it definitionally transparent, which is
what makes four axiom proofs feasible — but it is the natural basis for a general-`V` version.
