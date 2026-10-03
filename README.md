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

Continuous integration (`.github/workflows`): every push to `main` and every pull request builds
with warnings as errors, runs Mathlib's environment linters (`lake exe runLinter Operad`), checks
line lengths and the absence of `sorry`, and runs the axiom audit; `mathlib-master.yml` builds
weekly against Mathlib master; `docs.yml` builds the API documentation with doc-gen4 and publishes
it on GitHub Pages (enable Pages with "GitHub Actions" as its source).

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
| **Koszul duality with commutative and anticommutative generators**: the relations of arity three of relators of arity two (`FreeBin.ideal3Of`) and the arity-three part of the ideal of relators of arities two and three (`FreeBin.span_sub_three_23`, `FreeBin.span_le_23`); the basis of monomials of arity two (`FreeBin.basis2`) and the signature twist (`FreeBin.twist2`); composites of monomials computed in the free model of labelled trees (`FreeBin.evalW_injective`, `FreeBin.comp_e0_bin2`, `FreeBin.comp_e1_bin2`); the Koszul dual `BinPres.dual23` (`FreeBin.dualRel23`), which without relators of arity two is that of `BinaryKoszul.lean` (`FreeBin.BinPres.dual23_empty`); **`Com^! = Lie` and `Lie^! = Com`** in characteristic other than two (`FreeBin.BinCom.dual`, `FreeBin.Lie.dual`, via the antisymmetrized associator `FreeBin.asym3` and the relations of `Com` as the vectors with coordinates summing to zero, `FreeBin.comRel3_eq_ker`) | `BinaryKoszulSym.lean` | **proved** |
| **Certificates in arity three**: integer combinations of monomials (`FreeBin.Cert3`, `FreeBin.Cert2`) with their values, relabellings, coordinates, Koszul pairing and composites (`FreeBin.Cert3.pair3_val`, `FreeBin.Cert2.comp0_val`); membership in a span of relabelled generators, orthogonality to the relations of arity three, and lower bounds on dimensions, each reduced to a computation checked by the kernel (`FreeBin.val_mem_of_cert`, `FreeBin.val_mem_dualRel23`, `FreeBin.le_finrank_of_cert`); **Koszul dual relations and presentations by certificate** (`FreeBin.dualRel23_eq_span_of_cert`, `FreeBin.dual23_span_eq_of_cert`) | `BinaryCert.lean` | **proved** |
| **`ComTrias^! = PostLie`** (Vallette): commutative trialgebras and post-Lie algebras as binary quadratic operads (`BinComTrias`, `PostLie`); in characteristic zero the Koszul dual relations of `ComTrias` are spanned by the signed sums of seven classes of monomials (`dualRel23_comTrias`), its Koszul dual is presented by the post-Lie relations with the bracket halved (`dual23_comTrias`, `BinComTrias.dual23_eq`) and **is isomorphic to `PostLie`** (`BinComTrias.dualIso`); for the leading forms, `x ⊣ (y ⊥ z) = 0`, the Koszul dual is the operad of a Lie bracket and a right pre-Lie product acting by derivations (`BinComTriasLead.dual23_eq`, `BinComTriasLead.dualIso`); renaming and rescaling generators of presented operads (`FreeBin.rename`, `FreeBin.BinPres.renameIso`) | `PostLie.lean` | **proved** |
| **`ComTrias` is `BinComTrias`**: the values of the monomials under a morphism out of the free operad on binary generators (`FreeBin.linHom_bin2`, `FreeBin.linHom_binL`, `FreeBin.linHom_binR`); the relators of `ComTrias` vanish exactly when the generator values satisfy the relations of commutative trialgebras (`BinComTrias.dataOfKills`, `BinComTrias.kills_of_data`), so **Vallette's `ComTrias R = Lin R NonemptySubset` is isomorphic to `BinComTrias R`** (`BinComTrias.isoComTrias`) and `ComTrias^! ≅ PostLie` is about it | `ComTriasBin.lean` | **proved** |
| **Infinitesimal deformations of a symmetric operad**: two-cochains `ω` and the deformed operad on pairs `x + εx'` (`Deformed`), **an operad exactly when `ω` is an `𝔖`-cocycle** (`Deformed.instSymOperad`, `Deformed.isCocycle_of_symOperad`); coboundaries of equivariant families, and **a cocycle is a coboundary exactly when `P → P_ω` lifts the identity** (`isCoboundary_iff_exists_lift`); derivations are the lifts `P → P[ε]` of the identity (`SymDerivation.liftEquiv`), the Euler and inner derivations with `ad_1 = -euler` (`ad_one`); transport along isomorphisms (`SymOperadIso.forall_isCoboundary`) | `Deformation.lean` | **proved** |
| **Derivations along a morphism** `f : F → P` (`SymDerivationAlong`), killing the unit (`SymDerivationAlong.app_one`); the lifts of `f` to a deformed operad `P_ω` form a torsor under them (`SymDerivationAlong.ofLifts`, `Deformed.liftAdd`), and **they are the lifts of `f` to `P[ε]`** (`SymDerivationAlong.liftEquiv`); out of a free operad, morphisms and **derivations along `f` are their values on the generators** (`FreeSet.linHom`, `Pres.lin_hom_ext`, `SymDerivationAlong.freeEquiv`), and `f` lifts to every `P_ω` (`Deformed.freeLift`) | `DerivationAlong.lean` | **proved** |
| **Formal deformations** of a symmetric operad (`FormalDeformation`: cochains `μ_k` making `Σ t^k μ_k` an operad structure on power series, `FormalDeformation.instSymOperad`); the obstruction to extending a trivialization by one order is a two-cocycle (`isCocycle_obstruction`, via `SymCochain.isCocycle_of_injective`) and is the coboundary of the next term exactly when it extends (`isMorAt_iff`); **rigidity**: if every two-cocycle is a coboundary, every formal deformation is trivial (`exists_trivialization`), by an isomorphism of operads with the trivial deformation (`exists_iso_trivial`) | `FormalDeformation.lean` | **proved** |
| **The bar construction of a shuffle operad and the criterion of Dotsenko and Khoroshkin**: bar trees (monomials with cut edges) and the bar differential of the free shuffle operad, **`d² = 0`** (`ShuffleBar.d_dTree`); the relators substituted at uncut edges span a subcomplex `J R` (`ShuffleBar.d_mem_J`), the kernel onto the bar construction of the presented operad; quadratic Gröbner bases (`LTree.IsGroebner`), the normal monomials as a complement of the ideal (`IsGroebner.isCompl`) and normal forms on any set of labels from any such complement (`LTree.nfOf`); **a shuffle operad with a quadratic Gröbner basis is Koszul**: its bar homology vanishes below the diagonal (`ShuffleBar.isKoszul`), for any Gröbner data — a complement by normal monomials and a level lowered by the relators led by leading windows (`ShuffleBar.GroebnerData`, `ShuffleBar.isKoszul_of_data`) — by components normalization (`ShuffleBar.Φ`), reduction modulo the relators (`ShuffleBar.reduce`) and a contracting homotopy for the leading part (`ShuffleBar.d₀_hTree_add`) | `ShuffleNormal.lean`, `ShuffleBar.lean`, `ShuffleKoszul.lean` | **proved** |
| **The dimension of the Koszul dual cooperad from a quadratic Gröbner basis**: the Koszul dual cooperad of a shuffle operad presented by relators of arity three, in arity `n`, as the top homology of its bar construction (`ShuffleBar.KD`); the normal bar trees are a basis of the bar construction modulo the relators (`ShuffleBar.normalized_eq`, `ShuffleBar.normalized_injective`), on which the complex is exact below the diagonal (`ShuffleBar.exact_dN`); **its Euler characteristic gives `dim KD(n)` as an alternating sum of numbers of normal bar trees** (`ShuffleBar.finrank_KD`), so **two quadratic Gröbner bases with the same leading monomials have Koszul dual cooperads of the same dimension in every arity** (`ShuffleBar.finrank_KD_eq`); by inclusion and exclusion over the cut edges, **that dimension is the number of monomials all of whose windows are leading** (`ShuffleBar.sum_ncard_nrm`, `ShuffleBar.finrank_KD_eq_ncard`) | `ShuffleKoszulDual.lean` | **proved** |
| **Rescaling the generators**: the weight of a monomial, the product of the scalars of its vertices (`LTree.wt`), is multiplicative under plugging and substitution (`LTree.wt_plug`, `LTree.wt_substAt`) and unchanged by merging along a cut edge (`ShuffleBar.wt_mergeK`); the diagonal rescaling of the bar construction (`ShuffleBar.scaleBar`) commutes with the differential (`ShuffleBar.d_scaleBar`) and carries the relator subcomplex of `R` into that of the rescaled relators (`ShuffleBar.map_scaleBar_J_le`), so **for nonzero scalars it carries the Koszul dual cooperad of `R` onto that of the rescaled relators** (`ShuffleBar.map_scaleBar_KD`) and **their dimensions agree in every arity** (`ShuffleBar.finrank_KD_rescale`); **Koszulness is invariant under rescaling** (`ShuffleBar.isKoszul_rescale`) | `ShuffleRescale.lean` | **proved** |
| **The associated graded of the Koszul dual cooperad**: a weight on a basis grades the free module (`Graded.wproj`), and the associated graded of a subspace for the filtration by weight, the span of its top components (`Graded.grW`), has its dimension (`Graded.finrank_grW`); a weight on the generators weighs bar trees additively, kept by the differential (`ShuffleBar.d_wproj`) and added by substitution (`ShuffleBar.wdegB_substBar`); if `R₀` is spanned by top components of relators of `R`, the relator subcomplex of `R₀` is the associated graded of that of `R` (`ShuffleBar.J_inf_C_eq_grW`) and **the Koszul dual cooperad of `R₀` is the associated graded of that of `R`** (`ShuffleBar.KD_eq_grW`), as soon as the dimensions agree, for instance for two quadratic Gröbner bases with the same leading monomials (`ShuffleBar.finrank_J_inf_C_add`, `ShuffleBar.KD_eq_grW_of_isGroebner`): the Rees family of the Koszul dual cooperad is flat | `ShuffleGraded.lean` | **proved** |
| **Signs of the fully cut bar trees**: the inversions of a list and their sign (`ListInv.sgn`), moving an entry to the front (`ListInv.sgn_move`) and exchanging two values (`ListInv.sgn_swap`); the key and the right label of each vertex of a shuffle monomial (`LTree.vlist`), kept outside a replaced subtree (`LTree.vlist_replaceAt`); the three monomials of arity three (`LTree.mono3_cases`) and their sign `chi3 = (+1, -1, -1)`; the orientation sign of a monomial (`LTree.tauS`, the sign of its right labels in the order of the keys) and the sign of an edge in the bar differential (`LTree.topSgn`): **substituting the monomials `σ` of arity three at an edge, the sign of the new edge times the orientation sign is `± chi3(σ)`, the sign `±` depending only on the edge** (`LTree.topSgn_mul_tauS_substAt`) | `ListInv.lean`, `ShuffleVData.lean` | **proved** |
| **Bar trees with one uncut edge**: on a monomial with distinct labels the key of a vertex determines its path (`LTree.eq_of_key_subtreeAt`) and a flag says whether the key is cut (`ShuffleBar.flagAt_eq`), so such a bar tree has one uncut vertex below the root (`ShuffleBar.eq_of_flagAt_eq_false`); a plugged monomial of arity three determines the monomial and its inputs (`LTree.plug_inj`); the substitutions at the uncut edges sort these bar trees into classes (`ShuffleBar.substBar_eq_substBar`, `ShuffleBar.substBar_eq_iff`, `ShuffleBar.substBar_injective`), and **a chain of degree `n - 2` lies in the relator subcomplex exactly when its coefficients along the substitutions at every uncut edge form a relator** (`ShuffleBar.mem_J_iff_winCoef`) | `ShuffleBarEdge.lean` | **proved** |
| **The Koszul dual operad of a shuffle operad**: the Koszul dual relators, orthogonal to `R` for the pairing twisted by `chi3` (`ShuffleBar.dualRel`, `dualRel_dualRel`, `finrank_dualRel`); the fully cut bar trees are the monomials, twisted by the orientation sign (`ShuffleBar.toMono`, `ShuffleBar.ofMono`), and by the coherence of the signs the differential of a chain of top degree has coefficients `± chi3(σ)` times its values along every edge (`ShuffleBar.d_ofMono_substBar`, `ShuffleBar.winCoef_d_ofMono`): **the Koszul dual cooperad is the space of functions on the monomials whose twisted values at the substitutions at each edge form a relator** (`ShuffleBar.KD_equiv_KDmono`), **the orthogonal of the ideal of the Koszul dual relators** (`ShuffleBar.KDmono_eq_orthogonal`); so **the Koszul dual operad has the dimension of the Koszul dual cooperad in every arity** (`ShuffleBar.finrank_quotient_dualRel`), and for a quadratic Gröbner basis **the number of monomials all of whose windows are leading** (`ShuffleBar.finrank_quotient_dualRel_eq_ncard`) | `ShuffleKoszulOperad.lean` | **proved** |
| **The associated graded of the Koszul dual operad**: the associated graded of a space of functions on a finite set (`Graded.grF`, `Graded.finrank_grF`); for a diagonal pairing, **the orthogonal of the associated graded is the associated graded of the orthogonal for the reversed weight** (`Graded.orthogonal_grF`); the fully cut bar trees keep the weight (`ShuffleBar.map_toMono_grW`), so if the Koszul dual cooperad of `R₀` is the associated graded of that of `R`, **the ideal of the Koszul dual relators of `R₀` is the associated graded of that of `R` for the dual filtration** (`ShuffleBar.idealOf_dualRel_eq_grF`, a PBW property of the Koszul dual operad), and in arity three **the Koszul dual relators of `R₀` are the leading forms of those of `R`** (`ShuffleBar.idealOf_three`, `ShuffleBar.dualRel_eq_grF`); both hold for two quadratic Gröbner bases with the same leading monomials (`ShuffleBar.idealOf_dualRel_eq_grF_of_isGroebner`) | `ShuffleGradedDual.lean` | **proved** |
| **The Rees module of a weight filtration** and **the Rees family of the Koszul dual cooperad**: for a subspace `V` of `K^α` filtered by a weight, its Rees module over `K[X]` (`Graded.rees`), spanned by the homogenizations (`Graded.homog_mem_rees`, `Graded.eq_sum_homog`); **its fibers** are `V` at `X = 1`, its associated graded at `X = 0` and `V` rescaled by `c^{-W}` at `X = c ≠ 0` (`Graded.evalAt_rees_one`, `Graded.evalAt_rees_zero`, `Graded.evalAt_rees_of_ne_zero`); **it is flat**, an element vanishing at `X = c` being divisible by `X - c` (`Graded.exists_eq_smul_of_evalAt_eq_zero`), **free of rank the dimension of every fiber** (`Graded.free_rees`, `Graded.finrank_rees`), and over an infinite field **the module of polynomial sections of its fibers** (`Graded.mem_rees_iff_evalAt`, `Graded.sections_fiber`); for shuffle operads, the Koszul dual cooperad of the relators rescaled by `c^{-w}` is the rescaled Koszul dual cooperad (`ShuffleBar.KDmono_rescale_pow`), so if the Koszul dual cooperad of `R₀` is the associated graded of that of `R`, **the Rees module of the Koszul dual cooperad of `R` is the family of the Koszul dual cooperads of the rescalings of `R`, degenerating to that of `R₀`** (`ShuffleBar.fiber_rees_KDmono_of_ne_zero`, `ShuffleBar.fiber_rees_KDmono_zero`, `ShuffleBar.finrank_rees_KDmono`, `ShuffleBar.sections_KDmono_eq_rees`) | `ReesModule.lean`, `ShuffleReesKD.lean` | **proved** |
| **The Koszul dual of a shuffle operad with a quadratic Gröbner basis is Koszul**: in arity three every monomial outside the leading monomials `L` is the least monomial of a Koszul dual relator (`ShuffleBar.exists_dualRel_lead`); for the reversed key the monomials with a window outside `L` lead vectors of the ideal of the Koszul dual relators and the monomials all of whose windows lie in `L` span a complement of it (`ShuffleBar.isLeading_dual`, `ShuffleBar.isCompl_dual`, by reduction and the dimension of the Koszul dual operad); so the Koszul dual relators have Gröbner data (`ShuffleBar.dualData`) and **the Koszul dual operad is Koszul** (`ShuffleBar.isKoszul_dualRel`) | `ShuffleDualKoszul.lean` | **proved** |
| **The cobar construction of the Koszul dual cooperad**: the cobar differential cuts an uncut edge and is the transpose of the bar differential for the pairing in which bar trees are orthonormal (`ShuffleBar.δ`, `ShuffleBar.pairL_d_δ`, `ShuffleBar.δ_δ`); the cobar construction is the dual of the bar construction of the Koszul dual operad, the chains orthogonal to its relator subcomplex (`ShuffleBar.CobarOf`, `ShuffleBar.Cobar`, `ShuffleBar.δ_mem_cobarOf`); a chain orthogonal to the bar cycles is a cobar boundary (`ShuffleBar.exists_δ_eq`), so it is exact below the top degree when the Koszul dual operad is Koszul (`ShuffleBar.exact_cobarOf`), and its top-degree boundaries are the ideal of the relators (`ShuffleBar.map_δ_cobar_top`); **for a quadratic Gröbner basis the cobar construction of the Koszul dual cooperad is a resolution of the operad** (`ShuffleBar.cobar_resolution`) | `ShuffleCobar.lean` | **proved** |
| **Contexts in shuffle monomials**: grafting commutes with taking and replacing subtrees (`LTree.plug_plug`, `LTree.subtreeAt_plug`, `LTree.replaceAt_plug`, `LTree.replaceAt_append`, `LTree.replaceAt_plug_leafPos`), and grafting inputs whose least labels increase keeps the windows and grafts their inputs (`LTree.windowRoot_plug`, `LTree.winIns_plug`); **a context** — a vertex whose subtree is a small monomial with inputs grafted in increasing order of least labels (`LTree.IsCtx`) — keeps the monomials and the order of the path-lexicographic keys when the small monomial is replaced (`LTree.IsCtx.ctx_mem_monomials`, `LTree.IsCtx.pathKey_ctx_lt`), and substituting at an edge of the small monomial or of an input is substituting there (`LTree.substAt_ctx`, `LTree.substAt_ctx_ins`); the window of an edge is a context of arity three (`LTree.isCtx_window`) and the subtree spanned by two adjacent edges, truncated and standardized, one of arity four (`LTree.trunc`, `LTree.plug_trunc`, `LTree.isCtx_std`, `LTree.exists_ctx4`); two edges are adjacent, nested in an input of a window, or in disjoint subtrees, where substitutions commute (`LTree.edge_below_cases`, `LTree.path_cases`, `LTree.substAt_comm_of_diverge`) | `ShuffleContext.lean` | **proved** |
| **The syzygies of a quadratic Gröbner basis are generated in arity four**: an abstract Schreyer argument — generators with a leading monomial, any two at the same monomial agreeing modulo lower ones, have no relations beyond those of lower ones (`schreyer`), with standard representations (`exists_mem_span_fst`); the relators are combinations of the normalized leading relators (`LTree.lrel`, `LTree.mem_span_lrel`), every placement is a leading placement (`LTree.exists_lpos_pairOf`, `LTree.syzSpan_le`), and two leading placements at a monomial agree modulo lower ones — by commuting substitutions at disjoint edges (`LTree.spair_comm`, `LTree.spair_nested`, `LTree.spair_diverge`) and by the reduction in arity four at adjacent edges (`LTree.spair_ctx4`); so **a cochain on the relators killing the syzygies of arity four kills those of every arity** (`LTree.KillsSyz`, `LTree.killsSyz_of_four`) and **extends uniquely to the ideal**, a linear map on it taking each relator placed at an edge to its image placed there (`LTree.killsSyz_iff_exists_ext`, `LTree.exists_idealExt`, `LTree.idealExt_unique`) | `ShuffleSyzygy.lean` | **proved** |
| **Monoids for Day convolution are lax monoidal functors** (Day): on Mathlib's Day convolution monoidal structure on `C ⥤ V` (`DayFunctor`), the units of the Day convolution and their whiskerings, associator and unitors (`DayMonoid.ηa`, `DayMonoid.η_associator`, `DayMonoid.ν_leftUnitor`), maps out of a Day convolution and of a double one determined on the units (`DayMonoid.tensor_ext`, `DayMonoid.tensor₂_ext`); a monoid gives a lax monoidal functor and conversely (`DayMonoid.laxMonoidalOfMonObj`, `DayMonoid.monObjOfLaxMonoidal`), **inversely** (`DayMonoid.monObjEquivLaxMonoidal`), monoid morphisms being the monoidal natural transformations (`DayMonoid.isMonHom_iff`); for `C` symmetric, **the commutative monoids are the lax braided functors** (`DayMonoid.isCommDay_iff`, `DayMonoid.laxBraidedOfCommDay`, `DayMonoid.isCommDay_of_laxBraided`) | `DayUnits.lean`, `DayMonoid.lean` | **proved** |
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

**Total composition.** May's definition of an operad by total composition
`γ x y : P (Σ a, B a)` is equivalent to the partial-composition definition used here.
`Operad/MayOperad.lean` builds total composition from partial composition and proves May's axioms
(equivariance, the unit laws, and associativity along `Equiv.sigmaAssoc`); in modules it is
multilinear (`SymOperad.totalL`). `Operad/MayClass.lean` builds partial composition from total
composition and proves that the two constructions are inverse to each other
(`MaySetOperad.toSetOperad_toMaySetOperad`, `MaySetOperad.toMaySetOperad_toSetOperad`).

**Species, free operads and free algebras.** `Operad/SpeciesOp.lean` has species of sets and of
modules indexed like operads, with the skeleton (a morphism of species is an equivariant family on
the `Fin n`). `Operad/FreeSpecies.lean` builds the free operad on a set species and on a linear
species, with their universal properties (`FreeSp.homEquiv`, `FreeL.homEquiv`).
`Operad/Schur.lean` presents the Schur functor `S(P, V) = ⊕ₙ P(n) ⊗_{Σₙ} V^{⊗n}` as a module, and
`Operad/FreeAlgebra.lean` makes it the free `P`-algebra on `V`. Operations act by total composition,
every algebra acts through total composition (`SymAlgebra.act_total`), and morphisms of algebras out
of `S(P, V)` are the linear maps out of `V` (`Schur.liftEquiv`). `Operad/ComAlgebra.lean` shows
that algebras over `Com` are commutative algebras (`ComAlg.toCommRing`, `ComAlg.ofCommAlgebra`,
`ComAlg.homEquiv`) and that the free `Com`-algebra is Mathlib's `SymmetricAlgebra`
(`Schur.isSymmetricAlgebra_com`). `Operad/SymCooperad.lean` has symmetric cooperads with
infinitesimal decompositions `C (Without A i ⊕ B) → C A ⊗ C B`, their morphisms, the operad
structure on the linear dual of a cooperad (`SymCooperad.instSymOperadDual`), and the commutative
cooperad, whose dual is `Com`.

**Shuffle operads.** `Operad/ShuffleOperad.lean` defines shuffle operads on ordered species, with
partial compositions along shuffles (`IsShuffle`), their morphisms, ideals and quotients, and the
forgetful functor from symmetric operads (`SymOperad.toShuffle`), which transports morphisms,
ideals and quotients. `Operad/ShuffleIdeal.lean` shows that every relabelled composite is a shuffle
composite of relabelled operations, and that the forgetful image of the ideal generated by
relators is the shuffle ideal generated by all their relabellings (`SymOperadIdeal.toShuffle_span`),
so presentations are transported; the underlying shuffle operad of a presented operad is generated
by the relabelled generators (`Pres.shuffle_hom_ext`). `Operad/PlanarFree.lean` shows that planar
trees of any arity form the free non-symmetric set operad (`TreeOfArity.homEquiv`), and that the
free symmetric set operad on generators of any arity is the regular operad of planar trees
(`FreeReg.regIso`), with a basis and the dimension `n!` times the number of planar trees.

**Colored operads.** `Operad/Colored.lean` defines colored operads in the species convention, with
relabellings and partial compositions carrying proofs that the colors match (`ColOperad`), their
morphisms, the endomorphism colored operad of a family of modules (`ColEnd.instColOperad`) and
algebras over colored operads (`ColAlgebra`). Operads are one-colored operads
(`SymOperad.toCol`, with the same morphisms `SymOperad.colHomEquiv`) with the same algebras
(`SymOperad.colAlgebraEquiv`).

**Cyclic operads.** `Operad/Cyclic.lean` defines cyclic operads in the entries-only form: a linear
species with gluings `C X → C Y → C ((X ∖ a) ⊔ (Y ∖ b))` of an entry of one operation to an entry
of another, equivariant, commutative and associative, with a two-entry unit (`CycOperad`). Its
underlying operad `A ↦ C (Option A)` (`CycOperad.toSymOperad`) carries the extended symmetric
action by all bijections of the entries, which fixes the unit and is compatible with composition
in the sense of Getzler–Kapranov (`CycOperad.reroot_comp_inl`, `CycOperad.reroot_comp_inr`); the
commutative cyclic operad has underlying operad `Com`. `Operad/CyclicExt.lean` proves the
converse: on a species vanishing on empty sets of entries, **cyclic operad structures are the
operad structures on `C ∘ Option` with a compatible extended action** (`CycOperad.extEquiv`), the
gluing being recovered by rooting at any entry (`CycOperad.compX_root`, `CycOperad.compX_eq_compY`).

**Homological algebra.** `Operad/Perturbation.lean` has the homology of a module with a square-zero
endomorphism, induced maps of chain maps and their invariance under chain homotopy, contractions
(strong deformation retracts with the side conditions), which induce isomorphisms on homology
(`Contraction.homologyEquiv`), and **the homological perturbation lemma** (`Contraction.perturb`):
a perturbation `δ` of the differential with `1 - δ h` invertible transfers the contraction, with
explicit formulas, the key identity being `d A + A d + A ι π A = 0` (`Contraction.perturb_key`).

**Koszul signs and A∞-algebras.** `Operad/KoszulSign.lean` treats a super module as a module with
an involution `ε`; inserting a homogeneous operation of parity `q` into a slot twists the inputs
before it by `ε^q` (`End.kcompFin`). Sequential associativity holds on the nose and parallel
associativity up to the Koszul sign (`End.kcompFin_assoc_seq`, `End.kcompFin_assoc_par`), so the
Koszul circle product satisfies the graded pre-Lie identity (`End.kstar_assoc_symm`), an odd
operation cancelling against itself without division by two (`End.kstar_kstar_odd`).
`Operad/AInfinity.lean` extends this to families of all arities (`AInf.tstar`,
`AInf.tstar_assoc_symm`), defines A∞-structures in the bar convention as odd families with
`b ⋆ b = 0` (`AInf.IsAInf`), proves that **the Hochschild differential of an A∞-structure squares
to zero** (`AInf.hoch_hoch`), and identifies dg algebras with the A∞-structures concentrated in
arities one and two (`AInf.isAInf_dga_iff`).

**Gerstenhaber and BV algebras.** `Operad/GerBV.lean` proves **Koszul's theorem**: for a graded
commutative product and an odd operator `Δ` with `Δ² = 0` of order at most two (a BV algebra,
`GerBV.IsBV`), the derived bracket `[x, y] = σ|x| (Δ(xy) - Δ(x) y - σ|x| x Δ(y))` is a Gerstenhaber
bracket: graded antisymmetric, a graded derivation of the product, satisfying the graded Jacobi
identity, with `Δ` a derivation of it (`GerBV.IsBV.bracket_antisymm`, `bracket_mul_right`,
`bracket_jacobi`, `GerBV.Δ_bracket`). The Jacobi identity needs only `Δ² = 0` and the order
condition (`GerBV.dev_jacobi`).

**Graded and dg operads.** `Operad/DGOperad.lean` defines graded operads in super modules, with a
parity decomposition preserved by relabellings and compositions and parallel associativity up to
the Koszul sign (`GrOperad`), and dg operads, with an odd differential satisfying the Leibniz rule
`d (x ∘ᵢ y) = d x ∘ᵢ y + ε x ∘ᵢ d y` (`DGOperad`). **The homology of a dg operad is a graded
operad** (`DGOperad.instGrOperadHomology`): composites of cycles are cycles, composites with a
boundary are boundaries, and the axioms descend to homology, through homogeneous representatives
for parallel associativity.

**The diamond lemma and Gröbner bases in any arity.** `Operad/Diamond.lean` proves **Bergman's
diamond lemma** for linear rewriting on a free module with a well-founded order: the irreducible
monomials span a complement of the rewriting ideal if and only if every ambiguity is resolvable
relative to the order (`Rewriting.resolvable_iff`), with the normal form deciding membership in
the ideal and the irreducible monomials a basis of the quotient (`Rewriting.Resolvable.basis`).
`Operad/DiamondCtx.lean` specializes it to rules applied inside contexts (`CtxOrder`, `Rules`):
the ideal is generated by the relations (`Rules.ideal_eq_span`), disjoint ambiguities are always
resolvable, resolvability passes along factorizations, and **the Buchberger criterion**
(`Rules.isCompl_of_crit`) reduces everything to the critical ambiguities. `Operad/ShuffleAny.lean`
introduces **shuffle trees with generators of any arity** (`STree`), with substitution,
positions, replacement and truncation, and `Operad/ShuffleAnyGroebner.lean` makes them a rewriting
setting: monomials on finite sets of leaves, contexts, admissible orders (`STree.AdmOrder`), and
**the classification of ambiguities** — two occurrences of leading monomials are at incomparable
positions, or one is inside an input of the other, or they overlap and the ambiguity factors
through the truncation to their union (`STree.classify`). So **the Buchberger criterion holds for
shuffle operads with generators of any arity** (`STree.isCompl_of_critical`,
`STree.basisOfCritical`): if the critical ambiguities, whose monomials are covered by two
overlapping leading monomials, are resolvable, the normal monomials are a basis of the presented
operad in every arity. `Operad/ShuffleAnyOrder.lean` constructs **the path-lexicographic order**
from the words of the leaves (`STree.pathLex`) and proves it admissible (`STree.pathLexOrder`).

**Bergman's diamond lemma for free algebras and the Poincaré–Birkhoff–Witt theorem.**
`Operad/DiamondWords.lean` is the same theory for words, compared degree-lexicographically, with
the contexts `w ↦ u ++ w ++ v`: ambiguities are disjoint or factor through the segment covered
by two overlapping leading words (`Words.classify`), so the critical ambiguities decide everything
(`Words.isCompl_of_critical`). `Operad/PBW.lean` applies it to the quadratic-linear presentation
of the universal enveloping algebra — the classical instance of inhomogeneous Koszul duality —
and proves **the Poincaré–Birkhoff–Witt theorem** for a Lie algebra with a basis over any
commutative ring: the products of the basis vectors along nondecreasing words are a basis of
`UniversalEnvelopingAlgebra R g` (`PBW.basis`, `PBW.basis_apply`). The critical ambiguities are the
words `k j i` with `i < j < k`, resolved by the Jacobi identity (`PBW.overlap_res`); the quotient of
the free module on words by the ideal of the rules is the enveloping algebra (`PBW.quotEquiv`),
through the action of the Lie algebra on the quotient by left multiplication. In particular the
canonical map `g → U g` is injective for every Lie algebra which is free as a module
(`UniversalEnvelopingAlgebra.ι_injective_of_free`).

**PBW implies Koszul in any arity.** `Operad/ShuffleAnyBar.lean` builds **the bar construction of
the free shuffle operad** on generators of any arity: bar trees are monomials whose vertices carry
a flag saying whether the edge above is cut; a vertex is named by the least leaf and the number of
vertices of its subtree, names which are distinct in a monomial (`STree.nodup_vkeys`); merging
along each cut edge with the sign of its position among the cuts is a differential squaring to
zero (`STree.Bar.d_d`). For homogeneous rules `G`, the **flagged rules** `G.bar` rewrite a leading
monomial at an uncut edge; their ideal is a subcomplex (`Rules.bar_d_mem_ideal`), and the quotient
is the bar construction of the operad presented by `G`. `Operad/ShuffleAnyBarNormal.lean` shows
that the critical ambiguities of the flagged rules have no cut edge (`Rules.critical_cuts`), so
they are flagged images of ambiguities of `G` and **resolvability passes to the bar
construction** (`Rules.bar_resolvable`): a PBW basis of the operad gives a basis of normal bar
trees. `Operad/ShuffleAnyKoszul.lean` shows that **normality is local** for quadratic rules — a
bar tree is normal exactly when the edges whose window is leading are cut
(`Rules.bar_normal_iff_quad`) — and proves **PBW implies Koszul**
(`Rules.isKoszul_of_resolvable`, and `Rules.isKoszul_of_critical` from the critical ambiguities):
the homology of the bar construction vanishes below the diagonal in every arity. The proof is
Hoffbeck's, through two abstract tools in `Operad/Hoffbeck.lean`: complexes of cuts, whose
differential restricted to the non-leading cuts is contracted by cutting along a non-leading edge
(`CutComplex.dL_hL_add`), and the filtration argument over a well-founded order, by induction in
the Dershowitz–Manna order on finite sets (`Hoffbeck.exact_of_leading`).

**Inhomogeneous presentations.** `Operad/ShuffleAnyInhom.lean` treats rules whose tails have at
most as many vertices as their leading monomials, such as quadratic-linear rules. Contexts shift
weights uniformly (`STree.IsSCtx.weight_add`), so every admissible order has a weight-graded
refinement (`STree.AdmOrder.byWeight`). The **leading part** `G.top` keeps the top-weight terms
of the tails; over a weight-graded order, **the leading part of a resolvable presentation is
resolvable** (`Rules.top_resolvable`), so the quadratic part of a quadratic-linear presentation
with a PBW basis is Koszul (`Rules.top_isKoszul`). **The PBW theorem** (`Rules.pbw`,
`Rules.grEquiv`): a combination of monomials of weight `n` is congruent to one of lower weight
modulo the relations exactly when it lies in the ideal of the leading part, that is, the
associated graded of the filtered operad presented by `G` is the operad presented by `G.top`.

**The homotopy transfer theorem.** `Operad/HTT.lean` proves Kadeishvili's theorem in the form of
Kontsevich–Soibelman and Merkulov: for a dg algebra `(V, d, μ)` in the bar convention and a
retraction onto the image of an even idempotent `e` with an odd homotopy `h` (`h d + d h = e - 1`),
the operations `b'₁ = e d e`, `b'ₙ = e ∘ ∑ μ (f, f)` over planar binary trees with `e` on the leaves
and `h` on the internal edges form an **A∞-structure** (`HTT.isAInf_transfer`,
`HTT.isAInf_transfer_of_dga`). The trees themselves satisfy the ∞-morphism equation
`d ∘ f + μ (f, f) = f ⋆ b'` (`HTT.morphism_eq`). The proof is an induction on the arity through the
Leibniz rule, associativity and the insertion law for binary composites of families
(`HTT.comp_BIN`, `HTT.BIN_assoc`, `HTT.tstar_BIN`); the side conditions on `h` are not needed.

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
