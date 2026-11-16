# Completing `ROADMAP.md`

Written 2026-11-15 against `main` at 9badf6e (274 modules, sorry-free). The work closes every row
of every phase of `ROADMAP.md`, along with every "started", "planned", "open", "not done" and
"in progress" clause. Mathlib pull requests are out of scope. Publishing the doc-gen4 site waits
on the owner enabling GitHub Pages.

Each work package below (W1, W2, ...) is one branch and one PR. A package that needs another is
stacked on it. Sizes count new Lean lines. Days are wall-clock days for one session, at about
1.5k lines a day for routine material and about 1k for sign-heavy dg material. The pace of the
symmetric bridge was 27k lines in 12 days with up to three agents in parallel.

## Status

| package | state | where |
|---|---|---|
| W0 | PR open | `completion-plan-2026-11-15` |
| W5 | PR open | `w5-groebner-koszul-2026-11-15`, `SymGroebner.lean` |
| W1 | PR open | `w1-free-linearization-2026-11-15`, `FreeLin.lean` |
| W3 | PR open | `w3-shuffle-isos-2026-11-15`, `ShufflePresIso.lean`, `ShuffleIsoComAss.lean`, `ShuffleIsoPoisLie.lean` |
| W2 | PR open | `w2-rees-2026-11-15`, `PolyOperad.lean`, `ScalarRestriction.lean`, `ReesFiber.lean`, `BaseChange.lean`, `ReesWeight.lean` |
| W6 | PR open | `w6-hypercom4-2026-11-15`, `HyperComModel.lean`, `HyperComFour.lean` |
| W7 | PR open | `w7-koszul-dual-cooperad-2026-11-15`, `DualCooperad.lean`, `CooperadTranspose.lean`, `KoszulDualCooperad.lean` |
| W4 (a) | PR open | `w4a-lie-in-ass-2026-11-15`, `LieAss.lean`; `w4a-lie-groebner-2026-11-15`, `ShuffleAnyLie.lean` (the Gröbner basis of the Jacobi rule, `dim Lie(n) = (n - 1)!`) |
| W4 (b) | PRs open | `w4b-prelie-trees-2026-11-16` (#28), `PreLieTrees.lean` and five supporting files: `PreLie(A) ≅ R[rooted trees on A]` and `dim PreLie(n) = nⁿ⁻¹`; `w4b-prelie-insertion-2026-11-16`, `PreLieInsertion.lean` and `RootedTreeOps.lean`: the composition in the basis of trees is insertion at a vertex (the tree operad is the transported one, not built separately) |
| W10 | PR open | `w10-bar-adjunction-2026-11-15`, `BarAdjunction.lean`; with today's `CutCofreeConil`, so with its projectivity hypothesis, which holds over a field |
| W11 | PRs open | `w11-deformation-complex-2026-11-15`, `DeformationComplex.lean`: the complex and its cocycles of weight one (targets 1 and half of 2); `w11-obstructions-2026-11-15`, `TruncOperad.lean`, `ConvCoef.lean`, `InvObstruction.lean`, `DeformationLift.lean`: target 3; `w11-inner-derivations-2026-11-16`, `DeformationInner.lean`: the inner derivations (the rest of target 2) |
| W12 | PRs open | `w12-ql-dual-2026-11-16`, `KoszulInhom.lean`, `SpRetraction.lean`: item 1, in the graded symmetric setting, with the PBW property in weights one and two as the hypothesis, and the reduction of item 2 to the comparison morphism `(qP^¡, d_φ) → B(P, I)` being a quasi-isomorphism; `w12-ql-resolution-2026-11-16`, `KoszulInhomRes.lean`, `KoszulInhomQIso.lean`: item 2, with the PBW property in every weight as a hypothesis. Item 3 is a stretch item |

W3 as done differs from its target below in two ways. For `Com` and `Ass` the isomorphism is
with the operads without unit `Lin K ComSet` and `Lin K AssSet`, because `Sym.Com K` and
`Sym.Ass K` have the component `K` on the empty set and a presented shuffle operad has none;
with `Sym.Com` and `Sym.Ass` the morphism is bijective on every nonempty finite linear order.
For `Lie` the rule is the Jacobi rule on one generator, and injectivity goes through `Pois`,
the library having no dimension of `Lie` at that point. That the Jacobi rule is a Gröbner basis, and
`dim Lie(n) = (n - 1)!`, are proved with W4 (a), in `ShuffleAnyLie.lean`.

## Decisions, 2026-11-15

The cuts proposed below are accepted.

1. `HyperCom`: dimensions for `n ≤ 4`. The general dimensions are out of scope.
2. W12: items 1–2. Item 3, the any-arity bridge, is a stretch item.
3. W13: items 1–3. Item 4 is deferred; the alternative is the identification of `P∞`-algebras
   for `P = Lie, Com, Ass` with `L∞`, `C∞` and `A∞`.
4. W8 item 2: settle whether the statement holds. If it fails, prove the counterexample or the
   corrected statement and record it in `ROADMAP.md`.
5. One session works through the packages in the order given under "Totals".
6. W8 moves to the end, as a stretch item. The generality target is that of Loday–Vallette, a
   field of characteristic zero, where every module is projective and today's `CutCofree`
   applies. So W10 and W13 item 3 are stated over a field, and their docstrings and `ROADMAP.md`
   rows say so. W8 item 2 is settled in a short note, and blocks nothing. W9 keeps its
   dependency on W8 item 1 and moves with it.

## What is already closed but still reads as open

Checked against the code. Nothing new has to be proved for these; the text is stale.

| where | stale clause | why it is closed |
|---|---|---|
| L11 | "still open are the underlying shuffle operad of `FreeL R E` as a free shuffle operad on a basis of `E(2)` … and `B(P, I)` as the shuffle bar construction modulo `ShuffleBar.J`" | bridge step 1 (`ShuffleFreeL`: `FreeL.toFreeSh`, `shuffleBasis`, `binBasis`) and step 2c (`ShuffleBarJ.isKoszul_iff_shuffle`) |
| L11 | "the comparison of the shuffle and symmetric bar complexes … which would carry these to `Koszul.IsKoszul`" | steps 2b and 2c (`ShuffleBarSymExp`, `ShuffleBarJ`), and step 3 proves `Com`, `Lie`, `Ass`, `Pois` `Koszul.IsKoszul` |
| P4 | "The shuffle Koszul notions are not yet related to `Koszul.IsKoszul` … the bar complexes are not compared" | closed **for binary generators**: `Koszul.IsKoszul ↔ ShuffleBar.IsKoszul` (2c), `ShuffleBar.IsKoszul ↔ Rules.IsKoszul` (`ShuffleBridge`). Open only for generators of other arities (W12) |
| `GrKoszulDual.lean` docstring | "the comparison of `Koszul.IsKoszul` with … is open" | same as the row above |
| `SetHadamard.lean` docstring | "That these relations present `Dias` and `Trias` is not proved here" | proved in `DiasTrias.lean`; the docstring should point there |
| README, "Roadmap" item 1 | "The product itself is still to build" | built in `Composite`, `CompositeAssoc`, `OperadMonoid` |
| P6b | "in progress" | linters pass and the `docs.yml` workflow exists; the remaining step, enabling Pages, belongs to the owner |

Still open in L11, and real: the isomorphisms of *shuffle operads* `Shuf (Sym.Com) ≅` the
presented shuffle operad of `ShuffleAnyCom`, and likewise for `Sym.Ass`, `Lie` and `Pois`.
`ShuffleAnyAss.lean` and `ShuffleAnyPois.lean` say "not constructed". Step 3's `SymPresIso`
gives isomorphisms with the `BinPres` operads, but not with these shuffle quotients. This is W3.

## Work packages, in dependency order

### W0 — documentation truth pass (no new mathematics)
Fix every stale clause in the table above, in `ROADMAP.md`, `README.md` and the three docstrings.
Mark P6b done, with Pages flagged as the owner's step.
*Size* about 100 lines of prose. *Time* 0.5 day. *Depends on* nothing.

### W1 — L14: the free operad on a linearized set species
**Target.** For a set species `X`, `FreeL R (Lin X) ≅ Lin R (FreeSp X)` as symmetric operads,
compatible with the generators: both satisfy the same universal property, through
`FreeL.homEquiv`, `FreeSp.homEquiv` and `linHomEquiv`. As a corollary, `FreeL R (Lin X)` has
the basis `FreeSp X`, which recovers `FreeBinary`'s count for binary generators.
*Size* 0.5–1.2k. *Time* 0.5–1.5 days. *Depends on* nothing.

### W2 — L6: filtered operads in general, the Rees operad over `R[ħ]`, base change
**Targets.**
1. For a filtered symmetric operad `(P, F)` (`SymOperadFiltration`), **the associated graded**
   `gr P`, a symmetric operad with `gr_p = F_p / F_{p-1}`.
2. **The Rees operad** `Rees P = ⊕ₚ F_p ħᵖ`, a symmetric operad over `R[ħ]`.
3. **Specialization**: `Rees P / (ħ - 1) ≅ P` and `Rees P / ħ ≅ gr P`, as operads over `R`.
4. **Base change** along a ring map `R → S`: `S ⊗_R P` as a symmetric operad over `S`, with
   its universal property among `S`-operads.
5. For a weighted set operad, the existing `TwLin`/`Gr` family is the instance of this
   construction.

*Size* 2–4k. *Time* 2–4 days. *Depends on* nothing.

### W3 — L11: shuffle-operad isomorphisms with `Sym.Com`, `Sym.Ass`, `Lie`, `Pois`
**Target.** For `X ∈ {Com, Ass, Lie, Pois}`, an isomorphism of shuffle operads
`Shuf (X) ≅ ShPres (rules of X)`, the presented shuffle operad with generators of any arity
(`ShuffleFreeAny`), whose arity-wise statements are those of `ShuffleAnyCom`, `ShuffleAnyAss`
and `ShuffleAnyPois`. The route:
- `SymPresIso` gives `Koszul.Pres ≅ SymGr (BinPres X)` and, on even parts, `≅ BinPres X`;
- `ShuffleSymPres` gives symmetric presentations as presentations of the free shuffle operad;
- `ShufflePresUniv` gives maps out of the presented shuffle operad;
- the bijectivity check is arity-wise and comes from the existing dimension counts.

`Sym.Ass ≅ BinPres Ass` and `Sym.Com ≅ BinPres Com` are needed and are not present as
isomorphisms; they come from `AssPres.presIso` and `ComSet`.
*Size* 2–5k. *Time* 2–5 days. *Depends on* nothing.

### W4 — Phase 3: `Lie` inside `Ass`, and `PreLie` as rooted trees
**Targets.**
- (a) **The commutator morphism** `Lie → Sym.Ass`, injective in every arity over a field
  with `2 ≠ 0`, so that `Lie` is the suboperad of `Ass` generated by the commutator. The
  route: free algebras are faithful (`Schur.algebra_app_injective`), and `PBW` makes the free
  Lie algebra inject into the tensor algebra. Size 1–2.5k, 1–3 days.
- (b) **`PreLie` as rooted trees** (Chapoton–Livernet): the operad `RT` of labelled rooted trees
  with composition by insertion at all vertices; `RT ≅ BinPres PreLie`; `dim PreLie(n) = nⁿ⁻¹`.
  Size 4–8k, 5–10 days. This is the largest classical item, but it is textbook.

*Depends on* nothing.

### W5 — P4 (binary): Gröbner bases make symmetric operads `Koszul.IsKoszul`
**Target.** For binary quadratic data in characteristic zero, a quadratic Gröbner basis of the
shuffle relators `Rsh`, or a resolvable rule set (`ShuffleAnyKoszul`), implies
`Koszul.IsKoszul K E r`. This is the composite of `ShuffleAnyKoszul`, `ShuffleBridge` and
`ShuffleBarJ`, and step 3 is re-derived through it.
*Size* 0.3–1k. *Time* 0.5–1 day. *Depends on* nothing.

### W6 — P5: `dim HyperCom(4) = 7`
**Target.** `Module.finrank K (HyperComOp K (Fin 4)) = 7`, and the same for every `A` with four
elements. Arity four of the free operad on `m₂`, `m₃`, `m₄` is spanned by 26 trees: 15 binary,
10 mixed and 1 corolla. The ideal in arity four is spanned by explicit relator composites. The
rank is checked by a kernel-checked certificate (ranks 14, 5 and 0 by degree), never by
`native_decide`. The upper bound uses the existing induction principle (`SymSuboperad`); the
lower bound uses the rank certificate.
*Size* 1.5–3.5k. *Time* 2–4 days.
**Proposed finite cut**: `n ≤ 4`. The general formula (Keel's presentation of
`H*(M̄₀,ₙ₊₁)`, Getzler's generating function) is research-scale. `n = 5` (34) is the same method
with a larger certificate, a stretch of +2–5k and 2–5 days, done only if asked.

### W7 — L8: the planar Koszul dual cooperad
**Targets.**
1. For planar binary quadratic data `(E, R)`, the subcooperad `P^¡ ⊆ T^c(E)` of the cofree
   planar cooperad. Its arity-`n` part is the intersection, over the windows, of `R` in the
   window and `E` elsewhere.
2. `P^¡` is an `NSCooperad`, with explicit weight ≤ 3 descriptions (`P^¡(2) = E`,
   `P^¡(3) ≅ R`, and arity four as the intersection of the two windows).
3. **Duality**: `P^¡(n)* ≅ P^!(n)` arity by arity, through the annihilator of `KoszulDual.lean`.

*Size* 2.5–5k. *Time* 3–6 days. *Depends on* nothing. A cofree planar cooperad on planar trees
may have to be built first, and it is included in the range.

### W8 — the cut cooperad: existence in general (P3 `CutCofree` open cases)
**Targets.**
1. **Existence without projectivity.** For a conilpotent coaugmented graded cooperad `C` over a
   `ℚ`-algebra, every morphism `C̄ → V` lifts to `C → T^c(V)`. The construction is direct: sum
   over trees of the iterated decompositions `Δ_t`, finite by conilpotency, in place of the
   present transposition through scalar functionals.
2. **Species with elements without inputs**: investigate first, for at most one day. The
   uniqueness argument counts vertices, and with arity-zero elements a fixed arity has
   infinitely many trees. The outcome is either a proof under conilpotency or a counterexample.
   **If the statement fails, I stop and ask** rather than weaken it.

*Size* 3–6k, plus 0–3k for item 2. *Time* 4–8 days, plus 1–3. *Depends on* nothing.

### W9 — P2: the cofree conilpotent cooperad on an arbitrary linear species
**Target.** The ungraded statement: for a reduced linear species `V`, a cooperad `T^c(V)`, and
a natural isomorphism between morphisms of conilpotent coaugmented cooperads `C → T^c(V)` and
morphisms of species `C̄ → V`. The route is the even case of W8, through `EvenOp`, or a direct
copy. `CofreeCooperad` becomes the instance of a species free over a collection.
*Size* 1–3k. *Time* 1–3 days. *Depends on* W8.

### W10 — P3: the bar side of the bar–cobar adjunction
**Target.** For a conilpotent dg cooperad `C` and `P = R 1 ⊕ I`, morphisms of dg cooperads
`C → B(P, I)` correspond to twisting morphisms `C → P` with values in `I`. Composed with
`TwistingDG`, this gives `Hom(ΩC, P) ≅ Tw(C, P) ≅ Hom(C, BP)`, natural in both variables. The
new ingredient is that a coderivation of a cofree cooperad is determined by its projection to
the cogenerators.
*Size* 4–7k. *Time* 5–9 days. *Depends on* W8.

### W11 — L10 and the L12 clause: the deformation complex of a morphism and of an operad
**Targets**, for `φ : P → Q` a morphism of dg operads with `P = Koszul.Pres K E r` quadratic:
1. **The deformation complex** `Def(φ) = Hom_𝔖(P^¡, Q)`, with differential `∂ + [φκ, −]`, a
   complex because `φκ` is a twisting morphism (`InvLie`). Its cohomology is `Hⁿ(φ)`. The
   deformation complex of `P` is the case `φ = id`.
2. **`H¹`**: the 1-cocycles are the derivations of `P` along `φ` (`DerivationAlong`), and the
   1-coboundaries are those inner to `Q(1)`. So `H¹(φ)` is derivations modulo inner ones. As
   done: the two statements, without the quotient, the cochains being graded by parity only.
3. **`H²` and obstructions**: a lift of `φ` to `Q[t]/tⁿ⁺¹` extends to `Q[t]/tⁿ⁺²` iff its
   obstruction class in `H²(φ)` vanishes. As done: the cochains are graded by parity only, so
   the vanishing is stated as the obstruction being minus the differential of a cochain of
   weight one with values in the cycles. The complex `Hom_𝔖(P^¡, P)` is not compared with the
   cochains of `FormalDeformation`; that comparison is the stretch item W14.

*Size* 3–6k. *Time* 4–8 days. *Depends on* nothing, though it is best after W10.

### W12 — P4: inhomogeneous Koszul duality, and the any-arity bridge
**Targets.**
1. For a quadratic-linear presentation with the PBW property (`ShuffleAnyInhom`), **the Koszul
   dual dg cooperad** `(qP^¡, d_φ)`: the derivation induced by `φ : qR → E` squares to zero.
2. **The resolution**: `Ω(qP^¡, d_φ) → P` is a quasi-isomorphism, by the weight filtration and
   the comparison lemma, from the homogeneous case (`KoszulCriterion`, `CobarWeight`).
3. *(any-arity bridge)* `Koszul.IsKoszul ↔` the shuffle notion for generators of any arity,
   generalizing steps 2b and 2c from `ShuffleBar` to `ShuffleAnyBar`.

*Size* 5–10k for items 1–2, and 8–15k for item 3. *Time* 6–12 days, plus 7–14.
**Ambiguous "done"**: the P4 sentence "the shuffle Koszul notions are not yet related" is closed
for binary generators. **Proposed cut**: items 1–2 plus W5, with item 3 done only if you want the
any-arity generality.

### W13 — L13 and P3: homotopy algebras, ∞-morphisms and the homotopy transfer theorem
**Targets.**
1. **`L∞`**: ∞-morphisms of `L∞[1]`-algebras (symmetric multilinear series, as `AInfMorphism`
   is for `A∞`), their composition, and **the HTT for dg Lie algebras**: a contraction of `V`
   onto `H` transfers a dg Lie structure to an `L∞` structure on `H`, with the ∞-morphism `i∞`.
   Size 3–6k, 4–8 days.
2. **`C∞`**: ∞-morphisms, and **the HTT for commutative dg algebras**: the transferred `A∞`
   structure vanishes on signed shuffles (Kadeishvili; Cheng–Getzler). Size 2–5k, 3–6 days.
3. **Operadic HTT**: for a conilpotent graded cooperad `C`, a contraction of `V` onto `H`
   transfers twisting morphisms `C → End_V` to twisting morphisms `C → End_H`, by the tree
   formula (`p` at the root, `h` on inner edges, `i` at the leaves). With `C = P^¡` this is the
   HTT for `P∞`-algebras (`PInfinity`). Size 6–12k, 8–15 days. *Depends on* W8.
4. **∞-morphisms of `P∞`-algebras** in operadic generality, as morphisms of quasi-free
   `P^¡`-coalgebras. This needs `P^¡`-coalgebras and cofree coalgebras. Size 3–6k, 4–8 days.

**Research-scale in Lean, not in mathematics.** Items 3 and 4 carry the full Koszul-sign burden
of the tree formula in the species convention. **Proposed cut**: items 1–3. Item 4 would be
replaced by the identification of `P∞`-algebras for `P = Lie, Com, Ass` with `L∞`, `C∞` and
`A∞`. That identification is itself 3–6k per operad, so item 4 needs a decision.

### W14 — stretch: the deformation complex of a Koszul operad and `FormalDeformation`
**Target.** For a Koszul operad `P`, compare the cohomology of `Hom_𝔖(P^¡, P)` (W11) with the
`𝔖`-cochains of `Deformation.lean` and `FormalDeformation.lean`, in degrees one and two, and
match the obstruction of `Koszul.Lift` for the identity of `P` with the obstruction cocycle of
`FormalDeformation`. The two sides live in different settings: W11 is graded and symmetric, and
`FormalDeformation` is ungraded, so the comparison goes through `EvenOp` and the resolution
`Ω P^¡ → P`.

*Size* 6–12k. *Time* 8–15 days. *Depends on* W10 and W11, and on W8 for the generality of the
bar construction. A stretch item, next to W8 and W9: not started, and done only if asked.

## Totals

| package | lines, low–high (k) | days, low–high |
|---|---|---|
| W0 docs | 0 | 0.5 |
| W1 L14 | 0.5–1.2 | 0.5–1.5 |
| W2 L6 | 2–4 | 2–4 |
| W3 L11 isos | 2–5 | 2–5 |
| W4a Lie ⊆ Ass | 1–2.5 | 1–3 |
| W4b PreLie = RT | 4–8 | 5–10 |
| W5 Gröbner ⇒ `Koszul.IsKoszul` | 0.3–1 | 0.5–1 |
| W6 `HyperCom(4)` | 1.5–3.5 | 2–4 |
| W7 L8 planar `P^¡` | 2.5–5 | 3–6 |
| W8 cut cooperad existence | 3–9 | 5–11 |
| W9 P2 cofree on species | 1–3 | 1–3 |
| W10 bar side | 4–7 | 5–9 |
| W11 L10/L12 deformation complex | 3–6 | 4–8 |
| W12 inhomogeneous (items 1–2) | 5–10 | 6–12 |
| W13 items 1–3 | 11–23 | 15–29 |
| **total, with the proposed cuts** | **41–89k** | **53–107 days** |
| stretch: W6 `n = 5`; W12 item 3; W13 item 4 | +13–26k | +13–27 days |
| stretch: W14 comparison with `FormalDeformation` | +6–12k | +8–15 days |

With the cuts: 41–89k new lines and about 53–107 days for one session, which is 8–15 weeks.
Two sessions in parallel on independent packages would take about 5–9 weeks. Independent
packages: {W1, W2, W3, W4, W5, W6, W7, W11} against the chain W8 → W9, W10, W13.3. With the
stretch items the total is 54–115k lines.

**Order** (after decision 6). W0, W5 and W1 come first: they are cheap and close visible rows.
Then W3, W2, W6, W7 and W4a, then W10 and W11, then W12 and W4b, then W13. W8 and W9 come last.

## Top risks

1. **W13 (homotopy transfer in operadic generality)** is half the uncertainty in the total. The
   Koszul signs of the tree formula in the species convention are where the step-2b-style sign
   lemmas (`sign_mergeT`, `dExpansion`) cost the most. Item 4 has no settled finite form.
2. **W8 item 2 (elements without inputs)** may be false as stated, and W10 and W13.3 depend on
   W8 item 1.
3. **"Done" for P4 and P5** depends on the cuts proposed here: the binary bridge versus any
   arity, and `HyperCom` for `n ≤ 4` versus Keel's general dimensions. I need a yes on the cuts.
4. **Build cost**: a cold build takes about 41 minutes and grows with every package; machine
   contention from other sessions has doubled build times before. Every PR needs one cold gate
   (build, `runLinter`, `Audit`, `AxiomSweep`).
5. **W4b (`PreLie` as rooted trees)** is large for a Phase 3 item, and there is no smaller cut:
   the dimension `nⁿ⁻¹` already needs the full Chapoton–Livernet isomorphism.
