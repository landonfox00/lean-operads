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

2407 lines, 219 declarations, **`sorry`-free**. `Audit.lean` confirms every declaration rests
only on Lean's three standard axioms — `propext`, `Quot.sound`, and (wherever mathlib's
multilinear machinery is involved) `Classical.choice`. Never `sorryAx`.

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

1. **A graded/dg layer — and it is a real gate, not a preference.** Everything here is ungraded,
   and the Maurer–Cartan story is *not* available until that changes. Two things fail without
   signs. First, `Θ ⋆ Θ = 0` for a binary `Θ` says `Θ ∘₁ Θ = -(Θ ∘₂ Θ)`, which is
   anti-associativity, not associativity; making the equation mean what it should requires the
   operadic suspension. Second, `d² = 0` does not follow from Jacobi in an ungraded Lie ring —
   Jacobi with `x = y = Θ` degenerates to `0 = 0`, and `ad_Θ²` is genuinely nonzero in general.
   The dg layer is therefore the next substantial item, and it decorates the ungraded pre-Lie
   structure rather than replacing it.
2. **The species spine**, per the decision above.
3. **The universal property of `Free`.** `Free.lean` builds the operad of planar trees labelled
   by a collection `E` and proves all four axioms, which is the construction; what is *not* yet
   proved is that it is free — that a map of collections `E → P` extends uniquely to an operad
   morphism `Free R E → P`. Until that is done the name records the intent, not a theorem. The
   extension is a mutual recursion over trees and forests, and the forest half needs total
   composition, which the library does not yet have.
4. **A worked non-trivial example** beyond `Ass` and `End` — a concrete operad presented by
   generators and relations, which is what makes items 1 and 3 pay off.

Further out, in rough dependency order:

5. **The common operads.** Right now there are exactly two: `Ass` and `End`. `Com`, `Lie` and
   `Pois` are all *symmetric*, so they are blocked on item 2 rather than on effort; the magmatic
   operad, `uAss` and the free ns-operad on planar trees are reachable without symmetry.
6. **Operad cohomology.** Once the dg layer gives `d = ⁅Θ, -⁆` with `d² = 0`, the
   cohomology groups themselves are a further step, and cohomology in the technical sense
   (Gerstenhaber for associative algebras, André–Quillen for algebras over an operad) needs the
   dg layer of item 1.
7. **Derived operadic frameworks and their algebras.** Bar–cobar, Koszul duality, model
   structures, ∞-operads. Each of these sits on top of the dg layer, and each is a substantial
   project in its own right — this is the long-term destination, not a near-term item.

### A note for anyone taking the mathlib route later

Mathlib turns out to have more relevant API than the closed PRs suggest.
`MultilinearMap.compMultilinearMap` is *already* total (May-style) operadic composition over
`Σ i, β i` with multilinearity proved; `curryMid`, `currySum`/`uncurrySum` and `domDomCongr`
handle slot extraction; `Fin.insertNth` comes with `update_insertNth`/`insertNth_update`. That
route was not taken here — building `comp` by hand keeps it definitionally transparent, which is
what makes four axiom proofs feasible — but it is the natural basis for a general-`V` version.
