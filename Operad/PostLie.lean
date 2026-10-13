/-
# Post-Lie algebras: `ComTrias^! = PostLie`

**Vallette's theorem** (*Homology of generalized partition posets*, Thm. 30): the Koszul dual of
the operad of commutative trialgebras is the operad of post-Lie algebras.

* `BinComTrias`: Vallette's commutative trialgebras as a binary quadratic operad on `⊥` (`mid`),
  commutative, and `⊣` (`left`), with `⊥` associative, `(x ⊣ y) ⊣ z = x ⊣ (y ⊣ z) = x ⊣ (z ⊣ y)`,
  `x ⊣ (y ⊥ z) = x ⊣ (y ⊣ z)` and `(x ⊥ y) ⊣ z = x ⊥ (y ⊣ z)` (`comTriasRel`).
* `PostLie`: a Lie bracket and a product `∘` with `[x, y] ∘ z = [x ∘ z, y] + [x, y ∘ z]`
  (`BinRel.postLie₁`) and `(x ∘ y) ∘ z - x ∘ (y ∘ z) - (x ∘ z) ∘ y + x ∘ (z ∘ y) = x ∘ [y, z]`
  (`BinRel.postLie₂`).
* **`ComTrias^! = PostLie`**: over a field of characteristic zero the Koszul dual relations of
  `ComTrias` are spanned by seven explicit elements (`dualRel23_comTrias`), the Koszul dual is
  presented by the antisymmetry of `mid`, the Jacobi identity and the post-Lie relations with
  `mid` half the bracket (`dual23_comTrias`, `BinComTrias.dual23_eq`), and it is isomorphic to
  `PostLie` by `mid ↦ [-, -]/2`, `left ↦ ∘` (`BinComTrias.dualIso`).
* **The leading forms** (`BinComTriasLead`, `PostLieLead`): replacing `x ⊣ (y ⊥ z) = x ⊣ (y ⊣ z)`
  by `x ⊣ (y ⊥ z) = 0`, the Koszul dual is presented by the leading forms of the post-Lie
  relations for the filtration by the number of brackets, `∘` becoming right pre-Lie
  (`dual23_comTriasLead`, `BinComTriasLead.dual23_eq`, `BinComTriasLead.dualIso`).
* **Renaming and rescaling generators** (`FreeBin.rename`, `FreeBin.rename_binL`,
  `FreeBin.rename_binR`) gives morphisms and isomorphisms of presented operads
  (`FreeBin.BinPres.renameHom`, `FreeBin.BinPres.renameIso`).

The proof is a finite computation in arity three, checked by the kernel through the certificates of
`Operad.BinaryCert`. The relations of `ComTrias` identify monomials, so the `48` monomials of arity
three fall into classes, and the relations are spanned by the differences within a class (and, for
the leading forms, by the monomials of three classes): the paths to a root of each class bound
their dimension below by `41` (`PostLieData.ctDim`), and the signed sums of the seven surviving
classes span the dual relations (`PostLieData.ctU`). Each signed sum is an integer combination of
relabelled post-Lie relators and composites of the antisymmetry (`PostLieData.ctMemU`), and
conversely (`PostLieData.ctMemS`).
-/
import Operad.BinaryCert
import Operad.DerivationAlong

universe u v

namespace Operad

open Sym SetOperad FreeBin

/-! ## The generators and the relators -/

/-- **The generators of commutative trialgebras**: `⊥` (`mid`) and `⊣` (`left`). -/
inductive ComTriOp
  /-- `x ⊥ y`, commutative. -/
  | mid
  /-- `x ⊣ y`. -/
  | left
  deriving DecidableEq

instance : Fintype ComTriOp := ⟨{.mid, .left}, fun o => by cases o <;> simp⟩

/-- **The generators of post-Lie algebras**: the bracket and the product. -/
inductive PostLieOp
  /-- The Lie bracket. -/
  | bracket
  /-- The product `∘`. -/
  | product
  deriving DecidableEq

instance : Fintype PostLieOp := ⟨{.bracket, .product}, fun o => by cases o <;> simp⟩

section Relators

variable (R : Type u) [CommRing R] {G : Type v}

/-- The relator `x₀ ⊣ (x₁ ⊥ x₂) - x₀ ⊣ (x₁ ⊣ x₂)`, for `⊣ = l` and `⊥ = m`. -/
noncomputable def BinRel.leftMid (l m : G) : FreeBin R G (Fin 3) := binR l m 1 - binR l l 1

/-- The relator `(x₀ ⊥ x₁) ⊣ x₂ - x₀ ⊥ (x₁ ⊣ x₂)`, for `⊣ = l` and `⊥ = m`. -/
noncomputable def BinRel.midLeft (l m : G) : FreeBin R G (Fin 3) := binL l m 1 - binR m l 1

/-- The post-Lie relator `[x₀, x₁] ∘ x₂ - [x₀ ∘ x₂, x₁] - [x₀, x₁ ∘ x₂]`, for the bracket `b` and
the product `p`: the product acts on the right by derivations of the bracket. -/
noncomputable def BinRel.postLie₁ (b p : G) : FreeBin R G (Fin 3) :=
  binL p b 1 - binL b p (perm3 0 2 1) - binR b p 1

/-- The post-Lie relator `(x₀ ∘ x₁) ∘ x₂ - x₀ ∘ (x₁ ∘ x₂) - (x₀ ∘ x₂) ∘ x₁ + x₀ ∘ (x₂ ∘ x₁)
- x₀ ∘ [x₁, x₂]`, for the bracket `b` and the product `p`. -/
noncomputable def BinRel.postLie₂ (b p : G) : FreeBin R G (Fin 3) :=
  binL p p 1 - binR p p 1 - binL p p (perm3 0 2 1) + binR p p (perm3 0 2 1) - binR p b 1

/-- The relator `BinRel.postLie₂` for the bracket `2 b`. -/
noncomputable def BinRel.postLieHalf₂ (b p : G) : FreeBin R G (Fin 3) :=
  binL p p 1 - binR p p 1 - binL p p (perm3 0 2 1) + binR p p (perm3 0 2 1)
    - (2 : R) • binR p b 1

/-- **The relators of commutative trialgebras** of arity three: `⊥` associative,
`(x ⊣ y) ⊣ z = x ⊣ (y ⊣ z) = x ⊣ (z ⊣ y)`, `x ⊣ (y ⊥ z) = x ⊣ (y ⊣ z)`,
`(x ⊥ y) ⊣ z = x ⊥ (y ⊣ z)`. -/
def comTriasRel : Set (FreeBin R ComTriOp (Fin 3)) :=
  {BinRel.assoc R .mid, BinRel.assoc R .left, BinRel.perm R .left, BinRel.leftMid R .left .mid,
    BinRel.midLeft R .left .mid}

/-- **The leading forms of the relators of commutative trialgebras**, for the filtration by the
number of `⊥`: `x ⊣ (y ⊥ z) = 0` in place of `x ⊣ (y ⊥ z) = x ⊣ (y ⊣ z)`. -/
def comTriasLeadRel : Set (FreeBin R ComTriOp (Fin 3)) :=
  {BinRel.assoc R .mid, BinRel.assoc R .left, BinRel.perm R .left, binR .left .mid 1,
    BinRel.midLeft R .left .mid}

/-- **The post-Lie relators** of arity three: the Jacobi identity and the two post-Lie
relations. -/
def postLieRel : Set (FreeBin R PostLieOp (Fin 3)) :=
  {BinRel.jacobi R .bracket, BinRel.postLie₁ R .bracket .product,
    BinRel.postLie₂ R .bracket .product}

/-- **The leading forms of the post-Lie relators**, for the filtration by the number of brackets:
the Jacobi identity, the derivation relation and the right pre-Lie relation of the product. -/
def postLieLeadRel : Set (FreeBin R PostLieOp (Fin 3)) :=
  {BinRel.jacobi R .bracket, BinRel.postLie₁ R .bracket .product, BinRel.preLie R .product}

/-- The post-Lie relators with `mid` half the bracket and `left` the product. -/
def postLieHalfRel : Set (FreeBin R ComTriOp (Fin 3)) :=
  {BinRel.jacobi R .mid, BinRel.postLie₁ R .mid .left, BinRel.postLieHalf₂ R .mid .left}

/-- The leading forms of the post-Lie relators with `mid` the bracket and `left` the product. -/
def postLieLeadHalfRel : Set (FreeBin R ComTriOp (Fin 3)) :=
  {BinRel.jacobi R .mid, BinRel.postLie₁ R .mid .left, BinRel.preLie R .left}

end Relators

/-- **Commutative trialgebras** (Vallette's `ComTrias`), as a binary quadratic operad. -/
abbrev BinComTrias (R : Type u) [CommRing R] :=
  BinPres R {BinRel.comm R ComTriOp.mid} (comTriasRel R)

/-- **The leading forms of commutative trialgebras**: `x ⊣ (y ⊥ z) = 0`. -/
abbrev BinComTriasLead (R : Type u) [CommRing R] :=
  BinPres R {BinRel.comm R ComTriOp.mid} (comTriasLeadRel R)

/-- **The post-Lie operad.** -/
abbrev PostLie (R : Type u) [CommRing R] :=
  BinPres R {BinRel.antisymm R PostLieOp.bracket} (postLieRel R)

/-- **The leading forms of the post-Lie operad**: a Lie bracket and a right pre-Lie product acting
on it by derivations. -/
abbrev PostLieLead (R : Type u) [CommRing R] :=
  BinPres R {BinRel.antisymm R PostLieOp.bracket} (postLieLeadRel R)

/-! ## The certificates -/

namespace PostLieData

/-- The generators. -/
def gsT : List ComTriOp := [.mid, .left]

/-- The commutativity of `mid`, as a certificate. -/
noncomputable def commC : Cert2 ComTriOp := [((.mid, 1), 1), ((.mid, Equiv.swap 0 1), -1)]

/-- The antisymmetry of `mid`, as a certificate. -/
noncomputable def antiC : Cert2 ComTriOp := [((.mid, 1), 1), ((.mid, Equiv.swap 0 1), 1)]

/-- The relators of `ComTrias` of arity three, as certificates. -/
noncomputable def ctRelC : List (Cert3 ComTriOp) :=
  [[((false, .mid, .mid, 1), 1), ((true, .mid, .mid, 1), -1)],
   [((false, .left, .left, 1), 1), ((true, .left, .left, 1), -1)],
   [((true, .left, .left, 1), 1), ((true, .left, .left, perm3 0 2 1), -1)],
   [((true, .left, .mid, 1), 1), ((true, .left, .left, 1), -1)],
   [((false, .left, .mid, 1), 1), ((true, .mid, .left, 1), -1)]]

/-- The relators of the leading forms of `ComTrias`, as certificates. -/
noncomputable def ctLeadRelC : List (Cert3 ComTriOp) :=
  [[((false, .mid, .mid, 1), 1), ((true, .mid, .mid, 1), -1)],
   [((false, .left, .left, 1), 1), ((true, .left, .left, 1), -1)],
   [((true, .left, .left, 1), 1), ((true, .left, .left, perm3 0 2 1), -1)],
   [((true, .left, .mid, 1), 1)],
   [((false, .left, .mid, 1), 1), ((true, .mid, .left, 1), -1)]]

/-- The post-Lie relators with the bracket halved, as certificates. -/
noncomputable def plHalfC : List (Cert3 ComTriOp) :=
  [[((false, .mid, .mid, 1), 1), ((false, .mid, .mid, perm3 1 2 0), 1),
    ((false, .mid, .mid, perm3 2 0 1), 1)],
   [((false, .mid, .left, perm3 0 2 1), -1), ((false, .left, .mid, 1), 1),
    ((true, .mid, .left, 1), -1)],
   [((false, .left, .left, 1), 1), ((false, .left, .left, perm3 0 2 1), -1),
    ((true, .left, .mid, 1), -2), ((true, .left, .left, 1), -1),
    ((true, .left, .left, perm3 0 2 1), 1)]]

/-- The leading forms of the post-Lie relators, as certificates. -/
noncomputable def plLeadC : List (Cert3 ComTriOp) :=
  [[((false, .mid, .mid, 1), 1), ((false, .mid, .mid, perm3 1 2 0), 1),
    ((false, .mid, .mid, perm3 2 0 1), 1)],
   [((false, .mid, .left, perm3 0 2 1), -1), ((false, .left, .mid, 1), 1),
    ((true, .mid, .left, 1), -1)],
   [((false, .left, .left, 1), 1), ((false, .left, .left, perm3 0 2 1), -1),
    ((true, .left, .left, 1), -1), ((true, .left, .left, perm3 0 2 1), 1)]]

/-- The dimension certificates: each monomial outside the roots is the root of
its class, or zero, plus a path of relabelled generators. -/
noncomputable def ctDim : List (MemCert × Mono3 ComTriOp) :=
  [([(-1, 1, 0)],
     (true, .mid, .mid, perm3 2 0 1)),
   ([(-1, 1, 2)],
     (false, .mid, .mid, perm3 1 0 2)),
   ([(-1, 1, 16)],
     (true, .mid, .mid, 1)),
   ([(-1, perm3 2 0 1, 3), (-1, 1, 0)],
     (true, .mid, .mid, perm3 2 1 0)),
   ([(1, perm3 2 0 1, 16), (-1, 1, 0)],
     (false, .mid, .mid, perm3 2 0 1)),
   ([(-1, perm3 1 0 2, 16), (-1, 1, 2)],
     (true, .mid, .mid, perm3 1 0 2)),
   ([(1, perm3 1 2 0, 0), (-1, 1, 16)],
     (false, .mid, .mid, perm3 1 2 0)),
   ([(-1, 1, 3), (-1, 1, 16)],
     (true, .mid, .mid, perm3 0 2 1)),
   ([(1, perm3 2 1 0, 16), (-1, perm3 2 0 1, 3), (-1, 1, 0)],
     (false, .mid, .mid, perm3 2 1 0)),
   ([(-1, perm3 2 0 1, 0), (1, perm3 2 0 1, 16), (-1, 1, 0)],
     (true, .mid, .mid, perm3 1 2 0)),
   ([(1, perm3 0 2 1, 2), (1, perm3 2 0 1, 16), (-1, 1, 0)],
     (false, .mid, .mid, perm3 0 2 1)),
   ([(-1, 1, 8)],
     (true, .mid, .left, perm3 2 0 1)),
   ([(1, perm3 2 0 1, 20), (-1, 1, 8)],
     (false, .left, .mid, perm3 2 0 1)),
   ([(1, perm3 0 2 1, 10), (1, perm3 2 0 1, 20), (-1, 1, 8)],
     (false, .left, .mid, perm3 0 2 1)),
   ([(-1, perm3 0 2 1, 20), (1, perm3 0 2 1, 10), (1, perm3 2 0 1, 20), (-1, 1, 8)],
     (true, .mid, .left, perm3 0 2 1)),
   ([(1, perm3 2 1 0, 8), (-1, perm3 0 2 1, 20), (1, perm3 0 2 1, 10), (1, perm3 2 0 1, 20),
     (-1, 1, 8)],
     (false, .mid, .left, perm3 2 1 0)),
   ([(-1, perm3 0 2 1, 8)],
     (true, .mid, .left, perm3 1 0 2)),
   ([(1, perm3 1 0 2, 20), (-1, perm3 0 2 1, 8)],
     (false, .left, .mid, perm3 1 0 2)),
   ([(1, 1, 10), (1, perm3 1 0 2, 20), (-1, perm3 0 2 1, 8)],
     (false, .left, .mid, 1)),
   ([(-1, 1, 20), (1, 1, 10), (1, perm3 1 0 2, 20), (-1, perm3 0 2 1, 8)],
     (true, .mid, .left, 1)),
   ([(1, perm3 1 2 0, 8), (-1, 1, 20), (1, 1, 10), (1, perm3 1 0 2, 20), (-1, perm3 0 2 1, 8)],
     (false, .mid, .left, perm3 1 2 0)),
   ([(-1, perm3 1 0 2, 8)],
     (true, .mid, .left, perm3 2 1 0)),
   ([(1, perm3 2 1 0, 20), (-1, perm3 1 0 2, 8)],
     (false, .left, .mid, perm3 2 1 0)),
   ([(1, perm3 1 2 0, 10), (1, perm3 2 1 0, 20), (-1, perm3 1 0 2, 8)],
     (false, .left, .mid, perm3 1 2 0)),
   ([(-1, perm3 1 2 0, 20), (1, perm3 1 2 0, 10), (1, perm3 2 1 0, 20), (-1, perm3 1 0 2, 8)],
     (true, .mid, .left, perm3 1 2 0)),
   ([(1, perm3 2 0 1, 8), (-1, perm3 1 2 0, 20), (1, perm3 1 2 0, 10), (1, perm3 2 1 0, 20),
     (-1, perm3 1 0 2, 8)],
     (false, .mid, .left, perm3 2 0 1)),
   ([(-1, 1, 17)],
     (true, .left, .left, 1)),
   ([(-1, 1, 18), (-1, 1, 17)],
     (true, .left, .left, perm3 0 2 1)),
   ([(1, 1, 19), (-1, 1, 17)],
     (true, .left, .mid, 1)),
   ([(1, perm3 0 2 1, 17), (-1, 1, 18), (-1, 1, 17)],
     (false, .left, .left, perm3 0 2 1)),
   ([(1, perm3 0 2 1, 19), (-1, 1, 18), (-1, 1, 17)],
     (true, .left, .mid, perm3 0 2 1)),
   ([(-1, perm3 1 0 2, 17)],
     (true, .left, .left, perm3 1 0 2)),
   ([(-1, perm3 1 0 2, 18), (-1, perm3 1 0 2, 17)],
     (true, .left, .left, perm3 1 2 0)),
   ([(1, perm3 1 0 2, 19), (-1, perm3 1 0 2, 17)],
     (true, .left, .mid, perm3 1 0 2)),
   ([(1, perm3 1 2 0, 17), (-1, perm3 1 0 2, 18), (-1, perm3 1 0 2, 17)],
     (false, .left, .left, perm3 1 2 0)),
   ([(1, perm3 1 2 0, 19), (-1, perm3 1 0 2, 18), (-1, perm3 1 0 2, 17)],
     (true, .left, .mid, perm3 1 2 0)),
   ([(-1, perm3 2 0 1, 17)],
     (true, .left, .left, perm3 2 0 1)),
   ([(-1, perm3 2 0 1, 18), (-1, perm3 2 0 1, 17)],
     (true, .left, .left, perm3 2 1 0)),
   ([(1, perm3 2 0 1, 19), (-1, perm3 2 0 1, 17)],
     (true, .left, .mid, perm3 2 0 1)),
   ([(1, perm3 2 1 0, 17), (-1, perm3 2 0 1, 18), (-1, perm3 2 0 1, 17)],
     (false, .left, .left, perm3 2 1 0)),
   ([(1, perm3 2 1 0, 19), (-1, perm3 2 0 1, 18), (-1, perm3 2 0 1, 17)],
     (true, .left, .mid, perm3 2 1 0))]

/-- The signed sums of the classes of monomials, with a root of each. -/
noncomputable def ctU : List (Cert3 ComTriOp × Mono3 ComTriOp) :=
  [([((false, .mid, .mid, 1), 1), ((false, .mid, .mid, perm3 0 2 1), -1),
     ((false, .mid, .mid, perm3 1 0 2), -1), ((false, .mid, .mid, perm3 1 2 0), 1),
     ((false, .mid, .mid, perm3 2 0 1), 1), ((false, .mid, .mid, perm3 2 1 0), -1),
     ((true, .mid, .mid, 1), -1), ((true, .mid, .mid, perm3 0 2 1), 1),
     ((true, .mid, .mid, perm3 1 0 2), 1), ((true, .mid, .mid, perm3 1 2 0), -1),
     ((true, .mid, .mid, perm3 2 0 1), -1), ((true, .mid, .mid, perm3 2 1 0), 1)],
     (false, .mid, .mid, 1)),
   ([((false, .mid, .left, 1), 1), ((false, .mid, .left, perm3 2 1 0), -1),
     ((false, .left, .mid, perm3 0 2 1), -1), ((false, .left, .mid, perm3 2 0 1), 1),
     ((true, .mid, .left, perm3 0 2 1), 1), ((true, .mid, .left, perm3 2 0 1), -1)],
     (false, .mid, .left, 1)),
   ([((false, .mid, .left, perm3 0 2 1), -1), ((false, .mid, .left, perm3 1 2 0), 1),
     ((false, .left, .mid, 1), 1), ((false, .left, .mid, perm3 1 0 2), -1),
     ((true, .mid, .left, 1), -1), ((true, .mid, .left, perm3 1 0 2), 1)],
     (false, .mid, .left, perm3 0 2 1)),
   ([((false, .mid, .left, perm3 1 0 2), -1), ((false, .mid, .left, perm3 2 0 1), 1),
     ((false, .left, .mid, perm3 1 2 0), 1), ((false, .left, .mid, perm3 2 1 0), -1),
     ((true, .mid, .left, perm3 1 2 0), -1), ((true, .mid, .left, perm3 2 1 0), 1)],
     (false, .mid, .left, perm3 1 0 2)),
   ([((false, .left, .left, 1), 1), ((false, .left, .left, perm3 0 2 1), -1),
     ((true, .left, .mid, 1), -1), ((true, .left, .mid, perm3 0 2 1), 1),
     ((true, .left, .left, 1), -1), ((true, .left, .left, perm3 0 2 1), 1)],
     (false, .left, .left, 1)),
   ([((false, .left, .left, perm3 1 0 2), -1), ((false, .left, .left, perm3 1 2 0), 1),
     ((true, .left, .mid, perm3 1 0 2), 1), ((true, .left, .mid, perm3 1 2 0), -1),
     ((true, .left, .left, perm3 1 0 2), 1), ((true, .left, .left, perm3 1 2 0), -1)],
     (false, .left, .left, perm3 1 0 2)),
   ([((false, .left, .left, perm3 2 0 1), 1), ((false, .left, .left, perm3 2 1 0), -1),
     ((true, .left, .mid, perm3 2 0 1), -1), ((true, .left, .mid, perm3 2 1 0), 1),
     ((true, .left, .left, perm3 2 0 1), -1), ((true, .left, .left, perm3 2 1 0), 1)],
     (false, .left, .left, perm3 2 0 1))]

/-- The membership certificates of the signed sums of the classes. -/
noncomputable def ctMemU : List MemCert :=
  [[(-1, 1, 0), (1, perm3 0 2 1, 0), (1, perm3 1 0 2, 0), (-1, perm3 1 2 0, 0),
    (-1, perm3 2 0 1, 0), (1, perm3 2 1 0, 0), (-2, 1, 2), (-2, perm3 0 2 1, 2),
    (-2, perm3 1 2 0, 2), (4, 1, 16)],
   [(-1, 1, 8), (-1, perm3 2 1 0, 8), (1, perm3 0 2 1, 10), (-2, perm3 0 2 1, 17)],
   [(1, perm3 0 2 1, 8), (1, perm3 1 2 0, 8), (-1, 1, 10), (2, 1, 17)],
   [(1, perm3 1 0 2, 8), (1, perm3 2 0 1, 8), (-1, perm3 1 2 0, 10), (2, perm3 1 2 0, 17)],
   [(1, 1, 11), (1, 1, 18)],
   [(-1, perm3 1 0 2, 11), (-1, perm3 1 0 2, 18)],
   [(1, perm3 2 0 1, 11), (1, perm3 2 0 1, 18)]]

/-- The membership certificates of the dual relators, with their multipliers. -/
noncomputable def ctMemS : List (ℤ × MemCert) :=
  [(4, [(1, 1, 0), (-1, perm3 0 2 1, 0), (-1, perm3 1 0 2, 0), (1, perm3 1 2 0, 0),
     (1, perm3 2 0 1, 0), (-1, perm3 2 1 0, 0), (2, 1, 2), (2, perm3 0 2 1, 2),
     (2, perm3 1 2 0, 2), (1, 1, 16)]),
   (2, [(-1, perm3 0 2 1, 8), (-1, perm3 1 2 0, 8), (1, 1, 10), (-1, perm3 0 2 1, 17)]),
   (1, [(-1, 1, 11), (1, 1, 20)])]

/-- The dimension certificates: each monomial outside the roots is the root of
its class, or zero, plus a path of relabelled generators. -/
noncomputable def ctLeadDim : List (MemCert × Mono3 ComTriOp) :=
  [([(-1, 1, 0)],
     (true, .mid, .mid, perm3 2 0 1)),
   ([(-1, 1, 2)],
     (false, .mid, .mid, perm3 1 0 2)),
   ([(-1, 1, 16)],
     (true, .mid, .mid, 1)),
   ([(-1, perm3 2 0 1, 3), (-1, 1, 0)],
     (true, .mid, .mid, perm3 2 1 0)),
   ([(1, perm3 2 0 1, 16), (-1, 1, 0)],
     (false, .mid, .mid, perm3 2 0 1)),
   ([(-1, perm3 1 0 2, 16), (-1, 1, 2)],
     (true, .mid, .mid, perm3 1 0 2)),
   ([(1, perm3 1 2 0, 0), (-1, 1, 16)],
     (false, .mid, .mid, perm3 1 2 0)),
   ([(-1, 1, 3), (-1, 1, 16)],
     (true, .mid, .mid, perm3 0 2 1)),
   ([(1, perm3 2 1 0, 16), (-1, perm3 2 0 1, 3), (-1, 1, 0)],
     (false, .mid, .mid, perm3 2 1 0)),
   ([(-1, perm3 2 0 1, 0), (1, perm3 2 0 1, 16), (-1, 1, 0)],
     (true, .mid, .mid, perm3 1 2 0)),
   ([(1, perm3 0 2 1, 2), (1, perm3 2 0 1, 16), (-1, 1, 0)],
     (false, .mid, .mid, perm3 0 2 1)),
   ([(-1, 1, 8)],
     (true, .mid, .left, perm3 2 0 1)),
   ([(1, perm3 2 0 1, 20), (-1, 1, 8)],
     (false, .left, .mid, perm3 2 0 1)),
   ([(1, perm3 0 2 1, 10), (1, perm3 2 0 1, 20), (-1, 1, 8)],
     (false, .left, .mid, perm3 0 2 1)),
   ([(-1, perm3 0 2 1, 20), (1, perm3 0 2 1, 10), (1, perm3 2 0 1, 20), (-1, 1, 8)],
     (true, .mid, .left, perm3 0 2 1)),
   ([(1, perm3 2 1 0, 8), (-1, perm3 0 2 1, 20), (1, perm3 0 2 1, 10), (1, perm3 2 0 1, 20),
     (-1, 1, 8)],
     (false, .mid, .left, perm3 2 1 0)),
   ([(-1, perm3 0 2 1, 8)],
     (true, .mid, .left, perm3 1 0 2)),
   ([(1, perm3 1 0 2, 20), (-1, perm3 0 2 1, 8)],
     (false, .left, .mid, perm3 1 0 2)),
   ([(1, 1, 10), (1, perm3 1 0 2, 20), (-1, perm3 0 2 1, 8)],
     (false, .left, .mid, 1)),
   ([(-1, 1, 20), (1, 1, 10), (1, perm3 1 0 2, 20), (-1, perm3 0 2 1, 8)],
     (true, .mid, .left, 1)),
   ([(1, perm3 1 2 0, 8), (-1, 1, 20), (1, 1, 10), (1, perm3 1 0 2, 20), (-1, perm3 0 2 1, 8)],
     (false, .mid, .left, perm3 1 2 0)),
   ([(-1, perm3 1 0 2, 8)],
     (true, .mid, .left, perm3 2 1 0)),
   ([(1, perm3 2 1 0, 20), (-1, perm3 1 0 2, 8)],
     (false, .left, .mid, perm3 2 1 0)),
   ([(1, perm3 1 2 0, 10), (1, perm3 2 1 0, 20), (-1, perm3 1 0 2, 8)],
     (false, .left, .mid, perm3 1 2 0)),
   ([(-1, perm3 1 2 0, 20), (1, perm3 1 2 0, 10), (1, perm3 2 1 0, 20), (-1, perm3 1 0 2, 8)],
     (true, .mid, .left, perm3 1 2 0)),
   ([(1, perm3 2 0 1, 8), (-1, perm3 1 2 0, 20), (1, perm3 1 2 0, 10), (1, perm3 2 1 0, 20),
     (-1, perm3 1 0 2, 8)],
     (false, .mid, .left, perm3 2 0 1)),
   ([(-1, 1, 17)],
     (true, .left, .left, 1)),
   ([(-1, 1, 18), (-1, 1, 17)],
     (true, .left, .left, perm3 0 2 1)),
   ([(1, perm3 0 2 1, 17), (-1, 1, 18), (-1, 1, 17)],
     (false, .left, .left, perm3 0 2 1)),
   ([(-1, perm3 1 0 2, 17)],
     (true, .left, .left, perm3 1 0 2)),
   ([(-1, perm3 1 0 2, 18), (-1, perm3 1 0 2, 17)],
     (true, .left, .left, perm3 1 2 0)),
   ([(1, perm3 1 2 0, 17), (-1, perm3 1 0 2, 18), (-1, perm3 1 0 2, 17)],
     (false, .left, .left, perm3 1 2 0)),
   ([(-1, perm3 2 0 1, 17)],
     (true, .left, .left, perm3 2 0 1)),
   ([(-1, perm3 2 0 1, 18), (-1, perm3 2 0 1, 17)],
     (true, .left, .left, perm3 2 1 0)),
   ([(1, perm3 2 1 0, 17), (-1, perm3 2 0 1, 18), (-1, perm3 2 0 1, 17)],
     (false, .left, .left, perm3 2 1 0)),
   ([(1, 1, 11), (1, perm3 0 2 1, 19)],
     (true, .left, .mid, 1)),
   ([(-1, 1, 11), (1, 1, 11), (1, perm3 0 2 1, 19)],
     (true, .left, .mid, perm3 0 2 1)),
   ([(1, perm3 1 0 2, 11), (1, perm3 1 2 0, 19)],
     (true, .left, .mid, perm3 1 0 2)),
   ([(-1, perm3 1 0 2, 11), (1, perm3 1 0 2, 11), (1, perm3 1 2 0, 19)],
     (true, .left, .mid, perm3 1 2 0)),
   ([(1, perm3 2 0 1, 11), (1, perm3 2 1 0, 19)],
     (true, .left, .mid, perm3 2 0 1)),
   ([(-1, perm3 2 0 1, 11), (1, perm3 2 0 1, 11), (1, perm3 2 1 0, 19)],
     (true, .left, .mid, perm3 2 1 0))]

/-- The signed sums of the classes of monomials, with a root of each. -/
noncomputable def ctLeadU : List (Cert3 ComTriOp × Mono3 ComTriOp) :=
  [([((false, .mid, .mid, 1), 1), ((false, .mid, .mid, perm3 0 2 1), -1),
     ((false, .mid, .mid, perm3 1 0 2), -1), ((false, .mid, .mid, perm3 1 2 0), 1),
     ((false, .mid, .mid, perm3 2 0 1), 1), ((false, .mid, .mid, perm3 2 1 0), -1),
     ((true, .mid, .mid, 1), -1), ((true, .mid, .mid, perm3 0 2 1), 1),
     ((true, .mid, .mid, perm3 1 0 2), 1), ((true, .mid, .mid, perm3 1 2 0), -1),
     ((true, .mid, .mid, perm3 2 0 1), -1), ((true, .mid, .mid, perm3 2 1 0), 1)],
     (false, .mid, .mid, 1)),
   ([((false, .mid, .left, 1), 1), ((false, .mid, .left, perm3 2 1 0), -1),
     ((false, .left, .mid, perm3 0 2 1), -1), ((false, .left, .mid, perm3 2 0 1), 1),
     ((true, .mid, .left, perm3 0 2 1), 1), ((true, .mid, .left, perm3 2 0 1), -1)],
     (false, .mid, .left, 1)),
   ([((false, .mid, .left, perm3 0 2 1), -1), ((false, .mid, .left, perm3 1 2 0), 1),
     ((false, .left, .mid, 1), 1), ((false, .left, .mid, perm3 1 0 2), -1),
     ((true, .mid, .left, 1), -1), ((true, .mid, .left, perm3 1 0 2), 1)],
     (false, .mid, .left, perm3 0 2 1)),
   ([((false, .mid, .left, perm3 1 0 2), -1), ((false, .mid, .left, perm3 2 0 1), 1),
     ((false, .left, .mid, perm3 1 2 0), 1), ((false, .left, .mid, perm3 2 1 0), -1),
     ((true, .mid, .left, perm3 1 2 0), -1), ((true, .mid, .left, perm3 2 1 0), 1)],
     (false, .mid, .left, perm3 1 0 2)),
   ([((false, .left, .left, 1), 1), ((false, .left, .left, perm3 0 2 1), -1),
     ((true, .left, .left, 1), -1), ((true, .left, .left, perm3 0 2 1), 1)],
     (false, .left, .left, 1)),
   ([((false, .left, .left, perm3 1 0 2), -1), ((false, .left, .left, perm3 1 2 0), 1),
     ((true, .left, .left, perm3 1 0 2), 1), ((true, .left, .left, perm3 1 2 0), -1)],
     (false, .left, .left, perm3 1 0 2)),
   ([((false, .left, .left, perm3 2 0 1), 1), ((false, .left, .left, perm3 2 1 0), -1),
     ((true, .left, .left, perm3 2 0 1), -1), ((true, .left, .left, perm3 2 1 0), 1)],
     (false, .left, .left, perm3 2 0 1))]

/-- The membership certificates of the signed sums of the classes. -/
noncomputable def ctLeadMemU : List MemCert :=
  [[(-1, 1, 0), (1, perm3 0 2 1, 0), (1, perm3 1 0 2, 0), (-1, perm3 1 2 0, 0),
    (-1, perm3 2 0 1, 0), (1, perm3 2 1 0, 0), (-2, 1, 2), (-2, perm3 0 2 1, 2),
    (-2, perm3 1 2 0, 2), (4, 1, 16)],
   [(-1, 1, 8), (-1, perm3 2 1 0, 8), (1, perm3 0 2 1, 10), (-2, perm3 0 2 1, 17)],
   [(1, perm3 0 2 1, 8), (1, perm3 1 2 0, 8), (-1, 1, 10), (2, 1, 17)],
   [(1, perm3 1 0 2, 8), (1, perm3 2 0 1, 8), (-1, perm3 1 2 0, 10), (2, perm3 1 2 0, 17)],
   [(1, 1, 18)],
   [(-1, perm3 1 0 2, 18)],
   [(1, perm3 2 0 1, 18)]]

/-- The membership certificates of the dual relators, with their multipliers. -/
noncomputable def ctLeadMemS : List (ℤ × MemCert) :=
  [(4, [(1, 1, 0), (-1, perm3 0 2 1, 0), (-1, perm3 1 0 2, 0), (1, perm3 1 2 0, 0),
     (1, perm3 2 0 1, 0), (-1, perm3 2 1 0, 0), (2, 1, 2), (2, perm3 0 2 1, 2),
     (2, perm3 1 2 0, 2), (1, 1, 16)]),
   (2, [(-1, perm3 0 2 1, 8), (-1, perm3 1 2 0, 8), (1, 1, 10), (-1, perm3 0 2 1, 17)]),
   (1, [(1, 1, 20)])]

end PostLieData

/-! ## `ComTrias^! = PostLie` -/

section Dual

open PostLieData Cert3 Cert2

variable (K : Type u) [Field K]

lemma commC_val : Cert2.val K commC = BinRel.comm K ComTriOp.mid := by
  simp [commC, BinRel.comm, sub_eq_add_neg]

lemma antiC_val : Cert2.val K antiC = BinRel.antisymm K ComTriOp.mid := by
  simp [antiC, BinRel.antisymm]

lemma comm_set_eq : ({BinRel.comm K ComTriOp.mid} : Set (FreeBin K ComTriOp (Fin 2)))
    = Cert2.val K '' {a | a ∈ [commC]} := by
  rw [Cert2.image_val_singleton, commC_val]

lemma antisymm_set_eq : ({BinRel.antisymm K ComTriOp.mid} : Set (FreeBin K ComTriOp (Fin 2)))
    = Cert2.val K '' {a | a ∈ [antiC]} := by
  rw [Cert2.image_val_singleton, antiC_val]

lemma twist2_commC : twist2 K '' (Cert2.val K '' {a | a ∈ [commC]})
    = Cert2.val K '' {a | a ∈ [antiC]} := by
  rw [Cert2.image_val_singleton, Cert2.image_val_singleton, Set.image_singleton, commC_val,
    antiC_val, BinRel.comm, BinRel.antisymm, map_sub, twist2_bin2, twist2_bin2,
    Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1)]
  simp

lemma comTriasRel_eq : comTriasRel K = Cert3.val K '' {r | r ∈ ctRelC} := by
  simp only [ctRelC, image_val_cons, image_val_nil, insert_empty_eq, comTriasRel]
  congr 1
  · simp [BinRel.assoc, sub_eq_add_neg, mono3_false, mono3_true]
  congr 1
  · simp [BinRel.assoc, sub_eq_add_neg, mono3_false, mono3_true]
  congr 1
  · simp [BinRel.perm, sub_eq_add_neg, mono3_true]
  congr 1
  · simp [BinRel.leftMid, sub_eq_add_neg, mono3_true]
  · simp [BinRel.midLeft, sub_eq_add_neg, mono3_false, mono3_true]

lemma comTriasLeadRel_eq : comTriasLeadRel K = Cert3.val K '' {r | r ∈ ctLeadRelC} := by
  simp only [ctLeadRelC, image_val_cons, image_val_nil, insert_empty_eq, comTriasLeadRel]
  congr 1
  · simp [BinRel.assoc, sub_eq_add_neg, mono3_false, mono3_true]
  congr 1
  · simp [BinRel.assoc, sub_eq_add_neg, mono3_false, mono3_true]
  congr 1
  · simp [BinRel.perm, sub_eq_add_neg, mono3_true]
  congr 1
  · simp [mono3_true]
  · simp [BinRel.midLeft, sub_eq_add_neg, mono3_false, mono3_true]

lemma postLieHalfRel_eq : postLieHalfRel K = Cert3.val K '' {r | r ∈ plHalfC} := by
  simp only [plHalfC, image_val_cons, image_val_nil, insert_empty_eq, postLieHalfRel]
  congr 1
  · simp [BinRel.jacobi, mono3_false]
    abel
  congr 1
  · simp [BinRel.postLie₁, sub_eq_add_neg, mono3_false, mono3_true]
    abel
  · simp [BinRel.postLieHalf₂, sub_eq_add_neg, mono3_false, mono3_true]
    module

lemma postLieLeadHalfRel_eq : postLieLeadHalfRel K = Cert3.val K '' {r | r ∈ plLeadC} := by
  simp only [plLeadC, image_val_cons, image_val_nil, insert_empty_eq, postLieLeadHalfRel]
  congr 1
  · simp [BinRel.jacobi, mono3_false]
    abel
  congr 1
  · simp [BinRel.postLie₁, sub_eq_add_neg, mono3_false, mono3_true]
    abel
  · simp [BinRel.preLie, sub_eq_add_neg, mono3_false, mono3_true]
    abel

variable [CharZero K]

set_option maxRecDepth 100000 in
/-- **The Koszul dual relations of commutative trialgebras** are spanned by the signed sums of the
seven classes of monomials. -/
theorem dualRel23_comTrias :
    dualRel23 K {BinRel.comm K ComTriOp.mid} (comTriasRel K)
      = Submodule.span K (Cert3.val K '' {u | u ∈ ctU.map Prod.fst}) := by
  rw [comm_set_eq, comTriasRel_eq]
  exact dualRel23_eq_span_of_cert K gsT [commC] ctRelC ctDim ctU (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- **The Koszul dual relations of the leading forms of commutative trialgebras** are spanned by
the signed sums of the seven surviving classes of monomials. -/
theorem dualRel23_comTriasLead :
    dualRel23 K {BinRel.comm K ComTriOp.mid} (comTriasLeadRel K)
      = Submodule.span K (Cert3.val K '' {u | u ∈ ctLeadU.map Prod.fst}) := by
  rw [comm_set_eq, comTriasLeadRel_eq]
  exact dualRel23_eq_span_of_cert K gsT [commC] ctLeadRelC ctLeadDim ctLeadU (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- **`ComTrias^!`, presented**: the Koszul dual of commutative trialgebras is presented by the
antisymmetry of `mid`, the Jacobi identity and the post-Lie relations with `mid` half the
bracket and `left` the product. -/
theorem dual23_comTrias :
    SymOperadIdeal.span K (rel23 (twist2 K '' {BinRel.comm K ComTriOp.mid})
        (dualRel23 K {BinRel.comm K ComTriOp.mid} (comTriasRel K) :
          Set (FreeBin K ComTriOp (Fin 3))))
      = SymOperadIdeal.span K (rel23 {BinRel.antisymm K ComTriOp.mid} (postLieHalfRel K)) := by
  have hU := dualRel23_comTrias K
  rw [comm_set_eq, comTriasRel_eq] at hU ⊢
  rw [antisymm_set_eq, postLieHalfRel_eq]
  exact dual23_span_eq_of_cert K gsT [commC] ctRelC [antiC] plHalfC ctU hU (twist2_commC K)
    ctMemU (by decide +kernel) (by decide) ctMemS (by decide +kernel) (by decide)

set_option maxRecDepth 100000 in
/-- **The Koszul dual of the leading forms of commutative trialgebras** is presented by the
antisymmetry of `mid`, the Jacobi identity, the derivation relation and the right pre-Lie relation
of `left`. -/
theorem dual23_comTriasLead :
    SymOperadIdeal.span K (rel23 (twist2 K '' {BinRel.comm K ComTriOp.mid})
        (dualRel23 K {BinRel.comm K ComTriOp.mid} (comTriasLeadRel K) :
          Set (FreeBin K ComTriOp (Fin 3))))
      = SymOperadIdeal.span K (rel23 {BinRel.antisymm K ComTriOp.mid}
          (postLieLeadHalfRel K)) := by
  have hU := dualRel23_comTriasLead K
  rw [comm_set_eq, comTriasLeadRel_eq] at hU ⊢
  rw [antisymm_set_eq, postLieLeadHalfRel_eq]
  exact dual23_span_eq_of_cert K gsT [commC] ctLeadRelC [antiC] plLeadC ctLeadU hU (twist2_commC K)
    ctLeadMemU (by decide +kernel) (by decide) ctLeadMemS (by decide +kernel) (by decide)

/-- **`ComTrias^!` is presented by the post-Lie relations with the bracket halved.** -/
theorem BinComTrias.dual23_eq :
    BinPres.dual23 K {BinRel.comm K ComTriOp.mid} (comTriasRel K)
      = BinPres K {BinRel.antisymm K ComTriOp.mid} (postLieHalfRel K) :=
  congrArg SymOperadIdeal.Quot (dual23_comTrias K)

/-- **The Koszul dual of the leading forms of `ComTrias`** is presented by the leading forms of
the post-Lie relations. -/
theorem BinComTriasLead.dual23_eq :
    BinPres.dual23 K {BinRel.comm K ComTriOp.mid} (comTriasLeadRel K)
      = BinPres K {BinRel.antisymm K ComTriOp.mid} (postLieLeadHalfRel K) :=
  congrArg SymOperadIdeal.Quot (dual23_comTriasLead K)

end Dual

/-! ## Renaming and rescaling generators -/

namespace FreeBin

section Rename

variable (R : Type u) [CommRing R] {G G' : Type v}

lemma bin2_eq_map_single (g : G) (σ : Equiv.Perm (Fin 2)) :
    bin2 (R := R) g σ = SymOperad.map (R := R) σ
      (Finsupp.single (Pres.gen (BinGen.op g) : FreeSet (BinGen G) (Fin 2)) (1 : R)) := by
  rw [bin2]
  exact (Lin.mapL_single (R := R) σ (Pres.gen (BinGen.op g) : FreeSet (BinGen G) (Fin 2)) 1).symm

lemma bin2_one_eq_single (g : G) :
    bin2 (R := R) g 1
      = Finsupp.single (Pres.gen (BinGen.op g) : FreeSet (BinGen G) (Fin 2)) (1 : R) := by
  rw [bin2_eq_map_single, show (1 : Equiv.Perm (Fin 2)) = Equiv.refl _ from rfl,
    SymOperad.map_refl]

lemma map_bin2_one (g : G) (σ : Equiv.Perm (Fin 2)) :
    SymOperad.map (R := R) σ (bin2 (R := R) g 1) = bin2 g σ := by
  rw [bin2_one_eq_single, bin2_eq_map_single]

/-- **Renaming and rescaling the generators**: the morphism of free operads sending the generator
`g` to `c g • θ g`. -/
noncomputable def rename (θ : G → G') (c : G → R) : SymOperadHom R (FreeBin R G) (FreeBin R G') :=
  FreeSet.linHom R fun _ x => match x with
    | .op g => c g • bin2 (θ g) 1

variable {R}

lemma rename_bin2 (θ : G → G') (c : G → R) (g : G) (σ : Equiv.Perm (Fin 2)) :
    (rename R θ c).app _ (bin2 g σ) = c g • bin2 (θ g) σ := by
  rw [bin2_eq_map_single, (rename R θ c).app_map, rename, FreeSet.linHom_gen, map_smul,
    map_bin2_one]

variable [Fintype G] [DecidableEq G] [Fintype G'] [DecidableEq G']

lemma binL_eq_comp (g h : G) (σ : Equiv.Perm (Fin 3)) :
    binL (R := R) g h σ = SymOperad.map (R := R) σ (SymOperad.map (R := R) e0
      (SymOperad.comp (R := R) 0 (bin2 g 1) (bin2 h 1))) := by
  rw [comp_e0_bin2, if_pos rfl, if_pos rfl, ← mono3_false (R := R) g h 1, map_mono3]
  simp only [act3, mul_one]
  rfl

lemma binR_eq_comp (g h : G) (σ : Equiv.Perm (Fin 3)) :
    binR (R := R) g h σ = SymOperad.map (R := R) σ (SymOperad.map (R := R) e1
      (SymOperad.comp (R := R) 1 (bin2 g 1) (bin2 h 1))) := by
  rw [comp_e1_bin2, if_pos rfl, if_pos rfl, ← mono3_true (R := R) g h 1, map_mono3]
  simp only [act3, mul_one]
  rfl

lemma rename_binL (θ : G → G') (c : G → R) (g h : G) (σ : Equiv.Perm (Fin 3)) :
    (rename R θ c).app _ (binL g h σ) = (c g * c h) • binL (θ g) (θ h) σ := by
  rw [binL_eq_comp, (rename R θ c).app_map, (rename R θ c).app_map, (rename R θ c).app_comp,
    rename_bin2, rename_bin2, binL_eq_comp]
  simp only [map_smul, LinearMap.smul_apply, smul_smul, mul_comm]

lemma rename_binR (θ : G → G') (c : G → R) (g h : G) (σ : Equiv.Perm (Fin 3)) :
    (rename R θ c).app _ (binR g h σ) = (c g * c h) • binR (θ g) (θ h) σ := by
  rw [binR_eq_comp, (rename R θ c).app_map, (rename R θ c).app_map, (rename R θ c).app_comp,
    rename_bin2, rename_bin2, binR_eq_comp]
  simp only [map_smul, LinearMap.smul_apply, smul_smul, mul_comm]

end Rename

section RenamePres

variable {K : Type u} [Field K] {G G' : Type v} {r₂ : Set (FreeBin K G (Fin 2))}
  {r₃ : Set (FreeBin K G (Fin 3))}
  {s₂ : Set (FreeBin K G' (Fin 2))} {s₃ : Set (FreeBin K G' (Fin 3))}

/-- **A renaming carrying the relators into an ideal carries their ideal into it.** -/
lemma rename_mem_span (θ : G → G') (c : G → K)
    (h₂ : ∀ x ∈ r₂, (rename K θ c).app _ x ∈ (SymOperadIdeal.span K (rel23 s₂ s₃)).sub (Fin 2))
    (h₃ : ∀ x ∈ r₃, (rename K θ c).app _ x ∈ (SymOperadIdeal.span K (rel23 s₂ s₃)).sub (Fin 3))
    {A : Type} [Fintype A] [DecidableEq A] {x : FreeBin K G A}
    (hx : x ∈ (SymOperadIdeal.span K (rel23 r₂ r₃)).sub A) :
    (rename K θ c).app A x ∈ (SymOperadIdeal.span K (rel23 s₂ s₃)).sub A := by
  have := SymOperadIdeal.app_eq_zero_of_mem_span
    ((SymOperadIdeal.span K (rel23 s₂ s₃)).projHom.comp (rename K θ c))
    (forall_rel23.2 ⟨fun x hx => ((SymOperadIdeal.span K _).proj_eq_zero_iff _).2 (h₂ x hx),
      fun x hx => ((SymOperadIdeal.span K _).proj_eq_zero_iff _).2 (h₃ x hx)⟩) hx
  exact ((SymOperadIdeal.span K _).proj_eq_zero_iff _).1 this

/-- **The morphism of presented operads given by renaming and rescaling the generators**, when
it carries the relators into the ideal of the target. -/
noncomputable def BinPres.renameHom (θ : G → G') (c : G → K)
    (h₂ : ∀ x ∈ r₂, (rename K θ c).app _ x ∈ (SymOperadIdeal.span K (rel23 s₂ s₃)).sub (Fin 2))
    (h₃ : ∀ x ∈ r₃, (rename K θ c).app _ x ∈ (SymOperadIdeal.span K (rel23 s₂ s₃)).sub (Fin 3)) :
    SymOperadHom K (BinPres K r₂ r₃) (BinPres K s₂ s₃) :=
  SymOperadIdeal.presHomEquiv.symm
    ⟨(SymOperadIdeal.span K (rel23 s₂ s₃)).projHom.comp (rename K θ c), fun _ _ hx =>
      ((SymOperadIdeal.span K _).proj_eq_zero_iff _).2
        (rename_mem_span θ c h₂ h₃ (SymOperadIdeal.subset_span _ hx))⟩

lemma BinPres.renameHom_proj (θ : G → G') (c : G → K)
    (h₂ : ∀ x ∈ r₂, (rename K θ c).app _ x ∈ (SymOperadIdeal.span K (rel23 s₂ s₃)).sub (Fin 2))
    (h₃ : ∀ x ∈ r₃, (rename K θ c).app _ x ∈ (SymOperadIdeal.span K (rel23 s₂ s₃)).sub (Fin 3))
    {A : Type} [Fintype A] [DecidableEq A] (x : FreeBin K G A) :
    (BinPres.renameHom (r₂ := r₂) (r₃ := r₃) (s₂ := s₂) (s₃ := s₃) θ c h₂ h₃).app A
        ((SymOperadIdeal.span K (rel23 r₂ r₃)).proj A x)
      = (SymOperadIdeal.span K (rel23 s₂ s₃)).proj A ((rename K θ c).app A x) := rfl

/-- **Renamings inverse to each other on the generators give inverse morphisms.** -/
theorem BinPres.renameHom_comp (θ : G → G') (c : G → K) (θ' : G' → G) (c' : G' → K)
    (h₂ : ∀ x ∈ r₂, (rename K θ c).app _ x ∈ (SymOperadIdeal.span K (rel23 s₂ s₃)).sub (Fin 2))
    (h₃ : ∀ x ∈ r₃, (rename K θ c).app _ x ∈ (SymOperadIdeal.span K (rel23 s₂ s₃)).sub (Fin 3))
    (h₂' : ∀ x ∈ s₂, (rename K θ' c').app _ x ∈ (SymOperadIdeal.span K (rel23 r₂ r₃)).sub (Fin 2))
    (h₃' : ∀ x ∈ s₃, (rename K θ' c').app _ x ∈ (SymOperadIdeal.span K (rel23 r₂ r₃)).sub (Fin 3))
    (hθ : ∀ g, θ' (θ g) = g) (hc : ∀ g, c' (θ g) * c g = 1) :
    (BinPres.renameHom (r₂ := s₂) (r₃ := s₃) (s₂ := r₂) (s₃ := r₃) θ' c' h₂' h₃').comp
      (BinPres.renameHom (r₂ := r₂) (r₃ := r₃) (s₂ := s₂) (s₃ := s₃) θ c h₂ h₃)
        = SymOperadHom.id := by
  apply presLin_hom_ext
  intro n x
  cases x with
  | op g =>
    rw [SymOperadHom.comp_app, SymOperadHom.id_app, BinPres.renameHom_proj,
      ← bin2_one_eq_single, rename_bin2, map_smul, map_smul, BinPres.renameHom_proj, rename_bin2,
      hθ, map_smul, smul_smul, mul_comm, hc, one_smul]

/-- **The isomorphism of presented operads given by renamings inverse to each other.** -/
noncomputable def BinPres.renameIso (θ : G → G') (c : G → K) (θ' : G' → G) (c' : G' → K)
    (h₂ : ∀ x ∈ r₂, (rename K θ c).app _ x ∈ (SymOperadIdeal.span K (rel23 s₂ s₃)).sub (Fin 2))
    (h₃ : ∀ x ∈ r₃, (rename K θ c).app _ x ∈ (SymOperadIdeal.span K (rel23 s₂ s₃)).sub (Fin 3))
    (h₂' : ∀ x ∈ s₂, (rename K θ' c').app _ x ∈ (SymOperadIdeal.span K (rel23 r₂ r₃)).sub (Fin 2))
    (h₃' : ∀ x ∈ s₃, (rename K θ' c').app _ x ∈ (SymOperadIdeal.span K (rel23 r₂ r₃)).sub (Fin 3))
    (hθ : ∀ g, θ' (θ g) = g) (hc : ∀ g, c' (θ g) * c g = 1)
    (hθ' : ∀ g, θ (θ' g) = g) (hc' : ∀ g, c (θ' g) * c' g = 1) :
    SymOperadIso K (BinPres K r₂ r₃) (BinPres K s₂ s₃) where
  hom := BinPres.renameHom θ c h₂ h₃
  inv := BinPres.renameHom θ' c' h₂' h₃'
  hom_inv_id := BinPres.renameHom_comp θ c θ' c' h₂ h₃ h₂' h₃' hθ hc
  inv_hom_id := BinPres.renameHom_comp θ' c' θ c h₂' h₃' h₂ h₃ hθ' hc'

end RenamePres

end FreeBin

/-! ## `ComTrias^! ≅ PostLie` -/

section Iso

open FreeBin

/-- `mid ↦ bracket`, `left ↦ product`. -/
def ComTriOp.toPostLie : ComTriOp → PostLieOp
  | .mid => .bracket
  | .left => .product

/-- `bracket ↦ mid`, `product ↦ left`. -/
def PostLieOp.toComTri : PostLieOp → ComTriOp
  | .bracket => .mid
  | .product => .left

variable (K : Type u) [Field K] [CharZero K]

/-- The rescaling `mid ↦ [-, -]/2`. -/
noncomputable def halfScale : ComTriOp → K
  | .mid => (2 : K)⁻¹
  | .left => 1

/-- The rescaling `[-, -] ↦ 2 mid`. -/
noncomputable def twiceScale : PostLieOp → K
  | .bracket => 2
  | .product => 1

omit [CharZero K] in
lemma twist2_comm_set : twist2 K '' {BinRel.comm K ComTriOp.mid} = {BinRel.antisymm K .mid} := by
  rw [comm_set_eq, twist2_commC, antisymm_set_eq]

section Images

omit [CharZero K]

lemma rename_half_antisymm :
    (rename K ComTriOp.toPostLie (halfScale K)).app _ (BinRel.antisymm K .mid)
      = (2 : K)⁻¹ • BinRel.antisymm K .bracket := by
  simp [BinRel.antisymm, rename_bin2, halfScale, ComTriOp.toPostLie]

lemma rename_half_jacobi :
    (rename K ComTriOp.toPostLie (halfScale K)).app _ (BinRel.jacobi K .mid)
      = ((2 : K)⁻¹ * (2 : K)⁻¹) • BinRel.jacobi K .bracket := by
  simp [BinRel.jacobi, rename_binL, halfScale, ComTriOp.toPostLie]

lemma rename_half_postLie₁ :
    (rename K ComTriOp.toPostLie (halfScale K)).app _ (BinRel.postLie₁ K .mid .left)
      = (2 : K)⁻¹ • BinRel.postLie₁ K .bracket .product := by
  simp [BinRel.postLie₁, rename_binL, rename_binR, halfScale, ComTriOp.toPostLie, smul_sub]

lemma rename_half_postLieHalf₂ [CharZero K] :
    (rename K ComTriOp.toPostLie (halfScale K)).app _ (BinRel.postLieHalf₂ K .mid .left)
      = BinRel.postLie₂ K .bracket .product := by
  simp [BinRel.postLieHalf₂, BinRel.postLie₂, rename_binL, rename_binR, halfScale,
    ComTriOp.toPostLie, smul_smul]

lemma rename_half_preLie :
    (rename K ComTriOp.toPostLie (halfScale K)).app _ (BinRel.preLie K .left)
      = BinRel.preLie K .product := by
  simp [BinRel.preLie, rename_binL, rename_binR, halfScale, ComTriOp.toPostLie]

lemma rename_twice_antisymm :
    (rename K PostLieOp.toComTri (twiceScale K)).app _ (BinRel.antisymm K .bracket)
      = (2 : K) • BinRel.antisymm K .mid := by
  simp [BinRel.antisymm, rename_bin2, twiceScale, PostLieOp.toComTri]

lemma rename_twice_jacobi :
    (rename K PostLieOp.toComTri (twiceScale K)).app _ (BinRel.jacobi K .bracket)
      = ((2 : K) * 2) • BinRel.jacobi K .mid := by
  simp [BinRel.jacobi, rename_binL, twiceScale, PostLieOp.toComTri]

lemma rename_twice_postLie₁ :
    (rename K PostLieOp.toComTri (twiceScale K)).app _ (BinRel.postLie₁ K .bracket .product)
      = (2 : K) • BinRel.postLie₁ K .mid .left := by
  simp [BinRel.postLie₁, rename_binL, rename_binR, twiceScale, PostLieOp.toComTri, smul_sub]

lemma rename_twice_postLie₂ :
    (rename K PostLieOp.toComTri (twiceScale K)).app _ (BinRel.postLie₂ K .bracket .product)
      = BinRel.postLieHalf₂ K .mid .left := by
  simp [BinRel.postLie₂, BinRel.postLieHalf₂, rename_binL, rename_binR, twiceScale,
    PostLieOp.toComTri]

lemma rename_twice_preLie :
    (rename K PostLieOp.toComTri (twiceScale K)).app _ (BinRel.preLie K .product)
      = BinRel.preLie K .left := by
  simp [BinRel.preLie, rename_binL, rename_binR, twiceScale, PostLieOp.toComTri]

end Images

section Memberships

omit [CharZero K]

lemma mem_span_two {G : Type v} {r₂ : Set (FreeBin K G (Fin 2))} {r₃ : Set (FreeBin K G (Fin 3))}
    {x : FreeBin K G (Fin 2)} (hx : x ∈ r₂) (c : K) :
    c • x ∈ (SymOperadIdeal.span K (rel23 r₂ r₃)).sub (Fin 2) :=
  Submodule.smul_mem _ c (SymOperadIdeal.subset_span (R := K) 2 hx)

lemma mem_span_three {G : Type v} {r₂ : Set (FreeBin K G (Fin 2))} {r₃ : Set (FreeBin K G (Fin 3))}
    {x : FreeBin K G (Fin 3)} (hx : x ∈ r₃) (c : K) :
    c • x ∈ (SymOperadIdeal.span K (rel23 r₂ r₃)).sub (Fin 3) :=
  Submodule.smul_mem _ c (SymOperadIdeal.subset_span (R := K) 3 hx)

lemma half_mem₂ : ∀ x ∈ ({BinRel.antisymm K ComTriOp.mid} : Set (FreeBin K ComTriOp (Fin 2))),
    (rename K ComTriOp.toPostLie (halfScale K)).app _ x ∈ (SymOperadIdeal.span K
      (rel23 {BinRel.antisymm K PostLieOp.bracket} (postLieRel K))).sub (Fin 2) := by
  rintro x rfl
  rw [rename_half_antisymm]
  exact mem_span_two K (Set.mem_singleton _) _

lemma half_mem₃ [CharZero K] : ∀ x ∈ postLieHalfRel K,
    (rename K ComTriOp.toPostLie (halfScale K)).app _ x ∈
    (SymOperadIdeal.span K (rel23 {BinRel.antisymm K PostLieOp.bracket} (postLieRel K))).sub
      (Fin 3) := by
  rintro x (rfl | rfl | rfl)
  · rw [rename_half_jacobi]
    exact mem_span_three K (by simp [postLieRel]) _
  · rw [rename_half_postLie₁]
    exact mem_span_three K (by simp [postLieRel]) _
  · rw [rename_half_postLieHalf₂, ← one_smul K (BinRel.postLie₂ K _ _)]
    exact mem_span_three K (by simp [postLieRel]) _

lemma halfLead_mem₂ : ∀ x ∈ ({BinRel.antisymm K ComTriOp.mid} : Set (FreeBin K ComTriOp (Fin 2))),
    (rename K ComTriOp.toPostLie (halfScale K)).app _ x ∈ (SymOperadIdeal.span K
      (rel23 {BinRel.antisymm K PostLieOp.bracket} (postLieLeadRel K))).sub (Fin 2) := by
  rintro x rfl
  rw [rename_half_antisymm]
  exact mem_span_two K (Set.mem_singleton _) _

lemma halfLead_mem₃ : ∀ x ∈ postLieLeadHalfRel K,
    (rename K ComTriOp.toPostLie (halfScale K)).app _ x ∈ (SymOperadIdeal.span K
      (rel23 {BinRel.antisymm K PostLieOp.bracket} (postLieLeadRel K))).sub (Fin 3) := by
  rintro x (rfl | rfl | rfl)
  · rw [rename_half_jacobi]
    exact mem_span_three K (by simp [postLieLeadRel]) _
  · rw [rename_half_postLie₁]
    exact mem_span_three K (by simp [postLieLeadRel]) _
  · rw [rename_half_preLie, ← one_smul K (BinRel.preLie K _)]
    exact mem_span_three K (by simp [postLieLeadRel]) _

lemma twice_mem₂ (r₃ : Set (FreeBin K ComTriOp (Fin 3))) :
    ∀ x ∈ ({BinRel.antisymm K PostLieOp.bracket} : Set (FreeBin K PostLieOp (Fin 2))),
      (rename K PostLieOp.toComTri (twiceScale K)).app _ x ∈ (SymOperadIdeal.span K
        (rel23 (twist2 K '' {BinRel.comm K ComTriOp.mid}) r₃)).sub (Fin 2) := by
  rintro x rfl
  rw [rename_twice_antisymm]
  exact mem_span_two K (by rw [twist2_comm_set]; rfl) _

lemma twice_mem₃ : ∀ x ∈ postLieRel K, (rename K PostLieOp.toComTri (twiceScale K)).app _ x ∈
    (SymOperadIdeal.span K (rel23 {BinRel.antisymm K ComTriOp.mid} (postLieHalfRel K))).sub
      (Fin 3) := by
  rintro x (rfl | rfl | rfl)
  · rw [rename_twice_jacobi]
    exact mem_span_three K (by simp [postLieHalfRel]) _
  · rw [rename_twice_postLie₁]
    exact mem_span_three K (by simp [postLieHalfRel]) _
  · rw [rename_twice_postLie₂, ← one_smul K (BinRel.postLieHalf₂ K _ _)]
    exact mem_span_three K (by simp [postLieHalfRel]) _

lemma twiceLead_mem₃ : ∀ x ∈ postLieLeadRel K,
    (rename K PostLieOp.toComTri (twiceScale K)).app _ x ∈ (SymOperadIdeal.span K
      (rel23 {BinRel.antisymm K ComTriOp.mid} (postLieLeadHalfRel K))).sub (Fin 3) := by
  rintro x (rfl | rfl | rfl)
  · rw [rename_twice_jacobi]
    exact mem_span_three K (by simp [postLieLeadHalfRel]) _
  · rw [rename_twice_postLie₁]
    exact mem_span_three K (by simp [postLieLeadHalfRel]) _
  · rw [rename_twice_preLie, ← one_smul K (BinRel.preLie K _)]
    exact mem_span_three K (by simp [postLieLeadHalfRel]) _

end Memberships

lemma halfScale_twiceScale (g : ComTriOp) :
    twiceScale K (g.toPostLie) * halfScale K g = 1 := by
  cases g <;> simp [halfScale, twiceScale, ComTriOp.toPostLie]

lemma twiceScale_halfScale (g : PostLieOp) :
    halfScale K (g.toComTri) * twiceScale K g = 1 := by
  cases g <;> simp [halfScale, twiceScale, PostLieOp.toComTri]

/-- **`ComTrias^! ≅ PostLie`** (Vallette, *Homology of generalized partition posets*, Thm. 30):
over a field of characteristic zero, the Koszul dual of commutative trialgebras is the post-Lie
operad, with `mid` going to half the bracket and `left` to the product. -/
noncomputable def BinComTrias.dualIso :
    SymOperadIso K (BinPres.dual23 K {BinRel.comm K ComTriOp.mid} (comTriasRel K)) (PostLie K) :=
  BinPres.renameIso ComTriOp.toPostLie (halfScale K) PostLieOp.toComTri (twiceScale K)
    (by rw [twist2_comm_set]; exact half_mem₂ K)
    (fun x hx => rename_mem_span _ _ (half_mem₂ K) (half_mem₃ K) (by
      rw [← dual23_comTrias K]; exact SymOperadIdeal.subset_span (R := K) 3 hx))
    (twice_mem₂ K _)
    (fun x hx => by rw [dual23_comTrias K]; exact twice_mem₃ K x hx)
    (fun g => by cases g <;> rfl) (halfScale_twiceScale K)
    (fun g => by cases g <;> rfl) (twiceScale_halfScale K)

/-- **The Koszul dual of the leading forms of `ComTrias` is `PostLieLead`**: over a field of
characteristic zero, with `mid` going to half the bracket and `left` to the product. -/
noncomputable def BinComTriasLead.dualIso :
    SymOperadIso K (BinPres.dual23 K {BinRel.comm K ComTriOp.mid} (comTriasLeadRel K))
      (PostLieLead K) :=
  BinPres.renameIso ComTriOp.toPostLie (halfScale K) PostLieOp.toComTri (twiceScale K)
    (by rw [twist2_comm_set]; exact halfLead_mem₂ K)
    (fun x hx => rename_mem_span _ _ (halfLead_mem₂ K) (halfLead_mem₃ K) (by
      rw [← dual23_comTriasLead K]; exact SymOperadIdeal.subset_span (R := K) 3 hx))
    (twice_mem₂ K _)
    (fun x hx => by rw [dual23_comTriasLead K]; exact twiceLead_mem₃ K x hx)
    (fun g => by cases g <;> rfl) (halfScale_twiceScale K)
    (fun g => by cases g <;> rfl) (twiceScale_halfScale K)

end Iso

end Operad
