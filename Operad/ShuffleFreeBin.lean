/-
# The free operad on binary generators as a free shuffle operad

The general results of `Operad.ShuffleFreeSym` and `Operad.ShuffleSymPres`, specialized to the
free operad `FreeBin R G` on binary generators and to the binary presented operads `BinPres`, and
identified with the binary shuffle machinery of `Operad.ShuffleTree`.

* `FreeBin.shuffleBasis`: **the free operad on binary generators has, on every finite linear order,
  a basis of shuffle monomials** with vertices the generators with a permutation of their two
  inputs; `BinPres.presBasis`: **PBW bases of binary presented operads** from resolvable rules.
* **Binary shuffle trees are the shuffle monomials** (`LTree.toSTree`, `LTree.monoEquiv`): the
  monomials of `Operad.LTree.monomials` with decorations `G × Perm (Fin 2)` are the shuffle
  monomials of the free shuffle operad on the relabelled binary generators. So the dimension of
  the free operad on binary generators is `(2n - 1)!! (2 |G|)ⁿ` in arity `n + 1`
  (`FreeBin.finrank_eq_doubleFactorial`), by `Operad.LTree.card_monomials`.
-/
import Operad.ShuffleSymPres
import Operad.BinaryQuadratic
import Operad.ShuffleTree

universe u v

namespace Operad

instance BinGen.isEmpty_zero (G : Type v) : IsEmpty (BinGen G 0) := ⟨fun x => by cases x⟩

/-! ## Binary shuffle trees -/

namespace LTree

variable {G : Type v}

/-- **A binary shuffle tree as a shuffle tree**, the decoration of a vertex being a generator with
a permutation of its two inputs. -/
def toSTree : LTree (G × Equiv.Perm (Fin 2)) → STree (SGen (BinGen G))
  | leaf a => STree.leaf a
  | node e l r => STree.node (BinGen.op e.1, e.2) ![toSTree l, toSTree r]

/-- **A shuffle tree on binary generators as a binary tree.** -/
def ofSTree : STree (SGen (BinGen G)) → LTree (G × Equiv.Perm (Fin 2))
  | STree.leaf a => leaf a
  | STree.node (BinGen.op g, σ) c => node (g, σ) (ofSTree (c 0)) (ofSTree (c 1))

lemma ofSTree_toSTree : ∀ t : LTree (G × Equiv.Perm (Fin 2)), ofSTree (toSTree t) = t
  | leaf _ => rfl
  | node e l r => by
    show node (e.1, e.2) (ofSTree (toSTree l)) (ofSTree (toSTree r)) = node e l r
    rw [ofSTree_toSTree l, ofSTree_toSTree r]

lemma toSTree_ofSTree : ∀ m : STree (SGen (BinGen G)), toSTree (ofSTree m) = m
  | STree.leaf _ => rfl
  | STree.node (BinGen.op g, σ) c => by
    show STree.node (BinGen.op g, σ) ![toSTree (ofSTree (c 0)), toSTree (ofSTree (c 1))] =
      STree.node (BinGen.op g, σ) c
    rw [toSTree_ofSTree (c 0), toSTree_ofSTree (c 1)]
    congr 1
    funext j
    fin_cases j <;> rfl

lemma labels_toSTree : ∀ t : LTree (G × Equiv.Perm (Fin 2)),
    (toSTree t).labels = (t.labels : Multiset ℕ)
  | leaf _ => rfl
  | node e l r => by
    show (STree.node (BinGen.op e.1, e.2) ![toSTree l, toSTree r]).labels = _
    rw [STree.labels_node, Fin.sum_univ_two, labels_node, ← Multiset.coe_add]
    exact congrArg₂ (· + ·) (labels_toSTree l) (labels_toSTree r)

/-- On a shuffle tree the leftmost leaf is the least one. -/
lemma first_toSTree : ∀ t : LTree (G × Equiv.Perm (Fin 2)), t.IsShuffle →
    (toSTree t).first = t.minLabel
  | leaf _, _ => rfl
  | node e l r, h => by
    show (STree.node (BinGen.op e.1, e.2) ![toSTree l, toSTree r]).first = _
    rw [STree.first_node _ _ (by omega), minLabel_node_of_shuffle h]
    exact first_toSTree l h.2.1

lemma isShuffle_toSTree : ∀ t : LTree (G × Equiv.Perm (Fin 2)), t.IsShuffle →
    (toSTree t).IsShuffle
  | leaf _, _ => trivial
  | node e l r, h => by
    refine ⟨by omega, fun i => ?_, Fin.strictMono_iff_lt_succ.2 fun i => ?_⟩
    · fin_cases i
      · exact isShuffle_toSTree l h.2.1
      · exact isShuffle_toSTree r h.2.2
    · fin_cases i
      show (toSTree l).first < (toSTree r).first
      rw [first_toSTree l h.2.1, first_toSTree r h.2.2]
      exact h.1

lemma isShuffle_of_toSTree : ∀ t : LTree (G × Equiv.Perm (Fin 2)), (toSTree t).IsShuffle →
    t.IsShuffle
  | leaf _, _ => trivial
  | node e l r, h => by
    have hl := isShuffle_of_toSTree l (h.child 0)
    have hr := isShuffle_of_toSTree r (h.child 1)
    refine ⟨?_, hl, hr⟩
    have := h.mono (show (0 : Fin 2) < 1 by decide)
    change (toSTree l).first < (toSTree r).first at this
    rwa [first_toSTree l hl, first_toSTree r hr] at this

/-- **The binary shuffle monomials are the shuffle monomials** on the relabelled binary
generators. -/
def monoEquiv [Fintype G] [DecidableEq G] (n : ℕ) :
    {t // t ∈ monomials (E := G × Equiv.Perm (Fin 2)) n} ≃ STree.SMono (SGen (BinGen G))
      (Finset.range n) where
  toFun t := ⟨toSTree t.1, isShuffle_toSTree _ ((mem_monomials n t.1).1 t.2).1, by
    rw [labels_toSTree, Finset.range_val, ← Multiset.coe_range]
    exact Multiset.coe_eq_coe.2 ((mem_monomials n t.1).1 t.2).2⟩
  invFun m := ⟨ofSTree m.1, (mem_monomials n _).2 ⟨isShuffle_of_toSTree _ (by
      rw [toSTree_ofSTree]
      exact m.isShuffle), by
    have h1 : ((ofSTree m.1).labels : Multiset ℕ) = Multiset.range n := by
      rw [← labels_toSTree, toSTree_ofSTree]
      exact m.labels_eq
    exact Multiset.coe_eq_coe.1 (h1.trans (Multiset.coe_range n).symm)⟩⟩
  left_inv t := Subtype.ext (ofSTree_toSTree t.1)
  right_inv m := Subtype.ext (toSTree_ofSTree m.1)

end LTree

/-! ## The free operad on binary generators -/

namespace FreeBin

variable (R : Type u) [CommRing R] (G : Type v)

/-- **The shuffle-monomial basis of the free operad on binary generators**, on every finite linear
order. -/
noncomputable def shuffleBasis (A : Type) [Fintype A] [LinearOrder A] :
    Module.Basis (STree.SMono (SGen (BinGen G)) (Finset.range (Fintype.card A))) R
      (FreeBin R G A) :=
  FreeSet.shuffleBasis R A

/-- **The dimension of the free operad on binary generators** in arity `n + 1`:
`(2n - 1)!! (2 |G|)ⁿ`, the number of binary shuffle monomials. -/
theorem finrank_eq_doubleFactorial [Nontrivial R] [Fintype G] [DecidableEq G] (A : Type)
    [Fintype A] [LinearOrder A] (n : ℕ) (hA : Fintype.card A = n + 1) :
    Module.finrank R (FreeBin R G A) =
      Nat.doubleFactorial (2 * n - 1) * (Fintype.card G * 2) ^ n := by
  haveI : Fintype (STree.SMono (SGen (BinGen G)) (Finset.range (Fintype.card A))) :=
    Fintype.ofEquiv _ (LTree.monoEquiv (G := G) (Fintype.card A))
  rw [Module.finrank_eq_card_basis (shuffleBasis R G A),
    ← Fintype.card_congr (LTree.monoEquiv (G := G) (Fintype.card A)), Fintype.card_coe, hA,
    LTree.card_monomials, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]
  rfl

end FreeBin

/-- **PBW bases of binary presented operads** (Dotsenko–Khoroshkin): when the sorted relabellings
of the relators generate the ideal of a resolvable set of rules, the normal monomials are a basis
of the operad presented by binary generators and relators of arities two and three. -/
noncomputable def BinPres.presBasis (R : Type u) [CommRing R] {G : Type v}
    (r₂ : Set (FreeBin R G (Fin 2))) (r₃ : Set (FreeBin R G (Fin 3))) {ρ : Type*}
    {O : STree.AdmOrder (SGen (BinGen G))} (Gr : Rules R ρ O.toCtxOrder)
    (hG : ShuffleOperadIdeal.span R (FreeSet.shuffleRel R (rel23 r₂ r₃)) = Gr.shuffleIdeal)
    (hres : ∀ C, (Gr.rw C).Resolvable) (A : Type) [Fintype A] [LinearOrder A] :
    Module.Basis (Gr.rw (Finset.range (Fintype.card A))).Irr R (BinPres R r₂ r₃ A) :=
  FreeSet.presBasis R (rel23 r₂ r₃) Gr hG hres A

end Operad
