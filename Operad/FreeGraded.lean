/-
# Free graded operads

Generators of any arity carrying parities, `gp k : T k → Bool`, span **the free graded operad**
`FreeGr R gp`: in every arity, the free module on the planar trees with vertices labelled by the
generators and leaves labelled by the inputs, composed by grafting with a Koszul sign. Composing
`y` into the leaf `r` of `x` moves the vertices of `y` across those of `x` met after the leaf `r`
in the preorder, reading the tree from the root, depth first and left to right; this costs
`σ(|y| · apar(x, r))`.

* **Parities of trees.** A tree has the parity of its vertices (`Tree.tpar`), and each leaf the
  parity of the vertices after it (`Tree.apar`). Grafting adds parities (`Tree.tpar_graft`). The
  leaves of the grafted tree see its vertices and then those of the outer tree after the graft
  point (`Tree.apar_graft_inner`), the leaves before the graft point see the grafted tree in
  addition (`Tree.apar_graft_before`), and the leaves after it see no change
  (`Tree.apar_graft_after`).
* **Sign data** (`SgnData`): a linear order of the inputs, a parity after each input and a total
  parity. They form a set operad (`SgnData.instSetOperad`) on which the sign of a composite,
  `sgn i x y = |y| · aft_x(i)`, is a cocycle: sequentially (`SgnData.sgn_seq`), and in parallel up
  to the exchange sign `|y| |z|` (`SgnData.sgn_par`).
* **Twisted linearizations.** The linearization of a set operad over sign data, composed with the
  sign of the data, is a graded operad (`SgnLin.instGrOperad`). Dually, the homogeneous operations
  of a graded operad with sign data, composed with the sign of the data, form a set operad
  (`SgnOp.instSetOperad`): the signs of the data make up for the Koszul signs. **A morphism of
  graded operads (`GrOperadHom`) out of a twisted linearization is a morphism of set operads into
  the homogeneous operations with sign data, over the sign data** (`SgnLin.homEquiv`).
* The free graded operad is the twisted linearization of the regular operad of planar trees over
  their sign data (`FreeGr.treeSgn`). That operad is the free set operad on the generators, so
  **a morphism of graded operads out of `FreeGr R gp` is a choice of an operation of the parity of
  each generator** (`FreeGr.homEquiv`, `FreeGr.hom_ext`).
-/
import Operad.CofreeCooperad
import Operad.DGOperad

universe u v w

namespace Operad

namespace Tree

variable {E : ℕ → Type v} (gp : ∀ k, E k → Bool)

mutual

/-- **The parity of a tree**: the sum of the parities of its vertices. -/
def tpar : Tree E → Bool
  | .leaf => false
  | .node e f => xor (gp _ e) (Forest.tparF f)

/-- The parity of a forest. -/
def _root_.Operad.Forest.tparF : ∀ {k : ℕ}, Forest E k → Bool
  | _, .nil => false
  | _, .cons t f => xor (tpar t) (Forest.tparF f)

end

mutual

/-- **The parity after a leaf**: the sum of the parities of the vertices met after the leaf `p` in
the preorder. -/
def apar : Tree E → ℕ → Bool
  | .leaf, _ => false
  | .node _ f, p => Forest.aparF f p

/-- The parity after a leaf, in a forest. -/
def _root_.Operad.Forest.aparF : ∀ {k : ℕ}, Forest E k → ℕ → Bool
  | _, .nil, _ => false
  | _, .cons t f, p =>
      if p < t.arity then xor (apar t p) (Forest.tparF gp f) else Forest.aparF f (p - t.arity)

end

@[simp] lemma tpar_leaf : tpar gp (.leaf : Tree E) = false := rfl

@[simp] lemma tpar_node {k : ℕ} (e : E k) (f : Forest E k) :
    tpar gp (.node e f) = xor (gp _ e) (Forest.tparF gp f) := rfl

@[simp] lemma apar_leaf (p : ℕ) : apar gp (.leaf : Tree E) p = false := rfl

@[simp] lemma apar_node {k : ℕ} (e : E k) (f : Forest E k) (p : ℕ) :
    apar gp (.node e f) p = Forest.aparF gp f p := rfl

lemma aparF_cons_of_lt {k : ℕ} (t : Tree E) (f : Forest E k) {p : ℕ} (h : p < t.arity) :
    Forest.aparF gp (.cons t f) p = xor (apar gp t p) (Forest.tparF gp f) := by
  rw [Forest.aparF, if_pos h]

lemma aparF_cons_of_ge {k : ℕ} (t : Tree E) (f : Forest E k) {p : ℕ} (h : t.arity ≤ p) :
    Forest.aparF gp (.cons t f) p = Forest.aparF gp f (p - t.arity) := by
  rw [Forest.aparF, if_neg (by omega)]

@[simp] lemma tparF_cons {k : ℕ} (t : Tree E) (f : Forest E k) :
    Forest.tparF gp (.cons t f) = xor (tpar gp t) (Forest.tparF gp f) := rfl

mutual

/-- **Grafting adds parities.** -/
theorem tpar_graft : ∀ (t : Tree E) (p : ℕ) (s : Tree E), p < t.arity →
    tpar gp (t.graft p s) = xor (tpar gp t) (tpar gp s)
  | .leaf, p, s, _ => by simp
  | .node e f, p, s, h => by
      simp only [graft_node, tpar_node]
      rw [Forest.tparF_graftF f p s h, Bool.xor_assoc]

/-- The forest half of `tpar_graft`. -/
theorem _root_.Operad.Forest.tparF_graftF : ∀ {k : ℕ} (f : Forest E k) (p : ℕ) (s : Tree E),
    p < f.arityF → Forest.tparF gp (f.graftF p s) = xor (Forest.tparF gp f) (tpar gp s)
  | _, .nil, _, _, h => by simp at h
  | _, .cons t f, p, s, h => by
      simp only [arityF_cons] at h
      by_cases hlt : p < t.arity
      · rw [graftF_cons_of_lt s hlt, tparF_cons, tparF_cons, tpar_graft t p s hlt]
        cases tpar gp t <;> cases tpar gp s <;> cases Forest.tparF gp f <;> rfl
      · rw [graftF_cons_of_ge s (by omega), tparF_cons, tparF_cons,
          Forest.tparF_graftF f (p - t.arity) s (by omega), Bool.xor_assoc]

end

mutual

/-- **The leaves of a grafted tree** see its vertices, and then those of the outer tree after the
graft point. -/
theorem apar_graft_inner : ∀ (t : Tree E) (p : ℕ) (s : Tree E) (j : ℕ), p < t.arity →
    j < s.arity → apar gp (t.graft p s) (p + j) = xor (apar gp s j) (apar gp t p)
  | .leaf, p, s, j, h, _ => by
      obtain rfl : p = 0 := by simpa using h
      simp
  | .node e f, p, s, j, h, hj => by
      simp only [graft_node, apar_node]
      exact Forest.aparF_graftF_inner f p s j h hj

/-- The forest half of `apar_graft_inner`. -/
theorem _root_.Operad.Forest.aparF_graftF_inner : ∀ {k : ℕ} (f : Forest E k) (p : ℕ)
    (s : Tree E) (j : ℕ), p < f.arityF → j < s.arity →
    Forest.aparF gp (f.graftF p s) (p + j) = xor (apar gp s j) (Forest.aparF gp f p)
  | _, .nil, _, _, _, h, _ => by simp at h
  | _, .cons t f, p, s, j, h, hj => by
      simp only [arityF_cons] at h
      by_cases hlt : p < t.arity
      · have harity := arity_graft t p s hlt
        rw [graftF_cons_of_lt s hlt, aparF_cons_of_lt gp _ _ (by omega),
          apar_graft_inner t p s j hlt hj, aparF_cons_of_lt gp _ _ hlt, Bool.xor_assoc]
      · rw [graftF_cons_of_ge s (by omega), aparF_cons_of_ge gp _ _ (by omega),
          aparF_cons_of_ge gp _ _ (by omega), show p + j - t.arity = p - t.arity + j by omega,
          Forest.aparF_graftF_inner f (p - t.arity) s j (by omega) hj]

end

mutual

/-- **The leaves before the graft point** see the grafted tree in addition. -/
theorem apar_graft_before : ∀ (t : Tree E) (p : ℕ) (s : Tree E) (q : ℕ), q < p →
    p < t.arity → apar gp (t.graft p s) q = xor (apar gp t q) (tpar gp s)
  | .leaf, p, s, q, hq, h => by
      have : p = 0 := by simpa using h
      omega
  | .node e f, p, s, q, hq, h => by
      simp only [graft_node, apar_node]
      exact Forest.aparF_graftF_before f p s q hq h

/-- The forest half of `apar_graft_before`. -/
theorem _root_.Operad.Forest.aparF_graftF_before : ∀ {k : ℕ} (f : Forest E k) (p : ℕ)
    (s : Tree E) (q : ℕ), q < p → p < f.arityF →
    Forest.aparF gp (f.graftF p s) q = xor (Forest.aparF gp f q) (tpar gp s)
  | _, .nil, _, _, _, _, h => by simp at h
  | _, .cons t f, p, s, q, hq, h => by
      simp only [arityF_cons] at h
      by_cases hlt : p < t.arity
      · have harity := arity_graft t p s hlt
        rw [graftF_cons_of_lt s hlt, aparF_cons_of_lt gp _ _ (by omega),
          apar_graft_before t p s q hq hlt, aparF_cons_of_lt gp _ _ (by omega)]
        cases apar gp t q <;> cases tpar gp s <;> cases Forest.tparF gp f <;> rfl
      · rw [graftF_cons_of_ge s (by omega)]
        by_cases hqa : q < t.arity
        · rw [aparF_cons_of_lt gp _ _ hqa, aparF_cons_of_lt gp _ _ hqa,
            Forest.tparF_graftF gp f (p - t.arity) s (by omega), Bool.xor_assoc]
        · rw [aparF_cons_of_ge gp _ _ (by omega), aparF_cons_of_ge gp _ _ (by omega),
            Forest.aparF_graftF_before f (p - t.arity) s (q - t.arity) (by omega) (by omega)]

end

mutual

/-- **The leaves after the graft point** see no change. -/
theorem apar_graft_after : ∀ (t : Tree E) (p : ℕ) (s : Tree E) (q : ℕ), p < q →
    q < t.arity → apar gp (t.graft p s) (q + s.arity - 1) = apar gp t q
  | .leaf, p, s, q, hpq, hq => by
      have : q = 0 := by simpa using hq
      omega
  | .node e f, p, s, q, hpq, hq => by
      simp only [graft_node, apar_node]
      exact Forest.aparF_graftF_after f p s q hpq hq

/-- The forest half of `apar_graft_after`. -/
theorem _root_.Operad.Forest.aparF_graftF_after : ∀ {k : ℕ} (f : Forest E k) (p : ℕ)
    (s : Tree E) (q : ℕ), p < q → q < f.arityF →
    Forest.aparF gp (f.graftF p s) (q + s.arity - 1) = Forest.aparF gp f q
  | _, .nil, _, _, _, _, h => by simp at h
  | _, .cons t f, p, s, q, hpq, h => by
      simp only [arityF_cons] at h
      by_cases hlt : p < t.arity
      · have harity := arity_graft t p s hlt
        rw [graftF_cons_of_lt s hlt]
        by_cases hqa : q < t.arity
        · rw [aparF_cons_of_lt gp _ _ (by omega), apar_graft_after t p s q hpq hqa,
            aparF_cons_of_lt gp _ _ hqa]
        · rw [aparF_cons_of_ge gp _ _ (by omega), aparF_cons_of_ge gp _ _ (by omega)]
          congr 1
          omega
      · rw [graftF_cons_of_ge s (by omega), aparF_cons_of_ge gp _ _ (by omega),
          aparF_cons_of_ge gp _ _ (by omega),
          show q + s.arity - 1 - t.arity = q - t.arity + s.arity - 1 by omega,
          Forest.aparF_graftF_after f (p - t.arity) s (q - t.arity) (by omega) (by omega)]

end

end Tree

/-! ## Sign data -/

open Sym GerBV

/-- **Sign data** on a set of inputs: a linear order of the inputs, a parity after each input, and
a total parity. A planar tree with its leaves labelled carries the order of its leaves, the parity
of the vertices after each leaf in the preorder, and the parity of all its vertices
(`FreeGr.treeSgn`). -/
@[ext]
structure SgnData (A : Type) where
  /-- The order of the inputs. -/
  ord : LinOrd A
  /-- The parity after each input. -/
  aft : A → Bool
  /-- The total parity. -/
  tot : Bool

/-- Sign data, as a species. -/
@[nolint unusedArguments]
abbrev SgnD : (A : Type) → [Fintype A] → [DecidableEq A] → Type := fun A _ _ => SgnData A

namespace SgnData

variable {A B D : Type}

/-- Relabelling sign data. -/
def map (e : A ≃ B) (x : SgnData A) : SgnData B := ⟨LinOrd.map e x.ord, x.aft ∘ e.symm, x.tot⟩

/-- The sign data of the identity. -/
def one : SgnData Unit := ⟨LinOrd.one, fun _ => false, false⟩

@[simp] lemma map_ord (e : A ≃ B) (x : SgnData A) : (map e x).ord = LinOrd.map e x.ord := rfl

@[simp] lemma map_aft (e : A ≃ B) (x : SgnData A) (b : B) : (map e x).aft b = x.aft (e.symm b) :=
  rfl

@[simp] lemma map_tot (e : A ≃ B) (x : SgnData A) : (map e x).tot = x.tot := rfl

@[simp] lemma one_aft (u : Unit) : one.aft u = false := rfl

@[simp] lemma one_tot : one.tot = false := rfl

variable [DecidableEq A]

open Classical in
/-- **Composition of sign data**: the orders are composed, the inputs before the slot see the
inserted parity in addition, and the inserted inputs see the parity after the slot. -/
noncomputable def comp (i : A) (x : SgnData A) (y : SgnData B) : SgnData (Without A i ⊕ B) where
  ord := LinOrd.comp i x.ord y.ord
  aft := Sum.elim (fun a => if x.ord.lt a.1 i then xor (x.aft a.1) y.tot else x.aft a.1)
    fun b => xor (y.aft b) (x.aft i)
  tot := xor x.tot y.tot

@[simp] lemma comp_ord (i : A) (x : SgnData A) (y : SgnData B) :
    (comp i x y).ord = LinOrd.comp i x.ord y.ord := rfl

@[simp] lemma comp_tot (i : A) (x : SgnData A) (y : SgnData B) :
    (comp i x y).tot = xor x.tot y.tot := rfl

@[simp] lemma comp_aft_inr (i : A) (x : SgnData A) (y : SgnData B) (b : B) :
    (comp i x y).aft (.inr b) = xor (y.aft b) (x.aft i) := rfl

open Classical in
lemma comp_aft_inl (i : A) (x : SgnData A) (y : SgnData B) (a : Without A i) :
    (comp i x y).aft (.inl a) = if x.ord.lt a.1 i then xor (x.aft a.1) y.tot else x.aft a.1 :=
  rfl

lemma comp_aft_inl_of_lt (i : A) (x : SgnData A) (y : SgnData B) (a : Without A i)
    (h : x.ord.lt a.1 i) : (comp i x y).aft (.inl a) = xor (x.aft a.1) y.tot :=
  if_pos h

lemma comp_aft_inl_of_not_lt (i : A) (x : SgnData A) (y : SgnData B) (a : Without A i)
    (h : ¬ x.ord.lt a.1 i) : (comp i x y).aft (.inl a) = x.aft a.1 :=
  if_neg h

end SgnData

namespace SgnData

variable {A : Type}

/-- The inputs other than `i` lie on one side of it. -/
lemma lt_or_lt (x : SgnData A) {i a : A} (h : a ≠ i) : x.ord.lt a i ∨ x.ord.lt i a :=
  x.ord.total a i h

lemma not_lt_of_lt (x : SgnData A) {a i : A} (h : x.ord.lt a i) : ¬ x.ord.lt i a :=
  fun h' => x.ord.irrefl a (x.ord.trans _ _ _ h h')

end SgnData

open SgnData in
/-- **Sign data form a set operad.** -/
noncomputable instance SgnData.instSetOperad : SetOperad SgnD where
  map e x := map e x
  map_refl x := SgnData.ext (SetOperad.map_refl (S := fun A _ _ => LinOrd A) x.ord) rfl rfl
  map_trans e f x :=
    SgnData.ext (SetOperad.map_trans (S := fun A _ _ => LinOrd A) e f x.ord) rfl rfl
  one := one
  comp i x y := comp i x y
  map_comp σ τ i x y := by
    refine SgnData.ext (SetOperad.map_comp (S := fun A _ _ => LinOrd A) σ τ i x.ord y.ord) ?_ rfl
    funext u
    rcases u with a | b
    · simp only [map_aft, compEquiv_symm_inl]
      by_cases h : x.ord.lt (σ.symm a.1) i
      · rw [comp_aft_inl_of_lt _ _ _ _ h, comp_aft_inl_of_lt _ _ _ _
          (by simpa only [map_ord, LinOrd.map_lt, Equiv.symm_apply_apply] using h)]
        rfl
      · rw [comp_aft_inl_of_not_lt _ _ _ _ h, comp_aft_inl_of_not_lt _ _ _ _
          (by simpa only [map_ord, LinOrd.map_lt, Equiv.symm_apply_apply] using h)]
        rfl
    · simp
  comp_one i x := by
    refine SgnData.ext (SetOperad.comp_one (S := fun A _ _ => LinOrd A) i x.ord) ?_
      (Bool.xor_false x.tot)
    funext a
    show (comp i x one).aft ((rightUnitEquiv i).symm a) = x.aft a
    by_cases h : a = i
    · subst h
      rw [rightUnitEquiv_symm_self, comp_aft_inr, one_aft, Bool.false_xor]
    · rw [rightUnitEquiv_symm_of_ne h]
      by_cases h' : x.ord.lt a i
      · rw [comp_aft_inl_of_lt _ _ _ _ h', one_tot, Bool.xor_false]
      · rw [comp_aft_inl_of_not_lt _ _ _ _ h']
  one_comp y := by
    refine SgnData.ext (SetOperad.one_comp (S := fun A _ _ => LinOrd A) y.ord) ?_
      (Bool.false_xor y.tot)
    funext b
    show (comp () one y).aft (Sum.inr b) = y.aft b
    rw [comp_aft_inr, one_aft, Bool.xor_false]
  comp_assoc_seq {A B D} _ _ _ _ _ _ i j x y z := by
    refine SgnData.ext (SetOperad.comp_assoc_seq (S := fun A _ _ => LinOrd A) i j x.ord y.ord
      z.ord) ?_ (Bool.xor_assoc _ _ _)
    funext u
    classical
    show (comp (Sum.inr j) (comp i x y) z).aft ((seqEquiv i j D).symm u) = _
    rcases u with a | b | d
    · simp only [seqEquiv_symm_inl, comp_aft_inl, comp_ord, LinOrd.comp_lt, LinOrd.compLt_inl_inr,
        comp_tot]
      split_ifs <;> simp
    · simp only [seqEquiv_symm_inr_inl, comp_aft_inl, comp_aft_inr, comp_ord, LinOrd.comp_lt,
        LinOrd.compLt_inr_inr]
      split_ifs
      · cases y.aft b.1 <;> cases z.tot <;> cases x.aft i <;> rfl
      · rfl
    · simp only [seqEquiv_symm_inr_inr, comp_aft_inr, Bool.xor_assoc]
  comp_assoc_par {A B D} _ _ _ _ _ _ i k hik x y z := by
    refine SgnData.ext (SetOperad.comp_assoc_par (S := fun A _ _ => LinOrd A) hik x.ord y.ord
      z.ord) ?_ (by
        simp only [map_tot, comp_tot]
        cases x.tot <;> cases y.tot <;> cases z.tot <;> rfl)
    funext u
    classical
    show (comp (Sum.inl ⟨k, Ne.symm hik⟩) (comp i x y) z).aft ((parEquiv hik B D).symm u) = _
    rcases u with ⟨a | d, ha⟩ | b
    · simp only [parEquiv_symm_inl_inl, comp_aft_inl, comp_ord, LinOrd.comp_lt,
        LinOrd.compLt_inl_inl]
      split_ifs <;> cases x.aft a.1 <;> cases y.tot <;> cases z.tot <;> rfl
    · simp only [parEquiv_symm_inl_inr, comp_aft_inl, comp_aft_inr, comp_ord, LinOrd.comp_lt,
        LinOrd.compLt_inr_inl]
      split_ifs <;> cases z.aft d <;> cases x.aft k <;> cases y.tot <;> rfl
    · simp only [parEquiv_symm_inr, comp_aft_inl, comp_aft_inr, comp_ord, LinOrd.comp_lt,
        LinOrd.compLt_inr_inl]
      split_ifs <;> cases y.aft b <;> cases x.aft i <;> cases z.tot <;> rfl

namespace SgnData

section Defs

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

@[simp] lemma map_def (e : A ≃ B) (x : SgnData A) : SetOperad.map (S := SgnD) e x = map e x := rfl

@[simp] lemma comp_def (i : A) (x : SgnData A) (y : SgnData B) :
    SetOperad.comp (S := SgnD) i x y = comp i x y := rfl

@[simp] lemma one_def : (SetOperad.one : SgnD Unit) = one := rfl

end Defs

variable {A B D : Type}

/-- **The sign of a composite**: inserting `y` at `i` moves it across the parity after `i`. -/
def sgn (i : A) (x : SgnData A) (y : SgnData B) : Bool := y.tot && x.aft i

lemma sgn_map {A' B' : Type} (σ : A ≃ A') (τ : B ≃ B') (i : A) (x : SgnData A) (y : SgnData B) :
    sgn (σ i) (map σ x) (map τ y) = sgn i x y := by
  simp [sgn]

@[simp] lemma sgn_one_right (i : A) (x : SgnData A) : sgn i x one = false := rfl

@[simp] lemma sgn_one_left (y : SgnData B) : sgn () one y = false := by
  simp [sgn]

variable [DecidableEq A] [DecidableEq B]

/-- **The sign cocycle, sequentially.** -/
lemma sgn_seq (i : A) (j : B) (x : SgnData A) (y : SgnData B) (z : SgnData D) :
    xor (sgn i x y) (sgn (Sum.inr j) (comp i x y) z) = xor (sgn j y z) (sgn i x (comp j y z)) := by
  simp only [sgn, comp_aft_inr, comp_tot]
  cases y.tot <;> cases x.aft i <;> cases z.tot <;> cases y.aft j <;> rfl

omit [DecidableEq B] in
/-- **The sign cocycle, in parallel**: the two orders differ by the exchange of `y` and `z`. -/
lemma sgn_par [DecidableEq D] {i k : A} (hik : i ≠ k) (x : SgnData A) (y : SgnData B)
    (z : SgnData D) :
    xor (sgn i x y) (sgn (Sum.inl ⟨k, Ne.symm hik⟩) (comp i x y) z)
      = xor (y.tot && z.tot) (xor (sgn k x z) (sgn (Sum.inl ⟨i, hik⟩) (comp k x z) y)) := by
  classical
  simp only [sgn, comp_aft_inl]
  rcases x.ord.total i k hik with h | h
  · rw [if_neg (not_lt_of_lt x h), if_pos h]
    cases y.tot <;> cases x.aft i <;> cases z.tot <;> cases x.aft k <;> rfl
  · rw [if_pos h, if_neg (not_lt_of_lt x h)]
    cases y.tot <;> cases x.aft i <;> cases z.tot <;> cases x.aft k <;> rfl

end SgnData

/-- `σ` turns sums of parities into products of signs. -/
lemma σ_xor (R : Type u) [CommRing R] (a b : Bool) : σ R (xor a b) = σ R a * σ R b := by
  cases a <;> cases b <;> simp

lemma σ_mul_self (R : Type u) [CommRing R] (a : Bool) : σ R a * σ R a = 1 := by
  cases a <;> simp

/-! ## The twisted linearization -/

section SgnLin

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]

set_option linter.unusedVariables false in
/-- **The linearization twisted by sign data**: the free modules on the operations of a set operad
with sign data, composed with the sign of the data and graded by the total parity
(`SgnLin.instGrOperad`). -/
@[nolint unusedArguments]
def SgnLin (R : Type u) [CommRing R] (δ : SetOperadHom S SgnD) (A : Type) [Fintype A]
    [DecidableEq A] : Type (max u v) :=
  S A →₀ R

namespace SgnLin

variable (R : Type u) [CommRing R] (δ : SetOperadHom S SgnD)

noncomputable instance (A : Type) [Fintype A] [DecidableEq A] : AddCommGroup (SgnLin R δ A) :=
  inferInstanceAs (AddCommGroup (S A →₀ R))

noncomputable instance (A : Type) [Fintype A] [DecidableEq A] : Module R (SgnLin R δ A) :=
  inferInstanceAs (Module R (S A →₀ R))

variable {A A' B B' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] [Fintype D] [DecidableEq D]

/-- The parity projections: the basis elements of total parity `b`. -/
noncomputable def parT (b : Bool) : (S A →₀ R) →ₗ[R] (S A →₀ R) :=
  Finsupp.lift (S A →₀ R) R (S A) fun x =>
    if (δ.app A x).tot = b then Finsupp.single x 1 else 0

/-- **Composition**, with the sign of the data. -/
noncomputable def compT (i : A) : (S A →₀ R) →ₗ[R] (S B →₀ R) →ₗ[R] (S (Without A i ⊕ B) →₀ R) :=
  Finsupp.lift _ R (S A) fun x => Finsupp.lift (S (Without A i ⊕ B) →₀ R) R (S B) fun y =>
    Finsupp.single (SetOperad.comp i x y) (σ R (SgnData.sgn i (δ.app A x) (δ.app B y)))

variable {R δ}

@[simp] lemma parT_single (b : Bool) (x : S A) (r : R) :
    parT R δ b (Finsupp.single x r)
      = if (δ.app A x).tot = b then Finsupp.single x r else 0 := by
  unfold parT
  rw [Finsupp.lift_apply, Finsupp.sum_single_index (by simp)]
  split_ifs
  · rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  · exact smul_zero r

@[simp] lemma compT_single (i : A) (x : S A) (y : S B) (r r' : R) :
    compT R δ i (Finsupp.single x r) (Finsupp.single y r')
      = Finsupp.single (SetOperad.comp i x y)
          (σ R (SgnData.sgn i (δ.app A x) (δ.app B y)) * (r * r')) := by
  unfold compT
  rw [Finsupp.lift_apply, Finsupp.sum_single_index (by simp), LinearMap.smul_apply,
    Finsupp.lift_apply, Finsupp.sum_single_index (by simp), Finsupp.smul_single,
    Finsupp.smul_single, smul_eq_mul, smul_eq_mul]
  congr 1
  ring

lemma parT_add (x : S A →₀ R) : parT R δ false x + parT R δ true x = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => rw [map_add, map_add, add_add_add_comm, hx, hx']
  | single s r =>
    rw [parT_single, parT_single]
    cases (δ.app A s).tot <;> simp

lemma parT_parT (b b' : Bool) (x : S A →₀ R) :
    parT R δ b (parT R δ b' x) = if b = b' then parT R δ b' x else 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' =>
    rw [map_add, map_add, hx, hx']
    split_ifs <;> simp
  | single s r =>
    rw [parT_single]
    by_cases h : (δ.app A s).tot = b'
    · rw [if_pos h, parT_single]
      by_cases hb : b = b'
      · rw [if_pos (h.trans hb.symm), if_pos hb]
      · rw [if_neg (fun h' => hb (h'.symm.trans h)), if_neg hb]
    · rw [if_neg h, map_zero]
      split_ifs <;> rfl

lemma mapL_parT (e : A ≃ B) (b : Bool) (x : S A →₀ R) :
    Lin.mapL R e (parT R δ b x) = parT R δ b (Lin.mapL R e x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | single s r =>
    rw [parT_single, Lin.mapL_single, parT_single, δ.app_map]
    split_ifs <;> simp_all

lemma parT_one : parT R δ false (Finsupp.single (SetOperad.one : S Unit) 1)
    = Finsupp.single SetOperad.one 1 := by
  rw [parT_single, δ.app_one, SgnData.one_def, SgnData.one_tot, if_pos rfl]

lemma compT_par (i : A) (p q : Bool) (x : S A →₀ R) (y : S B →₀ R) :
    parT R δ (xor p q) (compT R δ i (parT R δ p x) (parT R δ q y))
      = compT R δ i (parT R δ p x) (parT R δ q y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | single s r =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | single t r' =>
      rw [parT_single, parT_single]
      split_ifs with h1 h2
      · rw [compT_single, parT_single, δ.app_comp, SgnData.comp_def, SgnData.comp_tot, h1, h2,
          if_pos rfl]
      · simp
      · simp
      · simp

lemma mapL_compT (σ' : A ≃ A') (τ : B ≃ B') (i : A) (x : S A →₀ R) (y : S B →₀ R) :
    Lin.mapL R (compEquiv σ' τ i) (compT R δ i x y)
      = compT R δ (σ' i) (Lin.mapL R σ' x) (Lin.mapL R τ y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | single s r =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | single t r' =>
      rw [compT_single, Lin.mapL_single, Lin.mapL_single, Lin.mapL_single, compT_single,
        SetOperad.map_comp, δ.app_map, δ.app_map, SgnData.map_def, SgnData.map_def,
        SgnData.sgn_map]

lemma compT_one (i : A) (x : S A →₀ R) :
    Lin.mapL R (rightUnitEquiv i) (compT R δ i x (Finsupp.single SetOperad.one 1)) = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | single s r =>
    rw [compT_single, Lin.mapL_single, SetOperad.comp_one, δ.app_one, SgnData.one_def,
      SgnData.sgn_one_right, σ_false, one_mul, mul_one]

lemma one_compT (y : S B →₀ R) :
    Lin.mapL R (leftUnitEquiv B) (compT R δ () (Finsupp.single SetOperad.one 1) y) = y := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y y' hy hy' => simp only [map_add, hy, hy']
  | single t r =>
    rw [compT_single, Lin.mapL_single, SetOperad.one_comp, δ.app_one, SgnData.one_def,
      SgnData.sgn_one_left, σ_false, one_mul, one_mul]

lemma compT_assoc_seq (i : A) (j : B) (x : S A →₀ R) (y : S B →₀ R) (z : S D →₀ R) :
    Lin.mapL R (seqEquiv i j D) (compT R δ (Sum.inr j) (compT R δ i x y) z)
      = compT R δ i x (compT R δ j y z) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | single s r =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
    | single t r' =>
      induction z using Finsupp.induction_linear with
      | zero => simp
      | add z z' hz hz' => simp only [map_add, hz, hz']
      | single w r'' =>
        rw [compT_single, compT_single, Lin.mapL_single, compT_single, compT_single,
          SetOperad.comp_assoc_seq, δ.app_comp, δ.app_comp, SgnData.comp_def, SgnData.comp_def]
        congr 1
        have key := congrArg (σ R) (SgnData.sgn_seq i j (δ.app A s) (δ.app B t) (δ.app D w))
        rw [σ_xor, σ_xor] at key
        linear_combination (r * r' * r'') * key

lemma compT_assoc_par {i k : A} (hik : i ≠ k) (x : S A →₀ R) (q r : Bool) (y : S B →₀ R)
    (z : S D →₀ R) :
    Lin.mapL R (parEquiv hik B D)
        (compT R δ (Sum.inl ⟨k, Ne.symm hik⟩) (compT R δ i x (parT R δ q y)) (parT R δ r z))
      = σ R (q && r) •
          compT R δ (Sum.inl ⟨i, hik⟩) (compT R δ k x (parT R δ r z)) (parT R δ q y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx', smul_add]
  | single s c =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy', smul_add]
    | single t c' =>
      induction z using Finsupp.induction_linear with
      | zero => simp
      | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz', smul_add]
      | single w c'' =>
        rw [parT_single, parT_single]
        by_cases h1 : (δ.app B t).tot = q
        · by_cases h2 : (δ.app D w).tot = r
          · rw [if_pos h1, if_pos h2, compT_single, compT_single, Lin.mapL_single, compT_single,
              compT_single, SetOperad.comp_assoc_par, δ.app_comp, δ.app_comp, SgnData.comp_def,
              SgnData.comp_def, Finsupp.smul_single, smul_eq_mul]
            congr 1
            have key := congrArg (σ R) (SgnData.sgn_par hik (δ.app A s) (δ.app B t) (δ.app D w))
            rw [σ_xor, σ_xor, σ_xor, h1, h2] at key
            linear_combination (c * c' * c'') * key
          · rw [if_neg h2]
            simp
        · rw [if_neg h1]
          simp

variable (R δ) in
/-- **The twisted linearization is a graded operad.** -/
noncomputable instance instGrOperad : GrOperad R (SgnLin R δ) where
  par b := parT R δ b
  par_add x := parT_add x
  par_par b b' x := parT_parT b b' x
  map e := Lin.mapL R e
  map_refl x := SymOperad.map_refl (R := R) (P := Lin R S) x
  map_trans e f x := SymOperad.map_trans (R := R) (P := Lin R S) e f x
  map_par e b x := mapL_parT e b x
  one := Finsupp.single SetOperad.one 1
  par_one := parT_one
  comp i := compT R δ i
  comp_par i p q x y := compT_par i p q x y
  map_comp σ' τ i x y := mapL_compT σ' τ i x y
  comp_one i x := compT_one i x
  one_comp y := one_compT y
  comp_assoc_seq i j x y z := compT_assoc_seq i j x y z
  comp_assoc_par {A B D} _ _ _ _ _ _ i k hik x q r y z hy hz := by
    have h := compT_assoc_par (δ := δ) hik x q r y z
    rw [show parT R δ q y = y from hy, show parT R δ r z = z from hz] at h
    exact h

lemma par_def (b : Bool) (x : SgnLin R δ A) : GrOperad.par (R := R) b x = parT R δ b x := rfl

lemma map_def (e : A ≃ B) (x : SgnLin R δ A) : GrOperad.map (R := R) e x = Lin.mapL R e x := rfl

lemma comp_def (i : A) (x : SgnLin R δ A) (y : SgnLin R δ B) :
    GrOperad.comp (R := R) i x y = compT R δ i x y := rfl

lemma one_def : GrOperad.one (R := R) (P := SgnLin R δ) = Finsupp.single SetOperad.one 1 := rfl

end SgnLin

end SgnLin

/-! ## Morphisms of graded operads -/

/-- **A morphism of graded operads**: linear maps commuting with the parity projections, the
relabellings, the units and the compositions. -/
structure GrOperadHom (R : Type u) [CommRing R]
    (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
    (Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q] where
  /-- The component at a finite input set. -/
  app (A : Type) [Fintype A] [DecidableEq A] : P A →ₗ[R] Q A
  app_par {A : Type} [Fintype A] [DecidableEq A] (b : Bool) (x : P A) :
    app A (GrOperad.par (R := R) b x) = GrOperad.par (R := R) b (app A x)
  app_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    (x : P A) : app B (GrOperad.map (R := R) e x) = GrOperad.map (R := R) e (app A x)
  app_one : app Unit (GrOperad.one (R := R) (P := P)) = GrOperad.one (R := R) (P := Q)
  app_comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (x : P A) (y : P B) :
    app (Without A i ⊕ B) (GrOperad.comp (R := R) i x y)
      = GrOperad.comp (R := R) i (app A x) (app B y)

namespace GrOperadHom

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]

@[ext] lemma ext {φ ψ : GrOperadHom R P Q}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : P A), φ.app A x = ψ.app A x) :
    φ = ψ := by
  obtain ⟨φa, _, _, _, _⟩ := φ
  obtain ⟨ψa, _, _, _, _⟩ := ψ
  have : @φa = @ψa := by
    funext A _ _
    exact LinearMap.ext (h A)
  subst this
  rfl

end GrOperadHom

/-! ## Homogeneous operations with sign data -/

section SgnOp

variable (R : Type u) [CommRing R] (Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]

/-- **Homogeneous operations with sign data**, of the parity of the data; a set operad under the
compositions with the sign of the data (`SgnOp.instSetOperad`). -/
def SgnOp (A : Type) [Fintype A] [DecidableEq A] : Type w :=
  {p : Q A × SgnData A // GrOperad.par (R := R) p.2.tot p.1 = p.1}

namespace SgnOp

variable {R Q}
variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The operation. -/
def op (p : SgnOp R Q A) : Q A := p.1.1

/-- The sign data. -/
def dat (p : SgnOp R Q A) : SgnData A := p.1.2

lemma par_op (p : SgnOp R Q A) : GrOperad.par (R := R) p.dat.tot p.op = p.op := p.2

@[ext] lemma ext {p p' : SgnOp R Q A} (h1 : p.op = p'.op) (h2 : p.dat = p'.dat) : p = p' :=
  Subtype.ext (Prod.ext h1 h2)

/-- A homogeneous operation with sign data. -/
def mk (q : Q A) (d : SgnData A) (h : GrOperad.par (R := R) d.tot q = q) : SgnOp R Q A :=
  ⟨(q, d), h⟩

@[simp] lemma mk_op (q : Q A) (d : SgnData A) (h : GrOperad.par (R := R) d.tot q = q) :
    (mk q d h).op = q := rfl

@[simp] lemma mk_dat (q : Q A) (d : SgnData A) (h : GrOperad.par (R := R) d.tot q = q) :
    (mk q d h).dat = d := rfl

/-- Relabelling. -/
def mapSO (e : A ≃ B) (p : SgnOp R Q A) : SgnOp R Q B :=
  mk (GrOperad.map (R := R) e p.op) (SgnData.map e p.dat) (by
    rw [SgnData.map_tot, ← GrOperad.map_par, p.par_op])

/-- The identity. -/
def oneSO : SgnOp R Q Unit := mk (GrOperad.one (R := R) (P := Q)) SgnData.one GrOperad.par_one

/-- **Composition, with the sign of the data.** -/
noncomputable def compSO (i : A) (p : SgnOp R Q A) (p' : SgnOp R Q B) :
    SgnOp R Q (Without A i ⊕ B) :=
  mk (σ R (SgnData.sgn i p.dat p'.dat) • GrOperad.comp (R := R) i p.op p'.op)
    (SgnData.comp i p.dat p'.dat) (by
      have h := GrOperad.comp_par (R := R) i p.dat.tot p'.dat.tot p.op p'.op
      rw [p.par_op, p'.par_op] at h
      rw [SgnData.comp_tot, map_smul, h])

@[simp] lemma mapSO_op (e : A ≃ B) (p : SgnOp R Q A) :
    (mapSO e p).op = GrOperad.map (R := R) e p.op := rfl

@[simp] lemma mapSO_dat (e : A ≃ B) (p : SgnOp R Q A) : (mapSO e p).dat = SgnData.map e p.dat := rfl

@[simp] lemma compSO_op (i : A) (p : SgnOp R Q A) (p' : SgnOp R Q B) :
    (compSO i p p').op = σ R (SgnData.sgn i p.dat p'.dat) • GrOperad.comp (R := R) i p.op p'.op :=
  rfl

@[simp] lemma compSO_dat (i : A) (p : SgnOp R Q A) (p' : SgnOp R Q B) :
    (compSO i p p').dat = SgnData.comp i p.dat p'.dat := rfl

end SgnOp

open SgnOp in
/-- **Homogeneous operations with sign data form a set operad**: the signs of the data make up for
the Koszul signs of the graded operad. -/
noncomputable instance SgnOp.instSetOperad : SetOperad (SgnOp R Q) where
  map e p := mapSO e p
  map_refl p := SgnOp.ext (GrOperad.map_refl _) (SetOperad.map_refl (S := SgnD) p.dat)
  map_trans e f p :=
    SgnOp.ext (GrOperad.map_trans _ _ _) (SetOperad.map_trans (S := SgnD) e f p.dat)
  one := oneSO
  comp i p p' := compSO i p p'
  map_comp σ' τ i p p' := by
    refine SgnOp.ext ?_ (SetOperad.map_comp (S := SgnD) σ' τ i p.dat p'.dat)
    show GrOperad.map (R := R) (compEquiv σ' τ i) (σ R (SgnData.sgn i p.dat p'.dat) •
        GrOperad.comp (R := R) i p.op p'.op)
      = σ R (SgnData.sgn (σ' i) (SgnData.map σ' p.dat) (SgnData.map τ p'.dat)) •
        GrOperad.comp (R := R) (σ' i) (GrOperad.map (R := R) σ' p.op)
          (GrOperad.map (R := R) τ p'.op)
    rw [map_smul, GrOperad.map_comp, SgnData.sgn_map]
  comp_one i p := by
    refine SgnOp.ext ?_ (SetOperad.comp_one (S := SgnD) i p.dat)
    show GrOperad.map (R := R) (rightUnitEquiv i) (σ R (SgnData.sgn i p.dat SgnData.one) •
        GrOperad.comp (R := R) i p.op (GrOperad.one (R := R) (P := Q))) = p.op
    rw [SgnData.sgn_one_right, σ_false, one_smul, GrOperad.comp_one]
  one_comp p := by
    refine SgnOp.ext ?_ (SetOperad.one_comp (S := SgnD) p.dat)
    show GrOperad.map (R := R) (leftUnitEquiv _) (σ R (SgnData.sgn () SgnData.one p.dat) •
        GrOperad.comp (R := R) () (GrOperad.one (R := R) (P := Q)) p.op) = p.op
    rw [SgnData.sgn_one_left, σ_false, one_smul, GrOperad.one_comp]
  comp_assoc_seq {A B D} _ _ _ _ _ _ i j p p' p'' := by
    refine SgnOp.ext ?_ (SetOperad.comp_assoc_seq (S := SgnD) i j p.dat p'.dat p''.dat)
    show GrOperad.map (R := R) (seqEquiv i j D)
        (σ R (SgnData.sgn (Sum.inr j) (SgnData.comp i p.dat p'.dat) p''.dat) •
          GrOperad.comp (R := R) (Sum.inr j) (σ R (SgnData.sgn i p.dat p'.dat) •
            GrOperad.comp (R := R) i p.op p'.op) p''.op)
      = σ R (SgnData.sgn i p.dat (SgnData.comp j p'.dat p''.dat)) •
          GrOperad.comp (R := R) i p.op (σ R (SgnData.sgn j p'.dat p''.dat) •
            GrOperad.comp (R := R) j p'.op p''.op)
    simp only [map_smul, LinearMap.smul_apply, smul_smul]
    rw [GrOperad.comp_assoc_seq]
    congr 1
    have key := congrArg (σ R) (SgnData.sgn_seq i j p.dat p'.dat p''.dat)
    rw [σ_xor, σ_xor] at key
    linear_combination key
  comp_assoc_par {A B D} _ _ _ _ _ _ i k hik p p' p'' := by
    refine SgnOp.ext ?_ (SetOperad.comp_assoc_par (S := SgnD) hik p.dat p'.dat p''.dat)
    show GrOperad.map (R := R) (parEquiv hik B D)
        (σ R (SgnData.sgn (Sum.inl ⟨k, Ne.symm hik⟩) (SgnData.comp i p.dat p'.dat) p''.dat) •
          GrOperad.comp (R := R) (Sum.inl ⟨k, Ne.symm hik⟩) (σ R (SgnData.sgn i p.dat p'.dat) •
            GrOperad.comp (R := R) i p.op p'.op) p''.op)
      = σ R (SgnData.sgn (Sum.inl ⟨i, hik⟩) (SgnData.comp k p.dat p''.dat) p'.dat) •
          GrOperad.comp (R := R) (Sum.inl ⟨i, hik⟩) (σ R (SgnData.sgn k p.dat p''.dat) •
            GrOperad.comp (R := R) k p.op p''.op) p'.op
    simp only [map_smul, LinearMap.smul_apply, smul_smul]
    rw [GrOperad.comp_assoc_par (R := R) hik p.op p'.par_op p''.par_op, smul_smul]
    congr 1
    have key := congrArg (σ R) (SgnData.sgn_par hik p.dat p'.dat p''.dat)
    rw [σ_xor, σ_xor, σ_xor] at key
    have h2 := σ_mul_self R (p'.dat.tot && p''.dat.tot)
    linear_combination (σ R (p'.dat.tot && p''.dat.tot)) * key
      + (σ R (SgnData.sgn k p.dat p''.dat) * σ R (SgnData.sgn (Sum.inl ⟨i, hik⟩)
        (SgnData.comp k p.dat p''.dat) p'.dat)) * h2

/-- **The sign data of homogeneous operations**, as a morphism of set operads. -/
noncomputable def SgnOp.proj : SetOperadHom (SgnOp R Q) SgnD where
  app _ _ _ p := p.dat
  app_map _ _ := rfl
  app_one := rfl
  app_comp _ _ _ := rfl

end SgnOp

/-! ## Morphisms out of a twisted linearization -/

section TwLinHom

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {R : Type u} [CommRing R] {δ : SetOperadHom S SgnD}
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]

namespace SgnLin

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- A basis element of a twisted linearization. -/
noncomputable def bas (δ : SetOperadHom S SgnD) (R : Type u) [CommRing R] (x : S A) :
    SgnLin R δ A :=
  Finsupp.single x 1

lemma par_bas (x : S A) :
    GrOperad.par (R := R) (δ.app A x).tot (bas δ R x) = bas δ R x :=
  (parT_single _ x 1).trans (if_pos rfl)

lemma map_bas (e : A ≃ B) (x : S A) :
    GrOperad.map (R := R) e (bas δ R x) = bas δ R (SetOperad.map e x) :=
  Lin.mapL_single e x 1

lemma comp_bas (i : A) (x : S A) (y : S B) :
    GrOperad.comp (R := R) i (bas δ R x) (bas δ R y)
      = σ R (SgnData.sgn i (δ.app A x) (δ.app B y)) • bas δ R (SetOperad.comp i x y) := by
  rw [comp_def]
  refine (compT_single i x y 1 1).trans ?_
  rw [mul_one, mul_one]
  exact (Finsupp.smul_single_one _ _).symm

/-- **A morphism out of a twisted linearization, on the basis**: a morphism of set operads into
the homogeneous operations with sign data. -/
noncomputable def toSO (Φ : GrOperadHom R (SgnLin R δ) Q) : SetOperadHom S (SgnOp R Q) where
  app A _ _ x := SgnOp.mk (Φ.app A (bas δ R x)) (δ.app A x) (by rw [← Φ.app_par, par_bas])
  app_map e x := SgnOp.ext (by
      show Φ.app _ (bas δ R (SetOperad.map e x)) = GrOperad.map (R := R) e (Φ.app _ (bas δ R x))
      rw [← Φ.app_map, map_bas]) (δ.app_map e x)
  app_one := SgnOp.ext Φ.app_one δ.app_one
  app_comp i x y := SgnOp.ext (by
      show Φ.app _ (bas δ R (SetOperad.comp i x y))
        = σ R (SgnData.sgn i (δ.app _ x) (δ.app _ y)) •
          GrOperad.comp (R := R) i (Φ.app _ (bas δ R x)) (Φ.app _ (bas δ R y))
      rw [← Φ.app_comp, comp_bas, map_smul, smul_smul, σ_mul_self, one_smul])
    (δ.app_comp i x y)

/-- The linear extension of a morphism into homogeneous operations with sign data. -/
noncomputable def ofSOApp (Ψ : SetOperadHom S (SgnOp R Q)) (A : Type) [Fintype A] [DecidableEq A] :
    (S A →₀ R) →ₗ[R] Q A :=
  Finsupp.lift (Q A) R (S A) fun x => (Ψ.app A x).op

lemma ofSOApp_single (Ψ : SetOperadHom S (SgnOp R Q)) (x : S A) (r : R) :
    ofSOApp Ψ A (Finsupp.single x r) = r • (Ψ.app A x).op := by
  unfold ofSOApp
  rw [Finsupp.lift_apply, Finsupp.sum_single_index (by simp)]

lemma dat_eq {Ψ : SetOperadHom S (SgnOp R Q)} (hΨ : (SgnOp.proj R Q).comp Ψ = δ) (x : S A) :
    (Ψ.app A x).dat = δ.app A x :=
  congrArg (fun φ : SetOperadHom S SgnD => φ.app A x) hΨ

lemma ofSOApp_par {Ψ : SetOperadHom S (SgnOp R Q)} (hΨ : (SgnOp.proj R Q).comp Ψ = δ) (b : Bool)
    (z : S A →₀ R) :
    ofSOApp Ψ A (parT R δ b z) = GrOperad.par (R := R) b (ofSOApp Ψ A z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | single x r =>
    have hx := (Ψ.app A x).par_op
    rw [dat_eq hΨ] at hx
    rw [parT_single, ofSOApp_single, map_smul]
    by_cases h : (δ.app A x).tot = b
    · rw [if_pos h, ofSOApp_single, ← h, hx]
    · rw [if_neg h, map_zero, ← hx, GrOperad.par_par, if_neg (Ne.symm h), smul_zero]

lemma ofSOApp_map (Ψ : SetOperadHom S (SgnOp R Q)) (e : A ≃ B) (z : S A →₀ R) :
    ofSOApp Ψ B (Lin.mapL R e z) = GrOperad.map (R := R) e (ofSOApp Ψ A z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | single x r =>
    rw [Lin.mapL_single, ofSOApp_single, ofSOApp_single, map_smul, Ψ.app_map]
    rfl

lemma ofSOApp_comp {Ψ : SetOperadHom S (SgnOp R Q)} (hΨ : (SgnOp.proj R Q).comp Ψ = δ) (i : A)
    (z : S A →₀ R) (z' : S B →₀ R) :
    ofSOApp Ψ _ (compT R δ i z z')
      = GrOperad.comp (R := R) i (ofSOApp Ψ A z) (ofSOApp Ψ B z') := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z z'' hz hz'' => simp only [map_add, LinearMap.add_apply, hz, hz'']
  | single x r =>
    induction z' using Finsupp.induction_linear with
    | zero => simp
    | add z' z'' hz' hz'' => simp only [map_add, hz', hz'']
    | single y r' =>
      rw [compT_single, ofSOApp_single, ofSOApp_single, ofSOApp_single, Ψ.app_comp]
      show _ • (σ R (SgnData.sgn i (Ψ.app A x).dat (Ψ.app B y).dat) •
        GrOperad.comp (R := R) i (Ψ.app A x).op (Ψ.app B y).op) = _
      rw [dat_eq hΨ, dat_eq hΨ, map_smul, map_smul, LinearMap.smul_apply, smul_smul, smul_smul]
      congr 1
      linear_combination (r * r') * σ_mul_self R (SgnData.sgn i (δ.app A x) (δ.app B y))

/-- **The morphism of graded operads** extending a morphism into the homogeneous operations with
sign data, over the sign data. -/
noncomputable def ofSO (Ψ : SetOperadHom S (SgnOp R Q)) (hΨ : (SgnOp.proj R Q).comp Ψ = δ) :
    GrOperadHom R (SgnLin R δ) Q where
  app A _ _ := ofSOApp Ψ A
  app_par b z := ofSOApp_par hΨ b z
  app_map e z := ofSOApp_map Ψ e z
  app_one := (ofSOApp_single Ψ SetOperad.one 1).trans (by rw [one_smul, Ψ.app_one]; rfl)
  app_comp i z z' := ofSOApp_comp hΨ i z z'

/-- **Morphisms out of a twisted linearization**: a morphism of graded operads `SgnLin R δ → Q` is
a morphism of set operads into the homogeneous operations of `Q` with sign data, over the sign
data `δ`. -/
noncomputable def homEquiv :
    GrOperadHom R (SgnLin R δ) Q
      ≃ {Ψ : SetOperadHom S (SgnOp R Q) // (SgnOp.proj R Q).comp Ψ = δ} where
  toFun Φ := ⟨toSO Φ, SetOperadHom.ext fun _ _ _ _ => rfl⟩
  invFun Ψ := ofSO Ψ.1 Ψ.2
  left_inv Φ := GrOperadHom.ext fun A _ _ z =>
    Lin.induction₁ (S := S) (ofSOApp (toSO Φ) A) (Φ.app A) (fun x => by
      rw [ofSOApp_single, one_smul]
      rfl) z
  right_inv Ψ := Subtype.ext (SetOperadHom.ext fun A _ _ x => SgnOp.ext
    (by
      show ofSOApp Ψ.1 A (Finsupp.single x 1) = _
      rw [ofSOApp_single, one_smul])
    (dat_eq Ψ.2 x).symm)

lemma homEquiv_apply_app (Φ : GrOperadHom R (SgnLin R δ) Q) (x : S A) :
    ((homEquiv Φ).1.app A x).op = Φ.app A (bas δ R x) := rfl

lemma homEquiv_symm_bas (Ψ : {Ψ : SetOperadHom S (SgnOp R Q) // (SgnOp.proj R Q).comp Ψ = δ})
    (x : S A) : (homEquiv.symm Ψ).app A (bas δ R x) = (Ψ.1.app A x).op :=
  (ofSOApp_single Ψ.1 x 1).trans (one_smul R _)

end SgnLin

end TwLinHom

/-! ## The free graded operad -/

namespace Tree

variable {E : ℕ → Type v} (gp : ∀ k, E k → Bool)

@[simp] lemma tparF_leaves : ∀ k : ℕ, Forest.tparF gp (TreeOfArity.leaves (E := E) k) = false
  | 0 => rfl
  | k + 1 => by
    rw [TreeOfArity.leaves, tparF_cons, tparF_leaves k, tpar_leaf]
    rfl

@[simp] lemma tpar_corolla {k : ℕ} (e : E k) :
    tpar gp (TreeOfArity.corolla e).1 = gp k e := by
  show xor (gp k e) (Forest.tparF gp (TreeOfArity.leaves k)) = gp k e
  rw [tparF_leaves, Bool.xor_false]

end Tree

namespace FreeGr

open TreeOfArity

variable {T : ℕ → Type v} (gp : ∀ k, T k → Bool)

/-- The tree of an operation of the regular operad of trees. -/
def treeOf {A : Type} [Fintype A] [DecidableEq A] (x : Reg (TreeOfArity T) A) : Tree T :=
  x.2.1.2.1

lemma treeOf_arity {A : Type} [Fintype A] [DecidableEq A] (x : Reg (TreeOfArity T) A) :
    (treeOf x).arity = x.2.1.1 :=
  x.2.1.2.2

lemma rank_lt_arity {A : Type} [Fintype A] [DecidableEq A] (x : Reg (TreeOfArity T) A) (a : A) :
    x.1.rank a < (treeOf x).arity := by
  rw [treeOf_arity]
  exact Reg.rank_lt x a

lemma treeOf_comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (x : Reg (TreeOfArity T) A) (y : Reg (TreeOfArity T) B) :
    treeOf (SetOperad.comp i x y) = (treeOf x).graft (x.1.rank i) (treeOf y) :=
  arr_comp_tree x.2.1 y.2.1 (Reg.rank_lt x i)

/-- **The sign data of a planar tree with its leaves labelled**: the order of its leaves, the
parity of the vertices after each leaf in the preorder, and the parity of all its vertices. -/
noncomputable def treeSgn : SetOperadHom (Reg (TreeOfArity T)) SgnD where
  app A _ _ x := ⟨x.1, fun a => Tree.apar gp (treeOf x) (x.1.rank a), Tree.tpar gp (treeOf x)⟩
  app_map e x := SgnData.ext rfl (funext fun b => by
    show Tree.apar gp (treeOf x) ((LinOrd.map e x.1).rank b) = Tree.apar gp (treeOf x)
      (x.1.rank (e.symm b))
    rw [LinOrd.rank_map]) rfl
  app_one := rfl
  app_comp {A B} _ _ _ _ i x y := by
    have hi := rank_lt_arity x i
    have hy : Fintype.card B = (treeOf y).arity := by
      rw [treeOf_arity]
      exact y.2.2.symm
    refine SgnData.ext rfl (funext fun u => ?_) ?_
    · show Tree.apar gp (treeOf (SetOperad.comp i x y)) ((LinOrd.comp i x.1 y.1).rank u) = _
      rw [treeOf_comp]
      rcases u with a | b
      · rcases x.1.total a.1 i a.2 with h | h
        · rw [LinOrd.rank_comp_inl_of_lt _ _ _ _ h,
            Tree.apar_graft_before gp _ _ _ _ (x.1.rank_lt_rank h) hi]
          exact (if_pos h).symm
        · have hr := x.1.rank_lt_rank h
          have e : x.1.rank a.1 - 1 + Fintype.card B = x.1.rank a.1 + (treeOf y).arity - 1 := by
            omega
          rw [LinOrd.rank_comp_inl_of_gt _ _ _ _ h, e,
            Tree.apar_graft_after gp _ _ _ _ hr (rank_lt_arity x a.1)]
          exact (if_neg (fun h' => x.1.irrefl _ (x.1.trans _ _ _ h' h))).symm
      · rw [LinOrd.rank_comp_inr, Tree.apar_graft_inner gp _ _ _ _ hi (by
          rw [← hy]
          exact y.1.rank_lt_card b)]
        rfl
    · show Tree.tpar gp (treeOf (SetOperad.comp i x y)) = _
      rw [treeOf_comp, Tree.tpar_graft gp _ _ _ hi]
      rfl

end FreeGr

variable (R : Type u) [CommRing R] {T : ℕ → Type v} (gp : ∀ k, T k → Bool)

/-- **The free graded operad** on generators of any arity with parities `gp`: planar trees with
their leaves labelled by the inputs, composed by grafting, with the Koszul sign of the vertices
the grafted tree moves across. -/
abbrev FreeGr : (A : Type) → [Fintype A] → [DecidableEq A] → Type (max u v) :=
  SgnLin R (FreeGr.treeSgn gp)

namespace FreeGr

open TreeOfArity

variable {R gp}

/-- **A generator**, as the corolla in the standard order. -/
noncomputable def gen {k : ℕ} (e : T k) : FreeGr R gp (Fin k) :=
  SgnLin.bas (treeSgn gp) R (Reg.std (corolla e))

lemma treeSgn_tot {k : ℕ} (e : T k) :
    ((treeSgn gp).app (Fin k) (Reg.std (corolla e))).tot = gp k e :=
  Tree.tpar_corolla gp e

/-- **A generator has the parity of its label.** -/
lemma par_gen {k : ℕ} (e : T k) :
    GrOperad.par (R := R) (gp k e) (gen (R := R) (gp := gp) e) = gen e := by
  rw [← treeSgn_tot (gp := gp) e]
  exact SgnLin.par_bas _

section Hom

variable (R) (Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q] (gp)

/-- **Values on the generators**: an operation of the parity of each generator. -/
abbrev GenVal : Type _ :=
  {f : ∀ k, T k → Q (Fin k) // ∀ k (e : T k), GrOperad.par (R := R) (gp k e) (f k e) = f k e}

variable {R Q gp}

/-- The morphism of set operads into homogeneous operations with sign data defined by values on
the generators. -/
noncomputable def liftSO (f : GenVal R gp Q) : SetOperadHom (Reg (TreeOfArity T)) (SgnOp R Q) :=
  Reg.lift (TreeOfArity.lift (S := SetOperad.toNSSet (SgnOp R Q)) fun k e =>
    SgnOp.mk (f.1 k e) ((treeSgn gp).app (Fin k) (Reg.std (corolla e)))
      (by rw [treeSgn_tot]; exact f.2 k e))

lemma liftSO_std (f : GenVal R gp Q) {k : ℕ} (e : T k) :
    (liftSO f).app (Fin k) (Reg.std (corolla e))
      = SgnOp.mk (f.1 k e) ((treeSgn gp).app (Fin k) (Reg.std (corolla e)))
          (by rw [treeSgn_tot]; exact f.2 k e) := by
  rw [liftSO, Reg.lift_std]
  exact TreeOfArity.lift_corolla (S := SetOperad.toNSSet (SgnOp R Q)) _ e

/-- Morphisms over the sign data of trees are their values on the generators. -/
noncomputable def genEquiv :
    {Ψ : SetOperadHom (Reg (TreeOfArity T)) (SgnOp R Q) // (SgnOp.proj R Q).comp Ψ = treeSgn gp}
      ≃ GenVal R gp Q where
  toFun Ψ := ⟨fun k e => (Ψ.1.app (Fin k) (Reg.std (corolla e))).op, fun k e => by
    have h := (Ψ.1.app (Fin k) (Reg.std (corolla e))).par_op
    rwa [SgnLin.dat_eq Ψ.2, treeSgn_tot] at h⟩
  invFun f := ⟨liftSO f, FreeReg.regHom_ext fun k e => by
    show ((liftSO f).app (Fin k) (Reg.std (corolla e))).dat = _
    rw [liftSO_std]
    rfl⟩
  left_inv Ψ := Subtype.ext (FreeReg.regHom_ext fun k e => by
    rw [liftSO_std]
    exact SgnOp.ext rfl (SgnLin.dat_eq Ψ.2 _).symm)
  right_inv f := Subtype.ext (funext fun k => funext fun e => by
    show ((liftSO f).app (Fin k) (Reg.std (corolla e))).op = f.1 k e
    rw [liftSO_std]
    rfl)

/-- **The universal property of the free graded operad**: a morphism of graded operads out of it
is a choice, for each generator, of an operation of its parity. -/
noncomputable def homEquiv : GrOperadHom R (FreeGr R gp) Q ≃ GenVal R gp Q :=
  SgnLin.homEquiv.trans genEquiv

@[simp] lemma homEquiv_apply (Φ : GrOperadHom R (FreeGr R gp) Q) {k : ℕ} (e : T k) :
    (homEquiv Φ).1 k e = Φ.app (Fin k) (gen e) := rfl

@[simp] lemma homEquiv_symm_gen (f : GenVal R gp Q) {k : ℕ} (e : T k) :
    (homEquiv.symm f).app (Fin k) (gen e) = f.1 k e := by
  rw [← homEquiv_apply, Equiv.apply_symm_apply]

/-- **Morphisms out of the free graded operad agree when they agree on the generators.** -/
theorem hom_ext {Φ Φ' : GrOperadHom R (FreeGr R gp) Q}
    (h : ∀ k (e : T k), Φ.app (Fin k) (gen e) = Φ'.app (Fin k) (gen e)) : Φ = Φ' :=
  homEquiv.injective (Subtype.ext (funext fun k => funext fun e => h k e))

end Hom

end FreeGr

end Operad
