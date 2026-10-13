/-
# The free operad on binary generators: planar trees and their symmetrization

**Planar binary trees** with vertices labelled by `E`, composed by grafting a tree onto a leaf,
form a non-symmetric set operad (`BTree.OfArity.instNSSetOperad`), and it is the free one on `E`
(`BTree.OfArity.homEquiv`): a morphism out of it is a binary operation for each generator, and the
value of a tree is the composite of the operations along it (`BTree.evalArr`).

By the symmetrization adjunction (`Reg.homEquiv`), **the free symmetric set operad on binary
generators is the regular operad of planar trees**: an operation with inputs `A` is a planar tree
together with a linear order on `A` labelling its leaves, `FreeSet (BinGen E) ≅ Reg (OfArity E)`
(`FreeBin.regIso`). So the free operad in modules `FreeBin R G` has, in every arity, a basis
indexed by these pairs (`FreeBin.basis`).
-/
import Operad.BinaryTree
import Operad.Regular
import Operad.BinaryQuadratic

universe u v w

namespace Operad

open NSSetOperad Sym

namespace BTree

namespace OfArity

variable {E : Type v}

lemma reindexS_val {m n : ℕ} (h : m = n) (t : OfArity E m) :
    (reindexS (OfArity E) h t).1 = t.1 := by
  subst h
  rfl

/-- **Planar binary trees form a non-symmetric set operad** under grafting. -/
instance instNSSetOperad : NSSetOperad (OfArity E) where
  one := one
  comp a b _ t s := graft a b t s
  comp_one_right a b α := Subtype.ext (BTree.graft_leaf_right α.1 a)
  comp_one_left α := Subtype.ext (by rw [reindexS_val]; rfl)
  comp_assoc_seq a b c d p α β γ := Subtype.ext (by
    rw [reindexS_val]
    simp only [graft_val, reindexS_val]
    exact BTree.graft_graft_seq α.1 a β.1 c γ.1 (by rw [α.2]; omega) (by rw [β.2]; omega))
  comp_assoc_par a b c n p α β γ := Subtype.ext (by
    rw [reindexS_val]
    simp only [graft_val, reindexS_val]
    have h := BTree.graft_graft_par α.1 a β.1 (a + 1 + b) γ.1 (by omega) (by rw [α.2]; omega)
    rw [β.2, show a + 1 + b - 1 + n = a + n + b by omega] at h
    exact h)

@[simp] lemma one_val : (NSSetOperad.one : OfArity E 1).1 = .leaf := rfl

@[simp] lemma comp_val (a b : ℕ) {n : ℕ} (t : OfArity E (a + 1 + b)) (s : OfArity E n) :
    (NSSetOperad.comp a b t s).1 = t.1.graft a s.1 := rfl

/-- A tree, as an operation of the planar operad of trees. -/
def toArr (t : BTree E) : Arr (OfArity E) := ⟨t.arity, ⟨t, rfl⟩⟩

lemma toArr_leaf : toArr (.leaf : BTree E) = Arr.one := rfl

/-- Operations of the planar operad of trees are determined by their trees. -/
lemma arr_ext {X Y : Arr (OfArity E)} (h : X.2.1 = Y.2.1) : X = Y := by
  obtain ⟨n, t, rfl⟩ := X
  obtain ⟨m, t', rfl⟩ := Y
  simp only at h
  subst h
  rfl

/-- **A tree is its root generator filled with its two subtrees.** -/
lemma toArr_node (e : E) (l r : BTree E) :
    toArr (.node e l r) = Arr.bin (corolla e) (toArr l) (toArr r) := by
  have h1 : Arr.comp (⟨1 + 1 + 0, corolla e⟩ : Arr (OfArity E)) 1 ⟨r.arity, ⟨r, rfl⟩⟩
      = ⟨0 + 1 + r.arity, ⟨.node e .leaf r, by simp only [arity_node, arity_leaf]⟩⟩ := by
    rw [Arr.mk_comp]
    exact arr_ext rfl
  have h2 : Arr.comp (⟨0 + 1 + r.arity, ⟨.node e .leaf r, by
      simp only [arity_node, arity_leaf]⟩⟩ : Arr (OfArity E)) 0 ⟨l.arity, ⟨l, rfl⟩⟩
      = toArr (.node e l r) := by
    rw [Arr.mk_comp]
    exact arr_ext rfl
  show _ = Arr.comp (Arr.comp ⟨1 + 1 + 0, corolla e⟩ 1 ⟨r.arity, ⟨r, rfl⟩⟩) 0
    ⟨l.arity, ⟨l, rfl⟩⟩
  rw [h1, h2]

end OfArity

/-! ## The free planar operad -/

section Eval

variable {E : Type v} {S : ℕ → Type w} [NSSetOperad S] (f : E → S 2)

/-- **The value of a tree**: the composite of the generators along it. -/
def evalArr : BTree E → Arr S
  | .leaf => Arr.one
  | .node e l r => Arr.bin (f e) (evalArr l) (evalArr r)

lemma evalArr_fst : ∀ t : BTree E, (evalArr f t).1 = t.arity
  | .leaf => rfl
  | .node e l r => by
    simp only [evalArr, Arr.bin_fst, evalArr_fst l, evalArr_fst r, arity_node]

/-- **The value of a graft is the composite of the values.** -/
theorem evalArr_graft : ∀ (t : BTree E) (i : ℕ) (s : BTree E), i < t.arity →
    evalArr f (t.graft i s) = (evalArr f t).comp i (evalArr f s)
  | .leaf, i, s, h => by
    obtain rfl : i = 0 := by simp only [arity_leaf] at h; omega
    simp only [graft_leaf, evalArr]
    exact (Arr.one_comp _).symm
  | .node e l r, i, s, h => by
    simp only [arity_node] at h
    by_cases hi : i < l.arity
    · rw [graft_node_of_lt r s hi]
      simp only [evalArr]
      rw [evalArr_graft l i s hi, Arr.comp_bin_left _ _ _ _ (by rw [evalArr_fst]; exact hi)]
    · rw [graft_node_of_ge l s (by omega)]
      simp only [evalArr]
      rw [evalArr_graft r (i - l.arity) s (by omega),
        Arr.comp_bin_right (c := i - l.arity) _ _ _ _ (by rw [evalArr_fst]; omega)
          (by rw [evalArr_fst]; omega)]

end Eval

namespace OfArity

variable {E : Type v} {S : ℕ → Type w} [NSSetOperad S]

/-- **The morphism defined by binary operations** `f e`, one for each generator. -/
def lift (f : E → S 2) : NSSetOperadHom (OfArity E) S where
  app n t := reindexS S ((evalArr_fst f t.1).trans t.2) (evalArr f t.1).2
  app_one := rfl
  app_comp a b n α β := by
    apply Arr.mk_eq_mk_iff.1
    rw [Arr.mk_reindexS, ← Arr.mk_comp, Arr.mk_reindexS, Arr.mk_reindexS]
    exact evalArr_graft f α.1 a β.1 (by rw [α.2]; omega)

lemma lift_mk (f : E → S 2) (t : BTree E) :
    Arr.map (lift f) (toArr t) = evalArr f t := by
  unfold toArr lift
  rw [Arr.map_mk]
  exact Arr.mk_reindexS _ _

@[simp] lemma lift_corolla (f : E → S 2) (e : E) : (lift f).app 2 (corolla e) = f e := by
  apply Arr.mk_eq_mk_iff.1
  rw [← Arr.map_mk, show (⟨2, corolla e⟩ : Arr (OfArity E)) = toArr (.node e .leaf .leaf) from rfl,
    lift_mk]
  exact Arr.bin_one_one (f e)

/-- A morphism out of the planar operad of trees is its values on the corollas, composed. -/
lemma map_toArr (φ : NSSetOperadHom (OfArity E) S) :
    ∀ t : BTree E, Arr.map φ (toArr t) = evalArr (fun e => φ.app 2 (corolla e)) t
  | .leaf => by rw [toArr_leaf, Arr.map_one]; rfl
  | .node e l r => by
    rw [toArr_node, Arr.map_bin, map_toArr φ l, map_toArr φ r]
    rfl

/-- **Morphisms out of the planar operad of trees are determined by the corollas.** -/
theorem hom_ext {φ ψ : NSSetOperadHom (OfArity E) S}
    (h : ∀ e, φ.app 2 (corolla e) = ψ.app 2 (corolla e)) : φ = ψ := by
  ext n t
  obtain ⟨t, rfl⟩ := t
  have := map_toArr φ t
  rw [show (fun e => φ.app 2 (corolla e)) = fun e => ψ.app 2 (corolla e) from funext h,
    ← map_toArr ψ t] at this
  exact Arr.mk_eq_mk_iff.1 this

/-- **The planar binary trees are the free non-symmetric set operad** on binary generators. -/
def homEquiv : NSSetOperadHom (OfArity E) S ≃ (E → S 2) where
  toFun φ e := φ.app 2 (corolla e)
  invFun := lift
  left_inv _ := hom_ext fun e => lift_corolla _ e
  right_inv f := funext fun e => lift_corolla f e

end OfArity

end BTree

/-! ## The free symmetric operad on binary generators -/

namespace FreeBin

variable {E : Type v}

open BTree.OfArity

/-- **Morphisms out of the regular operad of trees are determined by the corollas.** -/
theorem regHom_ext {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type w} [SetOperad S]
    {G G' : SetOperadHom (Reg (BTree.OfArity E)) S}
    (h : ∀ e, G.app (Fin 2) (Reg.std (corolla e)) = G'.app (Fin 2) (Reg.std (corolla e))) :
    G = G' :=
  Reg.hom_ext fun n x => by
    have := BTree.OfArity.hom_ext (φ := (SetOperadHom.toNSSet G).comp Reg.eta)
      (ψ := (SetOperadHom.toNSSet G').comp Reg.eta) h
    exact congrArg (fun φ => NSSetOperadHom.app φ n x) this

/-- The generators, as trees. -/
noncomputable def toReg : SetOperadHom (FreeSet (BinGen E)) (Reg (BTree.OfArity E)) :=
  FreeSet.homEquiv.symm fun _ g => match g with | .op e => Reg.std (corolla e)

/-- Trees, as composites of the generators. -/
noncomputable def ofReg : SetOperadHom (Reg (BTree.OfArity E)) (FreeSet (BinGen E)) :=
  Reg.lift (BTree.OfArity.lift (S := SetOperad.toNSSet (FreeSet (BinGen E)))
    fun e => (Pres.gen (.op e) : FreeSet (BinGen E) (Fin 2)))

lemma toReg_gen (e : E) : toReg.app (Fin 2) (Pres.gen (.op e)) = Reg.std (corolla e) := rfl

lemma ofReg_std (e : E) :
    ofReg.app (Fin 2) (Reg.std (corolla e)) = (Pres.gen (.op e) : FreeSet (BinGen E) (Fin 2)) := by
  rw [ofReg, Reg.lift_std]
  exact BTree.OfArity.lift_corolla (S := SetOperad.toNSSet (FreeSet (BinGen E))) _ e

/-- **The free symmetric set operad on binary generators is the regular operad of planar binary
trees**: an operation with inputs `A` is a planar tree with its leaves labelled by a linear order
of `A`. -/
noncomputable def regIso : SetOperadIso (FreeSet (BinGen E)) (Reg (BTree.OfArity E)) where
  hom := toReg
  inv := ofReg
  hom_inv_id := Pres.hom_ext fun n g => by
    cases g with
    | op e =>
      show ofReg.app (Fin 2) (toReg.app (Fin 2) (Pres.gen (.op e))) = Pres.gen (.op e)
      rw [toReg_gen, ofReg_std]
  inv_hom_id := regHom_ext fun e => by
    show toReg.app (Fin 2) (ofReg.app (Fin 2) (Reg.std (corolla e))) = Reg.std (corolla e)
    rw [ofReg_std, toReg_gen]

variable (R : Type u) [CommRing R] (G : Type v)

/-- **A basis of the free operad on binary generators**, in every arity: the planar binary trees
with their leaves labelled by a linear order of the inputs. -/
noncomputable def basis (A : Type) [Fintype A] [DecidableEq A] :
    Module.Basis (Reg (BTree.OfArity G) A) R (FreeBin R G A) :=
  Finsupp.basisSingleOne.reindex (regIso.equiv A)

lemma basis_apply (A : Type) [Fintype A] [DecidableEq A] (x : Reg (BTree.OfArity G) A) :
    basis R G A x = Finsupp.single (ofReg.app A x) 1 := by
  simp [basis, SetOperadIso.equiv, regIso]

instance (A : Type) [Fintype A] [DecidableEq A] : Module.Free R (FreeBin R G A) :=
  Module.Free.of_basis (basis R G A)

/-- The operations of a given arity of a planar operad, packaged with their arity. -/
def arrEquiv (N : ℕ → Type v) (n : ℕ) : {X : Arr N // X.1 = n} ≃ N n where
  toFun X := X.2 ▸ X.1.2
  invFun x := ⟨⟨n, x⟩, rfl⟩
  left_inv X := by
    obtain ⟨⟨m, x⟩, rfl⟩ := X
    rfl
  right_inv _ := rfl

/-- **The operations of a regular operad** with `n` inputs: `n!` orders, times the planar
operations of arity `n`. -/
lemma card_reg (N : ℕ → Type v) (A : Type) [Fintype A] [DecidableEq A] :
    Nat.card (Reg N A) = (Fintype.card A).factorial * Nat.card (N (Fintype.card A)) := by
  rw [show Nat.card (Reg N A) = Nat.card (LinOrd A × {X : Arr N // X.1 = Fintype.card A}) from rfl,
    Nat.card_prod, LinOrd.card, Nat.card_congr (arrEquiv N _)]

/-- **The dimension of the free operad on binary generators**: in arity `n`, `n!` times the
number of planar binary trees with `n` leaves and vertices labelled by `G`. -/
theorem finrank_eq [Fintype G] [DecidableEq G] [Nontrivial R] (A : Type) [Fintype A]
    [DecidableEq A] :
    Module.finrank R (FreeBin R G A)
      = (Fintype.card A).factorial * Fintype.card (BTree.OfArity G (Fintype.card A)) := by
  rw [Module.finrank_eq_nat_card_basis (basis R G A), card_reg, Nat.card_eq_fintype_card]

end FreeBin

end Operad
