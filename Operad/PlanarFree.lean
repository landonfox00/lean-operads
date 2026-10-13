/-
# The free operad on generators of any arity: planar trees and their symmetrization

**Planar trees** with vertices of arity `k` labelled by `E k` (`Operad.Tree`), composed by grafting
a tree onto a leaf, form a non-symmetric set operad (`TreeOfArity.instNSSetOperad`), and it is the
free one on `E` (`TreeOfArity.homEquiv`): a morphism out of it is an operation of arity `k` for each
generator of arity `k`, and the value of a tree is the composite of the operations along it
(`TreeOfArity.evalArr`, filling the inputs of the root generator with the values of the subtrees,
from left to right: `TreeOfArity.fillF`).

By the symmetrization adjunction (`Reg.homEquiv`), **the free symmetric set operad on generators of
any arity is the regular operad of planar trees**: an operation with inputs `A` is a planar tree
together with a linear order on `A` labelling its leaves, `FreeSet T ≅ Reg (TreeOfArity T)`
(`FreeReg.regIso`). So the free operad in modules `Lin R (FreeSet T)` has, in every arity, a basis
indexed by these pairs (`FreeReg.basis`).

This generalizes `Operad.FreeBinary`, the case of binary generators.
-/
import Operad.Free
import Operad.Regular
import Operad.FreeBinary

universe u v w x

namespace Operad

open NSSetOperad Sym

namespace TreeOfArity

variable {E : ℕ → Type v}

lemma reindexS_val {m n : ℕ} (h : m = n) (t : TreeOfArity E m) :
    (reindexS (TreeOfArity E) h t).1 = t.1 := by
  subst h
  rfl

/-- **Planar trees form a non-symmetric set operad** under grafting. -/
instance instNSSetOperad : NSSetOperad (TreeOfArity E) where
  one := one
  comp a b _ t s := graft a b t s
  comp_one_right a b α := Subtype.ext (Tree.graft_leaf_right α.1 a)
  comp_one_left α := Subtype.ext (by rw [reindexS_val]; rfl)
  comp_assoc_seq a b c d p α β γ := Subtype.ext (by
    rw [reindexS_val]
    simp only [graft_val, reindexS_val]
    exact Tree.graft_graft_seq α.1 a β.1 c γ.1 (by rw [α.2]; omega) (by rw [β.2]; omega))
  comp_assoc_par a b c n p α β γ := Subtype.ext (by
    rw [reindexS_val]
    simp only [graft_val, reindexS_val]
    have h := Tree.graft_graft_par α.1 a β.1 (a + 1 + b) γ.1 (by omega) (by rw [α.2]; omega)
    rw [β.2, show a + 1 + b - 1 + n = a + n + b by omega] at h
    exact h)

@[simp] lemma one_val : (NSSetOperad.one : TreeOfArity E 1).1 = .leaf := rfl

@[simp] lemma comp_val (a b : ℕ) {n : ℕ} (t : TreeOfArity E (a + 1 + b)) (s : TreeOfArity E n) :
    (NSSetOperad.comp a b t s).1 = t.1.graft a s.1 := rfl

/-- A tree, as an operation of the planar operad of trees. -/
def toArr (t : Tree E) : Arr (TreeOfArity E) := ⟨t.arity, ⟨t, rfl⟩⟩

/-- Operations of the planar operad of trees are determined by their trees. -/
lemma arr_ext {X Y : Arr (TreeOfArity E)} (h : X.2.1 = Y.2.1) : X = Y := by
  obtain ⟨n, t, rfl⟩ := X
  obtain ⟨m, t', rfl⟩ := Y
  simp only at h
  subst h
  rfl

lemma toArr_comp (t : Tree E) (i : ℕ) (s : Tree E) (h : i < t.arity) :
    (toArr t).comp i (toArr s) = toArr (t.graft i s) := by
  obtain ⟨b, x, hx⟩ := Arr.exists_mk (toArr t) h
  refine arr_ext ?_
  rw [hx, Arr.mk_comp]
  show (x.1.graft i s) = t.graft i s
  have : x.1 = t := by
    have := congrArg (fun X : Arr (TreeOfArity E) => X.2.1) hx
    exact this.symm
  rw [this]

/-- The forest of `k` leaves. -/
def leaves : (k : ℕ) → Forest E k
  | 0 => .nil
  | k + 1 => .cons .leaf (leaves k)

@[simp] lemma arityF_leaves : ∀ k : ℕ, (leaves (E := E) k).arityF = k
  | 0 => rfl
  | k + 1 => by
    simp only [leaves, Tree.arityF_cons, Tree.arity_leaf, arityF_leaves k]
    omega

/-- **The corolla of a generator.** -/
def corolla {k : ℕ} (e : E k) : TreeOfArity E k :=
  ⟨.node e (leaves k), by simp⟩

end TreeOfArity

/-! ## Values of trees -/

namespace TreeOfArity

section Eval

variable {E : ℕ → Type v} {S : ℕ → Type w} [NSSetOperad S] (f : ∀ k, E k → S k)

mutual

/-- **The value of a tree**: the composite of the generators along it. -/
def evalArr : Tree E → Arr S
  | .leaf => Arr.one
  | .node e fo => fillF (⟨_, f _ e⟩ : Arr S) 0 fo

/-- **Fill the inputs** `p, p + 1, …` of `X` with the values of the trees of a forest, from left to
right. -/
def fillF : {k : ℕ} → Arr S → ℕ → Forest E k → Arr S
  | _, X, _, .nil => X
  | _, X, p, .cons t fo => fillF (X.comp p (evalArr t)) (p + t.arity) fo

end

mutual

lemma evalArr_fst : ∀ t : Tree E, (evalArr f t).1 = t.arity
  | .leaf => rfl
  | .node e fo => by
    rw [evalArr, fillF_fst fo (⟨_, f _ e⟩ : Arr S) 0 (by simp)]
    simp

lemma fillF_fst : ∀ {k : ℕ} (fo : Forest E k) (X : Arr S) (p : ℕ), p + k ≤ X.1 →
    (fillF f X p fo).1 = X.1 - k + fo.arityF
  | _, .nil, X, p, _ => by simp [fillF]
  | k + 1, .cons t fo, X, p, h => by
    have hp : p < X.1 := by omega
    have h1 : (X.comp p (evalArr f t)).1 = X.1 + t.arity - 1 := by
      rw [Arr.comp_fst hp, evalArr_fst t]
    rw [fillF, fillF_fst fo _ (p + t.arity) (by rw [h1]; omega), h1, Tree.arityF_cons]
    omega

end

/-- **Composing at an earlier input commutes with filling later ones.** -/
lemma fillF_comp_left : ∀ {k : ℕ} (fo : Forest E k) (X Y : Arr S) (a p : ℕ), a < p →
    p + k ≤ X.1 → fillF f (X.comp a Y) (p + Y.1 - 1) fo = (fillF f X p fo).comp a Y
  | _, .nil, _, _, _, _, _, _ => rfl
  | k + 1, .cons t fo, X, Y, a, p, hap, h => by
    have hp : p < X.1 := by omega
    have h1 : (X.comp p (evalArr f t)).1 = X.1 + t.arity - 1 := by
      rw [Arr.comp_fst hp, evalArr_fst f t]
    rw [fillF, fillF, Arr.comp_comp_disjoint Y (evalArr f t) hap hp,
      show p + Y.1 - 1 + t.arity = p + t.arity + Y.1 - 1 by omega,
      fillF_comp_left fo _ Y a (p + t.arity) (by omega) (by rw [h1]; omega)]

mutual

/-- **The value of a graft is the composite of the values.** -/
theorem evalArr_graft : ∀ (t : Tree E) (i : ℕ) (s : Tree E), i < t.arity →
    evalArr f (t.graft i s) = (evalArr f t).comp i (evalArr f s)
  | .leaf, i, s, h => by
    obtain rfl : i = 0 := by simp only [Tree.arity_leaf] at h; omega
    rw [Tree.graft_leaf, evalArr]
    exact (Arr.one_comp _).symm
  | .node e fo, i, s, h => by
    rw [Tree.graft_node, evalArr, evalArr,
      fillF_graftF fo (⟨_, f _ e⟩ : Arr S) 0 i s (by simpa using h) (by simp), zero_add]

/-- The forest half of `evalArr_graft`. -/
theorem fillF_graftF : ∀ {k : ℕ} (fo : Forest E k) (X : Arr S) (p i : ℕ) (s : Tree E),
    i < fo.arityF → p + k ≤ X.1 →
    fillF f X p (fo.graftF i s) = (fillF f X p fo).comp (p + i) (evalArr f s)
  | _, .nil, _, _, _, _, h, _ => by simp at h
  | k + 1, .cons t fo, X, p, i, s, h, hX => by
    simp only [Tree.arityF_cons] at h
    have hp : p < X.1 := by omega
    by_cases hi : i < t.arity
    · rw [Tree.graftF_cons_of_lt s hi, fillF, fillF, evalArr_graft t i s hi,
        ← Arr.comp_comp_nested (evalArr f s) hp (by rw [evalArr_fst f t]; exact hi),
        Tree.arity_graft t i s hi, ← evalArr_fst f s,
        show p + (t.arity - 1 + (evalArr f s).1) = p + t.arity + (evalArr f s).1 - 1 by omega,
        fillF_comp_left f fo _ (evalArr f s) (p + i) (p + t.arity) (by omega)
          (by rw [Arr.comp_fst hp, evalArr_fst f t]; omega)]
    · rw [Tree.graftF_cons_of_ge s (by omega), fillF, fillF,
        fillF_graftF fo _ (p + t.arity) (i - t.arity) s (by omega)
          (by rw [Arr.comp_fst hp, evalArr_fst f t]; omega),
        show p + t.arity + (i - t.arity) = p + i by omega]

end

/-- Filling inputs with leaves changes nothing. -/
lemma fillF_leaves : ∀ (k : ℕ) (X : Arr S) (p : ℕ), p + k ≤ X.1 → fillF f X p (leaves k) = X
  | 0, _, _, _ => rfl
  | k + 1, X, p, h => by
    rw [leaves, fillF, show evalArr f (Tree.leaf : Tree E) = Arr.one from rfl,
      Arr.comp_one (by omega), Tree.arity_leaf, fillF_leaves k X (p + 1) (by omega)]

mutual

/-- **Morphisms commute with values.** -/
lemma map_evalArr {T : ℕ → Type x} [NSSetOperad T] (φ : NSSetOperadHom S T) :
    ∀ t : Tree E, Arr.map φ (evalArr f t) = evalArr (fun k e => φ.app k (f k e)) t
  | .leaf => by rw [evalArr, Arr.map_one]; rfl
  | .node e fo => by
    rw [evalArr, evalArr]
    exact map_fillF φ fo _ 0

/-- The forest half of `map_evalArr`. -/
lemma map_fillF {T : ℕ → Type x} [NSSetOperad T] (φ : NSSetOperadHom S T) :
    ∀ {k : ℕ} (fo : Forest E k) (X : Arr S) (p : ℕ),
      Arr.map φ (fillF f X p fo) = fillF (fun k e => φ.app k (f k e)) (Arr.map φ X) p fo
  | _, .nil, _, _ => rfl
  | _, .cons t fo, X, p => by
    rw [fillF, fillF, map_fillF φ fo, Arr.map_comp, map_evalArr φ t]

end


end Eval

end TreeOfArity

/-! ## The free planar operad -/

namespace TreeOfArity

variable {E : ℕ → Type v}

/-- **Graft the trees of a forest** at the leaves `p, p + 1, …` of the trees of a forest, from left
to right. -/
def graftAll {m : ℕ} : {k : ℕ} → Forest E m → ℕ → Forest E k → Forest E m
  | _, F, _, .nil => F
  | _, F, p, .cons t fo => graftAll (F.graftF p t) (p + t.arity) fo

lemma graftAll_cons_ge {m : ℕ} (t : Tree E) (G : Forest E m) (q : ℕ) :
    ∀ {k : ℕ} (fo : Forest E k),
      graftAll (Forest.cons t G) (t.arity + q) fo = Forest.cons t (graftAll G q fo)
  | _, .nil => rfl
  | _, .cons s fo => by
    rw [graftAll, graftAll, Tree.graftF_cons_of_ge s (by omega),
      show t.arity + q - t.arity = q by omega, show t.arity + q + s.arity = t.arity + (q + s.arity)
        by omega, graftAll_cons_ge t _ (q + s.arity) fo]

lemma graftAll_leaves : ∀ {k : ℕ} (fo : Forest E k), graftAll (leaves k) 0 fo = fo
  | _, .nil => rfl
  | _, .cons t fo => by
    rw [graftAll, leaves, Tree.graftF_cons_of_lt t (by simp), Tree.graft_leaf, zero_add,
      ← add_zero t.arity, graftAll_cons_ge t _ 0 fo, graftAll_leaves fo]

mutual

/-- **A tree is the value of its corollas** in the planar operad of trees. -/
theorem evalArr_corolla : ∀ t : Tree E, evalArr (fun _ e => corolla e) t = toArr t
  | .leaf => rfl
  | .node e fo => by
    rw [evalArr, show (⟨_, corolla e⟩ : Arr (TreeOfArity E)) = toArr (.node e (leaves _)) from
      arr_ext rfl, fillF_corolla fo e (leaves _) 0 (by simp), graftAll_leaves]

/-- The forest half of `evalArr_corolla`. -/
theorem fillF_corolla : ∀ {k : ℕ} (fo : Forest E k) {m : ℕ} (e : E m) (F : Forest E m) (p : ℕ),
    p + k ≤ F.arityF →
    fillF (fun _ e => corolla e) (toArr (.node e F)) p fo = toArr (.node e (graftAll F p fo))
  | _, .nil, _, _, _, _, _ => rfl
  | k + 1, .cons t fo, m, e, F, p, h => by
    rw [fillF, evalArr_corolla t, toArr_comp _ p t (by simp; omega), Tree.graft_node]
    exact fillF_corolla fo e (F.graftF p t) (p + t.arity)
      (by rw [Forest.arityF_graftF F p t (by omega)]; omega)

end

variable {S : ℕ → Type w} [NSSetOperad S]

/-- **The morphism defined by operations** `f k e`, one for each generator. -/
def lift (f : ∀ k, E k → S k) : NSSetOperadHom (TreeOfArity E) S where
  app n t := reindexS S ((evalArr_fst f t.1).trans t.2) (evalArr f t.1).2
  app_one := rfl
  app_comp a b n α β := by
    apply Arr.mk_eq_mk_iff.1
    rw [Arr.mk_reindexS, ← Arr.mk_comp, Arr.mk_reindexS, Arr.mk_reindexS]
    exact evalArr_graft f α.1 a β.1 (by rw [α.2]; omega)

lemma lift_mk (f : ∀ k, E k → S k) (t : Tree E) :
    Arr.map (lift f) (toArr t) = evalArr f t := by
  unfold toArr lift
  rw [Arr.map_mk]
  exact Arr.mk_reindexS _ _

@[simp] lemma lift_corolla (f : ∀ k, E k → S k) {k : ℕ} (e : E k) :
    (lift f).app k (corolla e) = f k e := by
  apply Arr.mk_eq_mk_iff.1
  rw [← Arr.map_mk, show (⟨k, corolla e⟩ : Arr (TreeOfArity E)) = toArr (.node e (leaves k)) from
    arr_ext rfl, lift_mk, evalArr, fillF_leaves f k _ 0 (by simp)]

/-- A morphism out of the planar operad of trees is its values on the corollas, composed. -/
lemma map_toArr (φ : NSSetOperadHom (TreeOfArity E) S) (t : Tree E) :
    Arr.map φ (toArr t) = evalArr (fun k e => φ.app k (corolla e)) t := by
  rw [← evalArr_corolla t, map_evalArr]

/-- **Morphisms out of the planar operad of trees are determined by the corollas.** -/
theorem hom_ext {φ ψ : NSSetOperadHom (TreeOfArity E) S}
    (h : ∀ k (e : E k), φ.app k (corolla e) = ψ.app k (corolla e)) : φ = ψ := by
  ext n t
  obtain ⟨t, rfl⟩ := t
  have := map_toArr φ t
  rw [show (fun k e => φ.app k (corolla e)) = fun k e => ψ.app k (corolla e) from
    funext fun k => funext (h k), ← map_toArr ψ t] at this
  exact Arr.mk_eq_mk_iff.1 this

/-- **The planar trees are the free non-symmetric set operad** on generators of any arity. -/
def homEquiv : NSSetOperadHom (TreeOfArity E) S ≃ (∀ k, E k → S k) where
  toFun φ k e := φ.app k (corolla e)
  invFun := lift
  left_inv _ := hom_ext fun _ e => lift_corolla _ e
  right_inv f := funext fun _ => funext fun e => lift_corolla f e

end TreeOfArity

/-! ## The free symmetric operad on generators of any arity -/

namespace FreeReg

variable {T : ℕ → Type v}

open TreeOfArity

/-- **Morphisms out of the regular operad of trees are determined by the corollas.** -/
theorem regHom_ext {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type w} [SetOperad S]
    {G G' : SetOperadHom (Reg (TreeOfArity T)) S}
    (h : ∀ k (e : T k),
      G.app (Fin k) (Reg.std (corolla e)) = G'.app (Fin k) (Reg.std (corolla e))) :
    G = G' :=
  Reg.hom_ext fun n x => by
    have := TreeOfArity.hom_ext (φ := (SetOperadHom.toNSSet G).comp Reg.eta)
      (ψ := (SetOperadHom.toNSSet G').comp Reg.eta) h
    exact congrArg (fun φ => NSSetOperadHom.app φ n x) this

/-- The generators, as corollas. -/
noncomputable def toReg : SetOperadHom (FreeSet T) (Reg (TreeOfArity T)) :=
  FreeSet.homEquiv.symm fun _ e => Reg.std (corolla e)

/-- Trees, as composites of the generators. -/
noncomputable def ofReg : SetOperadHom (Reg (TreeOfArity T)) (FreeSet T) :=
  Reg.lift (TreeOfArity.lift (S := SetOperad.toNSSet (FreeSet T))
    fun _ e => (Pres.gen e : FreeSet T (Fin _)))

lemma toReg_gen {k : ℕ} (e : T k) : toReg.app (Fin k) (Pres.gen e) = Reg.std (corolla e) := rfl

lemma ofReg_std {k : ℕ} (e : T k) :
    ofReg.app (Fin k) (Reg.std (corolla e)) = (Pres.gen e : FreeSet T (Fin k)) := by
  rw [ofReg, Reg.lift_std]
  exact TreeOfArity.lift_corolla (S := SetOperad.toNSSet (FreeSet T)) _ e

/-- **The free symmetric set operad on generators of any arity is the regular operad of planar
trees**: an operation with inputs `A` is a planar tree with its leaves labelled by a linear order of
`A`. -/
noncomputable def regIso : SetOperadIso (FreeSet T) (Reg (TreeOfArity T)) where
  hom := toReg
  inv := ofReg
  hom_inv_id := Pres.hom_ext fun _ e => by
    show ofReg.app _ (toReg.app _ (Pres.gen e)) = Pres.gen e
    rw [toReg_gen, ofReg_std]
  inv_hom_id := regHom_ext fun _ e => by
    show toReg.app _ (ofReg.app _ (Reg.std (corolla e))) = Reg.std (corolla e)
    rw [ofReg_std, toReg_gen]

end FreeReg

namespace FreeReg

open TreeOfArity

variable (R : Type u) [CommRing R] (T : ℕ → Type v)

/-- **A basis of the free operad on generators of any arity**, in every arity: the planar trees
with their leaves labelled by a linear order of the inputs. -/
noncomputable def basis (A : Type) [Fintype A] [DecidableEq A] :
    Module.Basis (Reg (TreeOfArity T) A) R (Lin R (FreeSet T) A) :=
  Finsupp.basisSingleOne.reindex (regIso.equiv A)

instance (A : Type) [Fintype A] [DecidableEq A] : Module.Free R (Lin R (FreeSet T) A) :=
  Module.Free.of_basis (basis R T A)

/-- **The dimension of the free operad**: in arity `n`, `n!` times the number of planar trees with
`n` leaves and vertices labelled by the generators. -/
theorem finrank_eq [Nontrivial R] (A : Type) [Fintype A] [DecidableEq A]
    [Finite (TreeOfArity T (Fintype.card A))] :
    Module.finrank R (Lin R (FreeSet T) A)
      = (Fintype.card A).factorial * Nat.card (TreeOfArity T (Fintype.card A)) := by
  haveI : Finite (Reg (TreeOfArity T) A) := by
    unfold Reg
    haveI : Finite {X : Arr (TreeOfArity T) // X.1 = Fintype.card A} :=
      Finite.of_equiv _ (FreeBin.arrEquiv (TreeOfArity T) (Fintype.card A)).symm
    infer_instance
  haveI := Fintype.ofFinite (Reg (TreeOfArity T) A)
  rw [Module.finrank_eq_nat_card_basis (basis R T A), FreeBin.card_reg]

end FreeReg

end Operad
