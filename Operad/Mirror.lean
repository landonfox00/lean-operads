/-
# Mirror images of planar binary trees

Reversing the order of the inputs of a planar binary tree while relabelling its vertices along a
map `f` of generators (`BTree.mirror`) preserves the arity (`BTree.arity_mirror`), and for an
involution `f` it is an involution (`BTree.mirror_mirror`), so it permutes the trees of each arity
(`BTree.OfArity.mirrorEquiv`). On the named trees of `Operad.LowWeight` it exchanges left and right
combs in arity three (`OfArity.mirror_lc`, `OfArity.mirror_rc`) and permutes the five shapes of
arity four (`OfArity.mirror_ll`, …). For the planar operad of a presentation whose generators come
with a reversal, this is the reversal involution of the free non-symmetric operad.
-/
import Operad.LowWeight

universe v

namespace Operad

namespace BTree

variable {E : Type v}

/-- **The mirror image** of a planar binary tree, its vertices relabelled along `f`. -/
def mirror (f : E → E) : BTree E → BTree E
  | leaf => leaf
  | node e l r => node (f e) (mirror f r) (mirror f l)

@[simp] lemma mirror_leaf (f : E → E) : mirror f (leaf : BTree E) = leaf := rfl

@[simp] lemma mirror_node (f : E → E) (e : E) (l r : BTree E) :
    mirror f (node e l r) = node (f e) (mirror f r) (mirror f l) := rfl

/-- The mirror image has the same number of leaves. -/
lemma arity_mirror (f : E → E) : ∀ t : BTree E, (mirror f t).arity = t.arity
  | leaf => rfl
  | node e l r => by
    rw [mirror_node, arity_node, arity_node, arity_mirror f l, arity_mirror f r, Nat.add_comm]

/-- Mirroring along an involution is an involution. -/
lemma mirror_mirror {f : E → E} (hf : Function.Involutive f) :
    ∀ t : BTree E, mirror f (mirror f t) = t
  | leaf => rfl
  | node e l r => by rw [mirror_node, mirror_node, mirror_mirror hf l, mirror_mirror hf r, hf e]

namespace OfArity

/-- **The mirror image** of a tree of arity `n`. -/
def mirror (f : E → E) {n : ℕ} (t : OfArity E n) : OfArity E n :=
  ⟨BTree.mirror f t.1, (BTree.arity_mirror f t.1).trans t.2⟩

lemma mirror_mirror {f : E → E} (hf : Function.Involutive f) {n : ℕ} (t : OfArity E n) :
    mirror f (mirror f t) = t :=
  Subtype.ext (BTree.mirror_mirror hf t.1)

/-- **Mirroring along an involution permutes the trees of each arity.** -/
def mirrorEquiv {f : E → E} (hf : Function.Involutive f) (n : ℕ) : OfArity E n ≃ OfArity E n where
  toFun := mirror f
  invFun := mirror f
  left_inv := mirror_mirror hf
  right_inv := mirror_mirror hf

@[simp] lemma mirrorEquiv_apply {f : E → E} (hf : Function.Involutive f) {n : ℕ}
    (t : OfArity E n) : mirrorEquiv hf n t = mirror f t := rfl

@[simp] lemma mirror_cor (f : E → E) (e : E) : mirror f (cor e) = cor (f e) := rfl

@[simp] lemma mirror_lc (f : E → E) (e e' : E) : mirror f (lc e e') = rc (f e) (f e') := rfl

@[simp] lemma mirror_rc (f : E → E) (e e' : E) : mirror f (rc e e') = lc (f e) (f e') := rfl

@[simp] lemma mirror_ll (f : E → E) (e₁ e₂ e₃ : E) :
    mirror f (ll e₁ e₂ e₃) = rr (f e₁) (f e₂) (f e₃) := rfl

@[simp] lemma mirror_lr (f : E → E) (e₁ e₂ e₃ : E) :
    mirror f (lr e₁ e₂ e₃) = rl (f e₁) (f e₂) (f e₃) := rfl

@[simp] lemma mirror_bl (f : E → E) (e₁ e₂ e₃ : E) :
    mirror f (bl e₁ e₂ e₃) = bl (f e₁) (f e₃) (f e₂) := rfl

@[simp] lemma mirror_rl (f : E → E) (e₁ e₂ e₃ : E) :
    mirror f (rl e₁ e₂ e₃) = lr (f e₁) (f e₂) (f e₃) := rfl

@[simp] lemma mirror_rr (f : E → E) (e₁ e₂ e₃ : E) :
    mirror f (rr e₁ e₂ e₃) = ll (f e₁) (f e₂) (f e₃) := rfl

end OfArity

end BTree

end Operad
