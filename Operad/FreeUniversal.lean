/-
# The universal property of the free operad

`Operad.TotalComp` evaluates a tree in an arbitrary operad `Q` and shows that a corolla evaluates
to its generator. What is missing for the universal property is that evaluation respects
grafting, which is precisely the condition making it a morphism of operads.

Everything here is written **positionally**: an operation with a distinguished slot has arity
`a + 1 + b`. That is the form the operad axioms are stated in, and the form `NSOperadHom.app_comp`
wants, so working in it avoids a layer of `compFin`'s internal reindexing.

The load-bearing lemma is `substF_comp`: substituting a forest into the trailing slots commutes
with grafting at an *earlier* slot. It is stated for an arbitrary inserted element rather than for
an `extend`-image, which makes it a plain induction on the forest rather than part of the mutual
recursion, and it is exactly one application of the parallel associativity axiom per cons.
-/
import Operad.TotalComp
import Operad.Free

universe u v w

namespace Operad

open NSOperad

variable {R : Type u} [CommRing R] {E : ℕ → Type w}
  {Q : ℕ → Type v} [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)] [NSOperad R Q]

/-- Substituting a forest into the trailing `k` slots commutes with grafting `δ` at the earlier
slot `p`. One application of `comp_assoc_par` per tree in the forest.

The offsets `c` and `e` are parameters constrained by equations rather than written out, so that
the induction hypothesis can be instantiated at `c + t.arity` without its syntactic form having
to match what `substF`'s own recursion produces. -/
lemma substF_comp (f : ∀ k, E k → Q k) :
    ∀ {k : ℕ} (fo : Forest E k) (p q d c e g : ℕ) (hc : c = p + d + q) (he : e = p + 1 + q)
      (hg : g = q + fo.arityF)
      (h3 : p + d + g = c + fo.arityF) (h4 : e + fo.arityF = p + 1 + g)
      (β : Q (e + k)) (δ : Q d),
      substF (R := R) f c
          (reindex R Q (show p + d + (q + k) = c + k by omega)
            (comp (R := R) p (q + k)
              (reindex R Q (show e + k = p + 1 + (q + k) by omega) β) δ)) fo
        = reindex R Q h3
            (comp (R := R) p g
              (reindex R Q h4 (substF (R := R) f e β fo)) δ)
  | _, .nil, p, q, d, c, e, g, hc, he, hg, h3, h4, β, δ => by
      simp only [Tree.arityF_nil] at hg
      subst hg
      simp only [substF]
      rfl
  | _, @Forest.cons _ k' t fo, p, q, d, c, e, g, hc, he, hg, h3, h4, β, δ => by
      subst hc
      subst he
      rw [Tree.arityF_cons] at hg
      simp only [substF, Tree.arityF_cons, reindex_reindex]
      have hax := comp_assoc_par (R := R) p q k'
        (reindex R Q (show p + 1 + q + (k' + 1) = p + 1 + q + 1 + k' by omega) β) δ
        (extend (R := R) f t)
      have hbridge := comp_index_congr (R := R) (P := Q) p
        (show q + 1 + k' = q + (k' + 1) by omega)
        (reindex R Q (show p + 1 + q + (k' + 1) = p + 1 + (q + 1 + k') by omega) β) δ
      simp only [reindex_reindex] at hbridge hax
      rw [hbridge]
      simp only [reindex_reindex]
      have hkey : (comp (R := R) (p + d + q) k'
            (reindex R Q (show p + d + (q + 1 + k') = p + d + q + 1 + k' by omega)
              (comp (R := R) p (q + 1 + k')
                (reindex R Q (show p + 1 + q + (k' + 1) = p + 1 + (q + 1 + k') by omega) β) δ))
            (extend (R := R) f t))
          = reindex R Q (show p + d + (q + t.arity + k') = p + d + q + t.arity + k' by omega)
              (comp (R := R) p (q + t.arity + k')
                (reindex R Q (show p + 1 + q + t.arity + k' = p + 1 + (q + t.arity + k') by omega)
                  (comp (R := R) (p + 1 + q) k'
                    (reindex R Q (show p + 1 + q + (k' + 1) = p + 1 + q + 1 + k' by omega) β)
                    (extend (R := R) f t))) δ) := by
        rw [← hax, reindex_reindex, reindex_self]
      rw [hkey]
      rw [substF_comp f fo p (q + t.arity) d (p + d + q + t.arity) (p + 1 + q + t.arity) g
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (comp (R := R) (p + 1 + q) k'
          (reindex R Q (show p + 1 + q + (k' + 1) = p + 1 + q + 1 + k' by omega) β)
          (extend (R := R) f t)) δ]
      set X := substF (R := R) f (p + 1 + q + t.arity)
        (comp (R := R) (p + 1 + q) k'
          (reindex R Q (show p + 1 + q + (k' + 1) = p + 1 + q + 1 + k' by omega) β)
          (extend (R := R) f t)) fo with hX
      clear_value X
      clear hX
      refine (reindex_reindex (R := R) (P := Q) _ _ _).trans ?_
      congr 1
      congr 1
      congr 1
      exact (reindex_reindex (R := R) (P := Q) _ _ _).symm

/-! ### Evaluation respects grafting

The mutual induction. The forest half splits on whether the grafted slot lies in the head tree
(where the tree half applies, then `comp_assoc_seq` turns "graft into the operation just inserted"
into "graft after inserting", and `substF_comp` carries the rest of the forest past it) or further
along (where only the forest half recurses). -/

mutual

/-- **Evaluation is compatible with grafting** — the operad-morphism condition. -/
theorem extend_graft (f : ∀ k, E k → Q k) :
    ∀ (t : Tree E) (a b : ℕ) (s : Tree E) (hab : t.arity = a + 1 + b)
      (h2 : a + (Tree.arity s) + b = (t.graft a s).arity),
      extend (R := R) f (t.graft a s)
        = reindex R Q h2
            (comp (R := R) a b (reindex R Q hab (extend (R := R) f t)) (extend (R := R) f s))
  | .leaf, a, b, s, hab, h2 => by
      simp only [Tree.arity_leaf] at hab
      obtain rfl : a = 0 := by omega
      obtain rfl : b = 0 := by omega
      simp only [Tree.graft_leaf, extend_leaf]
      exact (comp_one_left (extend (R := R) f s)).symm
  | .node (k := k) e fo, a, b, s, hab, h2 => by
      simp only [Tree.arity_node] at hab
      simp only [Tree.graft_node, Tree.arity_node] at h2
      simp only [Tree.graft_node, extend]
      rw [substF_graftF f fo 0 a b a s
        (reindex R Q (show k = 0 + k by omega) (f k e)) (fo.graftF a s) rfl hab
        (by omega) (by omega) (by omega)]
      refine (reindex_reindex (R := R) (P := Q) _ _ _).trans ?_
      congr 1
      congr 1
      congr 1
      exact (reindex_reindex (R := R) (P := Q) _ _ _).symm

/-- The forest half of `extend_graft`. -/
theorem substF_graftF (f : ∀ k, E k → Q k) :
    ∀ {k : ℕ} (fo : Forest E k) (c a b w : ℕ) (s : Tree E) (α : Q (c + k))
      (fo' : Forest E k) (hfo' : fo' = fo.graftF a s)
      (hab : fo.arityF = a + 1 + b) (hw : w = c + a)
      (h1 : c + fo.arityF = w + 1 + b)
      (h2 : w + (Tree.arity s) + b = c + fo'.arityF),
      substF (R := R) f c α fo'
        = reindex R Q h2
            (comp (R := R) w b (reindex R Q h1 (substF (R := R) f c α fo)) (extend (R := R) f s))
  | _, .nil, c, a, b, w, s, α, fo', hfo', hab, hw, h1, h2 => by
      simp only [Tree.arityF_nil] at hab; omega
  | _, @Forest.cons _ k' t fo, c, a, b, w, s, α, fo', hfo', hab, hw, h1, h2 => by
      simp only [Tree.arityF_cons] at hab
      subst hw
      by_cases hlt : a < t.arity
      · rw [Tree.graftF_cons_of_lt s hlt] at hfo'
        subst hfo'
        have harg := Tree.arity_graft t a s hlt
        simp only [substF, Tree.arityF_cons] at h2 ⊢
        rw [extend_graft f t a (t.arity - a - 1) s (by omega) (by omega)]
        rw [comp_arity_congr (R := R) (P := Q) c k'
          (show a + (Tree.arity s) + (t.arity - a - 1) = (t.graft a s).arity by omega)]
        rw [← comp_assoc_seq (R := R) (P := Q) c k' a (t.arity - a - 1)]
        rw [comp_arity_congr (R := R) (P := Q) c k'
          (show t.arity = a + 1 + (t.arity - a - 1) by omega)]
        simp only [reindex_reindex]
        rw [substF_comp (R := R) f fo (c + a) (t.arity - a - 1) (Tree.arity s)
          (c + (t.graft a s).arity) (c + t.arity) b
          (by omega) (by omega) (by omega) (by omega) (by omega)
          (comp (R := R) c k' (reindex R Q (show c + (k' + 1) = c + 1 + k' by omega) α)
            (extend (R := R) f t)) (extend (R := R) f s)]
        refine (reindex_reindex (R := R) (P := Q) _ _ _).trans ?_
        congr 1
        congr 1
        congr 1
        exact (reindex_reindex (R := R) (P := Q) _ _ _).symm
      · rw [Tree.graftF_cons_of_ge s (by omega)] at hfo'
        subst hfo'
        simp only [substF, Tree.arityF_cons] at h2 ⊢
        rw [substF_graftF f fo (c + t.arity) (a - t.arity) b (c + a) s
          (comp (R := R) c k' (reindex R Q (show c + (k' + 1) = c + 1 + k' by omega) α)
            (extend (R := R) f t))
          (fo.graftF (a - t.arity) s) rfl
          (by omega) (by omega) (by omega) (by omega)]
        refine (reindex_reindex (R := R) (P := Q) _ _ _).trans ?_
        congr 1
        congr 1
        congr 1
        exact (reindex_reindex (R := R) (P := Q) _ _ _).symm

end

/-! ### The universal property

`extend` evaluates a tree; extending it linearly over the basis of trees gives a morphism of
operads out of `Free R E`. `app_one` is `extend_corolla` at the bare leaf and `app_comp` is
`extend_graft`, so the two theorems above are exactly the two morphism laws. -/

/-- Evaluation, extended linearly over the basis of trees. -/
noncomputable def extendApp (f : ∀ k, E k → Q k) (n : ℕ) : Free R E n →ₗ[R] Q n :=
  Finsupp.lsum R fun t =>
    LinearMap.toSpanSingleton R (Q n) (reindex R Q t.property (extend (R := R) f t.val))

@[simp] lemma extendApp_gen (f : ∀ k, E k → Q k) {n : ℕ} (t : TreeOfArity E n) :
    extendApp (R := R) f n (Free.gen t) = reindex R Q t.property (extend (R := R) f t.val) := by
  simp only [extendApp, Free.gen, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply_one]

lemma extendApp_single (f : ∀ k, E k → Q k) {n : ℕ} (t : TreeOfArity E n) (r : R) :
    extendApp (R := R) f n (Finsupp.single t r)
      = r • reindex R Q t.property (extend (R := R) f t.val) := by
  rw [← Free.smul_gen, map_smul, extendApp_gen]

/-- **The universal property of the free operad, existence half.** A map of generators extends to
a morphism of operads out of `Free R E`. -/
noncomputable def extendHom (f : ∀ k, E k → Q k) : NSOperadHom R (Free R E) Q where
  app := extendApp (R := R) f
  app_one := by
    show extendApp (R := R) f 1 (Free.gen TreeOfArity.one) = _
    rw [extendApp_gen]
    exact reindex_self _ _
  app_comp := by
    intro a b n α β
    induction α using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
    | single t r =>
      induction β using Finsupp.induction_linear with
      | zero => simp
      | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
      | single s r' =>
        show extendApp (R := R) f (a + n + b) (Free.compL a b _ _) = _
        rw [Free.compL_single, extendApp_single, extendApp_single, extendApp_single]
        have ht := t.property
        have hs := s.property
        have harg := Tree.arity_graft t.val a s.val (by omega)
        simp only [TreeOfArity.graft_val]
        rw [map_smul, map_smul, LinearMap.smul_apply, smul_smul, mul_comm r' r]
        congr 1
        rw [comp_arity_congr (R := R) (P := Q) a b hs]
        rw [extend_graft f t.val a b s.val ht (by omega)]
        exact (reindex_reindex (R := R) (P := Q) _ _ _).trans rfl

/-- **The extension restricts to `f` on generators.** Together with `extendHom`, this is the
existence half of the universal property: every map of generators is realised by a morphism of
operads out of `Free R E`. -/
@[simp] theorem extendHom_corolla (f : ∀ k, E k → Q k) {k : ℕ} (e : E k) :
    (extendHom (R := R) f).app k (Free.gen ⟨corolla e, arity_corolla e⟩) = f k e := by
  show extendApp (R := R) f k (Free.gen ⟨corolla e, arity_corolla e⟩) = _
  rw [extendApp_gen, extend_corolla]
  exact reindex_reindex _ _ _ |>.trans (reindex_self _ _)

/-! ### Morphisms commute with evaluation

Evaluating a tree and then applying a morphism is the same as evaluating with the transported
generators. Unlike `extend_graft` this needs no associativity axiom at all — only the three
morphism laws — so it is a short mutual induction. -/

mutual

/-- A morphism of operads commutes with evaluation of trees. -/
theorem app_extend {S : ℕ → Type v} [∀ n, AddCommGroup (S n)] [∀ n, Module R (S n)]
    [NSOperad R S] (φ : NSOperadHom R Q S) (g : ∀ k, E k → Q k) :
    ∀ (t : Tree E),
      φ.app t.arity (extend (R := R) g t) = extend (R := R) (fun k e => φ.app k (g k e)) t
  | .leaf => φ.app_one
  | .node (k := k) e fo => by
      simp only [extend]
      rw [NSOperadHom.app_reindex, app_substF φ g 0
        (reindex R Q (show k = 0 + k by omega) (g k e)) fo, NSOperadHom.app_reindex]

/-- The forest half: a morphism commutes with substituting a forest. -/
theorem app_substF {S : ℕ → Type v} [∀ n, AddCommGroup (S n)] [∀ n, Module R (S n)]
    [NSOperad R S] (φ : NSOperadHom R Q S) (g : ∀ k, E k → Q k) :
    ∀ {k : ℕ} (c : ℕ) (α : Q (c + k)) (fo : Forest E k),
      φ.app (c + fo.arityF) (substF (R := R) g c α fo)
        = substF (R := R) (fun k e => φ.app k (g k e)) c (φ.app (c + k) α) fo
  | _, c, α, .nil => rfl
  | _, c, α, .cons t fo => by
      simp only [substF]
      rw [NSOperadHom.app_reindex, app_substF φ g (c + t.arity) _ fo, φ.app_comp,
        NSOperadHom.app_reindex, app_extend φ g t]

end

/-! ### Trees are the image of their own generators

`extend`, applied in the free operad itself with the canonical choice of generators, returns the
basis element of the tree it started from. This is the statement that every tree is built from
corollas by iterated composition, and it is what turns "agrees on generators" into "agrees".

`substTree` is the tree-level counterpart of `substF`: it grafts the trees of a forest into the
last `k` leaves of a tree, one at a time, exactly as `substF` does with `comp`. -/

/-- A generator, viewed inside the free operad as its corolla. -/
noncomputable def genOf {k : ℕ} (e : E k) : Free R E k :=
  Free.gen ⟨corolla e, arity_corolla e⟩

lemma genOf_def {k : ℕ} (e : E k) :
    genOf (R := R) e = Free.gen ⟨corolla e, arity_corolla e⟩ := rfl

/-- Graft the trees of a forest into the last `k` leaves of a tree. -/
def substTree : ∀ {k : ℕ}, Tree E → ℕ → Forest E k → Tree E
  | _, T, _, .nil => T
  | _, T, c, .cons t fo => substTree (T.graft c t) (c + t.arity) fo

lemma arity_substTree : ∀ {k : ℕ} (T : Tree E) (c : ℕ) (fo : Forest E k), T.arity = c + k →
    (substTree T c fo).arity = c + fo.arityF
  | _, T, c, .nil, h => by simpa [substTree] using h
  | _, T, c, .cons t fo, h => by
      have hlt : c < T.arity := by omega
      rw [substTree, arity_substTree (T.graft c t) (c + t.arity) fo
        (by rw [Tree.arity_graft T c t hlt]; omega), Tree.arityF_cons]
      omega

end Operad
