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

end Operad
