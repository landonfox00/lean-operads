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
      trace_state
      sorry

end Operad
