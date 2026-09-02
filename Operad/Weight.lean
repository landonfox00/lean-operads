/-
# The weight grading on the free operad

The weight of a tree is its number of internal vertices, and `Tree.weight_graft` says grafting
adds weights. Transported to `Free R E` this is the grading Koszul duality runs on: a presentation
is *quadratic* when its relations live in weight two, and the Koszul complex is built weight by
weight.

The statement that matters is `Free.comp_mem_weightSpan`: operadic composition of something of
weight `w₁` with something of weight `w₂` has weight `w₁ + w₂`. Note the contrast with arity,
which composition changes in a way depending on where the composition happens; weight does not
care about the slot at all.
-/
import Operad.Free
import Operad.TotalComp

universe u v

namespace Operad

open NSOperad

variable {R : Type u} [CommRing R] {E : ℕ → Type v}

/-- The weight of a tree of specified arity. -/
def TreeOfArity.weight {n : ℕ} (t : TreeOfArity E n) : ℕ := t.val.weight

@[simp] lemma TreeOfArity.weight_def {n : ℕ} (t : TreeOfArity E n) :
    t.weight = t.val.weight := rfl

/-- **Grafting adds weights**, at the level of arity-indexed trees. -/
@[simp] lemma TreeOfArity.graft_weight (a b : ℕ) {n : ℕ} (t : TreeOfArity E (a + 1 + b))
    (s : TreeOfArity E n) :
    (TreeOfArity.graft a b t s).weight = t.weight + s.weight := by
  have ht := t.property
  exact Tree.weight_graft t.val a s.val (by omega)

/-- The submodule of `Free R E n` spanned by the trees of weight `w`. -/
noncomputable def Free.weightSpan (R : Type u) [CommRing R] (E : ℕ → Type v) (n w : ℕ) :
    Submodule R (Free R E n) :=
  Submodule.span R {x | ∃ t : TreeOfArity E n, t.weight = w ∧ Free.gen (R := R) t = x}

lemma Free.gen_mem_weightSpan {n : ℕ} (t : TreeOfArity E n) :
    Free.gen (R := R) t ∈ Free.weightSpan R E n t.weight :=
  Submodule.subset_span ⟨t, rfl, rfl⟩

/-- **Composition adds weights.** -/
theorem Free.comp_mem_weightSpan (a b : ℕ) {n w₁ w₂ : ℕ}
    {α : Free R E (a + 1 + b)} (hα : α ∈ Free.weightSpan R E (a + 1 + b) w₁)
    {β : Free R E n} (hβ : β ∈ Free.weightSpan R E n w₂) :
    comp (R := R) (P := Free R E) a b α β ∈ Free.weightSpan R E (a + n + b) (w₁ + w₂) := by
  induction hα using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨t, ht, rfl⟩ := hx
      induction hβ using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨s, hs, rfl⟩ := hy
          have : comp (R := R) (P := Free R E) a b (Free.gen t) (Free.gen s)
              = Free.gen (TreeOfArity.graft a b t s) := Free.compL_gen a b t s
          rw [this, ← ht, ← hs, ← TreeOfArity.graft_weight a b t s]
          exact Free.gen_mem_weightSpan _
      | zero => simp
      | add y z _ _ ihy ihz => simpa [map_add] using Submodule.add_mem _ ihy ihz
      | smul r y _ ihy => simpa [map_smul] using Submodule.smul_mem _ r ihy
  | zero => simp
  | add x y _ _ ihx ihy => simpa [map_add] using Submodule.add_mem _ ihx ihy
  | smul r x _ ihx => simpa [map_smul] using Submodule.smul_mem _ r ihx

/-- Reindexing preserves weight. -/
lemma Free.reindex_mem_weightSpan {m n w : ℕ} (h : m = n) {x : Free R E m}
    (hx : x ∈ Free.weightSpan R E m w) :
    reindex R (Free R E) h x ∈ Free.weightSpan R E n w := by
  subst h
  simpa using hx

/-- Composition at a `Fin`-indexed slot adds weights. -/
lemma Free.compFin_mem_weightSpan {m n w₁ w₂ : ℕ} (i : Fin m)
    {α : Free R E m} (hα : α ∈ Free.weightSpan R E m w₁)
    {β : Free R E n} (hβ : β ∈ Free.weightSpan R E n w₂) :
    compFin (R := R) i α β ∈ Free.weightSpan R E (m - 1 + n) (w₁ + w₂) := by
  unfold compFin
  exact Free.reindex_mem_weightSpan _
    (Free.comp_mem_weightSpan _ _ (Free.reindex_mem_weightSpan _ hα) hβ)

end Operad
