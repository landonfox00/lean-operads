/-
# Transporting partitions along a bijection

The substitution product of species is indexed by partitions: `(F ∘ G)(S)` is a sum over the
partitions of `S`, of `F` applied to the set of blocks tensored with `G` applied to each block.
For that sum to be functorial in `S`, partitions have to be transported along bijections, and
that transport has to respect identities and composition.

This file builds exactly that indexing layer. Mathlib's `Finpartition.map` transports along an
*order* isomorphism, so the work is to turn a bijection of finite types into an order isomorphism
of their `Finset` lattices, and then to check the two functor laws.
-/
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Finset.Image

universe u v

namespace Operad

open Finset

variable {α : Type u} {β : Type v} {γ : Type*}

/-- A bijection of types induces an order isomorphism of their lattices of finite subsets. -/
def finsetOrderIso (e : α ≃ β) : Finset α ≃o Finset β where
  toEquiv := e.finsetCongr
  map_rel_iff' := by
    intro s t
    simp only [Equiv.finsetCongr_apply]
    exact Finset.map_subset_map

@[simp] lemma finsetOrderIso_apply (e : α ≃ β) (s : Finset α) :
    finsetOrderIso e s = s.map e.toEmbedding := rfl

variable [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]

lemma map_univ_equiv (e : α ≃ β) : (univ : Finset α).map e.toEmbedding = univ := by
  ext b
  simp only [Finset.mem_map, Finset.mem_univ, true_and, iff_true]
  exact ⟨e.symm b, by simp⟩

/-- Transport a partition of `univ` along a bijection. -/
def partMap (e : α ≃ β) (P : Finpartition (univ : Finset α)) :
    Finpartition (univ : Finset β) :=
  (P.map (finsetOrderIso e)).copy (by rw [finsetOrderIso_apply, map_univ_equiv])

@[simp] lemma partMap_parts (e : α ≃ β) (P : Finpartition (univ : Finset α)) :
    (partMap e P).parts = P.parts.map (finsetOrderIso e).toEquiv.toEmbedding := rfl

lemma finsetOrderIso_toEquiv (e : α ≃ β) : (finsetOrderIso e).toEquiv = e.finsetCongr := rfl

/-- Transport along the identity is the identity. -/
@[simp] lemma partMap_refl (P : Finpartition (univ : Finset α)) :
    partMap (Equiv.refl α) P = P := by
  apply Finpartition.ext
  rw [partMap_parts, finsetOrderIso_toEquiv, Equiv.finsetCongr_refl]
  simp

/-- Transport respects composition. -/
lemma partMap_trans (e : α ≃ β) (f : β ≃ γ) (P : Finpartition (univ : Finset α)) :
    partMap (e.trans f) P = partMap f (partMap e P) := by
  apply Finpartition.ext
  simp only [partMap_parts, finsetOrderIso_toEquiv, Finset.map_map]
  refine congrArg (fun g => P.parts.map g) ?_
  refine Function.Embedding.ext fun s => ?_
  ext x
  simp [Equiv.finsetCongr_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro h
    exact ⟨e.symm (f.symm x), h, by simp⟩

end Operad
