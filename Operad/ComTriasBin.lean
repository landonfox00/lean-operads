/-
# `ComTrias` is the binary quadratic operad `BinComTrias`

Vallette's operad of commutative trialgebras `ComTrias R = Lin R NonemptySubset`
(`Operad.ComTriasPres`) is isomorphic to the binary quadratic operad `BinComTrias R`
(`Operad.PostLie`): its generators `⊥` and `⊣` go to the full subset of two inputs and to the
first input (`BinComTrias.isoComTrias`). So `ComTrias^! ≅ PostLie` is about Vallette's operad
(`BinComTrias.dualIso`, `Operad.PostLie`).

* **The values of the monomials** under a morphism out of the free operad on binary generators
  are the expected composites (`FreeBin.linHom_bin2`, `FreeBin.linHom_binL`, `FreeBin.linHom_binR`).
* **The relators of `ComTrias` vanish under such a morphism exactly when its generator values
  satisfy the relations of commutative trialgebras** (`BinComTrias.dataOfKills`,
  `BinComTrias.kills_of_data`); the two universal properties then give inverse morphisms
  (`BinComTrias.toComTrias`, `BinComTrias.ofComTrias`).
-/
import Operad.PostLie
import Operad.ComTriasPres

universe u v w

namespace Operad

open Sym SetOperad FreeBin

namespace FreeBin

variable {R : Type u} [CommRing R] {G : Type v}
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]

/-- **The value of the morphism out of the free operad** on the basis element of an expression. -/
lemma linHom_single_mk (f : ∀ n, BinGen G n → Q (Fin n)) {A : Type} [Fintype A] [DecidableEq A]
    (x : Syn (BinGen G) A) :
    (FreeSet.linHom R f).app A (Finsupp.single (Pres.mk x) 1)
      = (Und.of R Q).symm (Syn.eval (fun n g => Und.of R Q (f n g)) x) := by
  show Finsupp.lift (Q A) R (FreeSet (BinGen G) A) _ (Finsupp.single (Pres.mk x) 1) = _
  simp
  rfl

lemma linHom_bin2 (f : ∀ n, BinGen G n → Q (Fin n)) (g : G) (σ : Equiv.Perm (Fin 2)) :
    (FreeSet.linHom R f).app _ (bin2 g σ) = SymOperad.map (R := R) σ (f 2 (.op g)) := by
  rw [bin2, linHom_single_mk]
  rfl

lemma linHom_binL (f : ∀ n, BinGen G n → Q (Fin n)) (g h : G) (σ : Equiv.Perm (Fin 3)) :
    (FreeSet.linHom R f).app _ (binL g h σ) = (Und.of R Q).symm
      (SetOperad.map (fin3Left.symm.trans σ) (SetOperad.bin (Und.of R Q (f 2 (.op g)))
        (SetOperad.bin (Und.of R Q (f 2 (.op h))) SetOperad.one SetOperad.one) SetOperad.one)) := by
  rw [binL, linHom_single_mk]
  rfl

lemma linHom_binR (f : ∀ n, BinGen G n → Q (Fin n)) (g h : G) (σ : Equiv.Perm (Fin 3)) :
    (FreeSet.linHom R f).app _ (binR g h σ) = (Und.of R Q).symm
      (SetOperad.map (fin3Right.symm.trans σ) (SetOperad.bin (Und.of R Q (f 2 (.op g)))
        SetOperad.one (SetOperad.bin (Und.of R Q (f 2 (.op h))) SetOperad.one SetOperad.one))) := by
  rw [binR, linHom_single_mk]
  rfl

end FreeBin

namespace BinComTrias

variable {R : Type u} [CommRing R]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]

/-- The generator values given by two operations of arity two. -/
def vals (m l : Q (Fin 2)) : ∀ n, BinGen ComTriOp n → Q (Fin n)
  | _, .op .mid => m
  | _, .op .left => l

section Moves

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type*} [SetOperad S]

lemma map_trans_one {B : Type} [Fintype B] [DecidableEq B] (e : B ≃ Fin 3) (x : S B) :
    SetOperad.map (e.trans (1 : Equiv.Perm (Fin 3))) x = SetOperad.map e x := rfl

lemma map_left_eq_right_iff (X : S ((Unit ⊕ Unit) ⊕ Unit)) (Y : S (Unit ⊕ (Unit ⊕ Unit))) :
    SetOperad.map fin3Left.symm X = SetOperad.map fin3Right.symm Y
      ↔ SetOperad.map (Equiv.sumAssoc Unit Unit Unit) X = Y := by
  have key : (Equiv.sumAssoc Unit Unit Unit).trans fin3Right.symm = fin3Left.symm := by
    ext c
    rcases c with (⟨⟩ | ⟨⟩) | ⟨⟩ <;> rfl
  rw [← key, SetOperad.map_trans]
  exact (SetOperad.map_injective _).eq_iff.trans eq_comm |>.trans eq_comm

lemma map_right_inj (Y Y' : S (Unit ⊕ (Unit ⊕ Unit))) :
    SetOperad.map fin3Right.symm Y = SetOperad.map fin3Right.symm Y' ↔ Y = Y' :=
  (SetOperad.map_injective _).eq_iff

lemma right_perm_eq :
    fin3Right.symm.trans (perm3 0 2 1)
      = (Equiv.sumCongr (Equiv.refl Unit) (Equiv.sumComm Unit Unit)).trans fin3Right.symm := by
  ext c
  rcases c with ⟨⟩ | (⟨⟩ | ⟨⟩) <;> rfl

lemma map_right_perm_iff (l : S (Fin 2)) :
    SetOperad.map fin3Right.symm (SetOperad.bin l SetOperad.one
        (SetOperad.bin l SetOperad.one SetOperad.one))
      = SetOperad.map (fin3Right.symm.trans (perm3 0 2 1)) (SetOperad.bin l SetOperad.one
          (SetOperad.bin l SetOperad.one SetOperad.one))
      ↔ SetOperad.bin l SetOperad.one (SetOperad.bin l SetOperad.one SetOperad.one)
        = SetOperad.bin l SetOperad.one
            (SetOperad.bin (SetOperad.map (Equiv.swap 0 1) l) SetOperad.one SetOperad.one) := by
  rw [bin_swap, bin_map_right, right_perm_eq, SetOperad.map_trans]
  exact (SetOperad.map_injective _).eq_iff

end Moves

variable (m l : Q (Fin 2))

/-- **Relators to relations**: generator values whose morphism kills the relators of `ComTrias`
satisfy the relations of commutative trialgebras. -/
def dataOfKills
    (h₂ : ∀ x ∈ ({BinRel.comm R ComTriOp.mid} : Set (FreeBin R ComTriOp (Fin 2))),
      (FreeSet.linHom R (vals m l)).app _ x = 0)
    (h₃ : ∀ x ∈ comTriasRel R, (FreeSet.linHom R (vals m l)).app _ x = 0) :
    ComTriasData (Und R Q) where
  mid := Und.of R Q m
  left := Und.of R Q l
  comm := by
    have h := h₂ _ rfl
    rw [BinRel.comm, map_sub, linHom_bin2, linHom_bin2, sub_eq_zero] at h
    have h' : SymOperad.map (R := R) (Equiv.swap 0 1) m = m := by
      have h'' := h.symm
      simp only [vals] at h''
      rw [h'', show (1 : Equiv.Perm (Fin 2)) = Equiv.refl _ from rfl, SymOperad.map_refl]
    show Und.of R Q (SymOperad.map (R := R) (Equiv.swap 0 1) m) = Und.of R Q m
    rw [h']
  assoc := by
    have h := h₃ (BinRel.assoc R ComTriOp.mid) (by simp [comTriasRel])
    rw [BinRel.assoc, map_sub, linHom_binL, linHom_binR, sub_eq_zero] at h
    have h' := congrArg (Und.of R Q) h
    simp only [Equiv.apply_symm_apply, map_trans_one] at h'
    exact (map_left_eq_right_iff _ _).1 h'
  lassoc := by
    have h := h₃ (BinRel.assoc R ComTriOp.left) (by simp [comTriasRel])
    rw [BinRel.assoc, map_sub, linHom_binL, linHom_binR, sub_eq_zero] at h
    have h' := congrArg (Und.of R Q) h
    simp only [Equiv.apply_symm_apply, map_trans_one] at h'
    exact (map_left_eq_right_iff _ _).1 h'
  lperm := by
    have h := h₃ (BinRel.perm R ComTriOp.left) (by simp [comTriasRel])
    rw [BinRel.perm, map_sub, linHom_binR, linHom_binR, sub_eq_zero] at h
    have h' := congrArg (Und.of R Q) h
    simp only [Equiv.apply_symm_apply, map_trans_one] at h'
    exact (map_right_perm_iff _).1 h'
  lmid := by
    have h := h₃ (BinRel.leftMid R ComTriOp.left ComTriOp.mid) (by simp [comTriasRel])
    rw [BinRel.leftMid, map_sub, linHom_binR, linHom_binR, sub_eq_zero] at h
    have h' := congrArg (Und.of R Q) h
    simp only [Equiv.apply_symm_apply, map_trans_one] at h'
    exact (map_right_inj _ _).1 h'
  midl := by
    have h := h₃ (BinRel.midLeft R ComTriOp.left ComTriOp.mid) (by simp [comTriasRel])
    rw [BinRel.midLeft, map_sub, linHom_binL, linHom_binR, sub_eq_zero] at h
    have h' := congrArg (Und.of R Q) h
    simp only [Equiv.apply_symm_apply, map_trans_one] at h'
    exact (map_left_eq_right_iff _ _).1 h'

/-- **Relations to relators**: generator values satisfying the relations of commutative
trialgebras define a morphism out of the free operad killing the relators of `ComTrias`. -/
theorem kills_of_data (D : ComTriasData (Und R Q)) :
    (∀ x ∈ ({BinRel.comm R ComTriOp.mid} : Set (FreeBin R ComTriOp (Fin 2))),
      (FreeSet.linHom R (vals ((Und.of R Q).symm D.mid) ((Und.of R Q).symm D.left))).app _ x = 0)
    ∧ ∀ x ∈ comTriasRel R,
      (FreeSet.linHom R (vals ((Und.of R Q).symm D.mid) ((Und.of R Q).symm D.left))).app _ x
        = 0 := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [BinRel.comm, map_sub, linHom_bin2, linHom_bin2, sub_eq_zero,
      show (1 : Equiv.Perm (Fin 2)) = Equiv.refl _ from rfl, SymOperad.map_refl]
    exact (congrArg (Und.of R Q).symm D.comm).symm
  · simp only [comTriasRel, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · rw [BinRel.assoc, map_sub, linHom_binL, linHom_binR, sub_eq_zero]
      apply congrArg (Und.of R Q).symm
      simp only [vals, Equiv.apply_symm_apply, map_trans_one]
      exact (map_left_eq_right_iff _ _).2 D.assoc
    · rw [BinRel.assoc, map_sub, linHom_binL, linHom_binR, sub_eq_zero]
      apply congrArg (Und.of R Q).symm
      simp only [vals, Equiv.apply_symm_apply, map_trans_one]
      exact (map_left_eq_right_iff _ _).2 D.lassoc
    · rw [BinRel.perm, map_sub, linHom_binR, linHom_binR, sub_eq_zero]
      apply congrArg (Und.of R Q).symm
      simp only [vals, Equiv.apply_symm_apply, map_trans_one]
      exact (map_right_perm_iff _).2 D.lperm
    · rw [BinRel.leftMid, map_sub, linHom_binR, linHom_binR, sub_eq_zero]
      apply congrArg (Und.of R Q).symm
      simp only [vals, Equiv.apply_symm_apply, map_trans_one]
      exact (map_right_inj _ _).2 D.lmid
    · rw [BinRel.midLeft, map_sub, linHom_binL, linHom_binR, sub_eq_zero]
      apply congrArg (Und.of R Q).symm
      simp only [vals, Equiv.apply_symm_apply, map_trans_one]
      exact (map_left_eq_right_iff _ _).2 D.midl

/-! ### The isomorphism -/

section Iso

variable (R : Type u) [CommRing R]

/-- The generators of `ComTrias R`: the full subset of two inputs and the first input. -/
noncomputable def nsData : ComTriasData (Und R (ComTrias R)) :=
  NonemptySubset.data.map ((linHomEquiv R).symm SymOperadHom.id)

/-- **`BinComTrias → ComTrias`**: `⊥` to the full subset, `⊣` to the first input. -/
noncomputable def toComTrias : SymOperadHom R (BinComTrias R) (ComTrias R) :=
  SymOperadIdeal.presHomEquiv.symm ⟨FreeSet.linHom R
    (vals ((Und.of R _).symm (nsData R).mid) ((Und.of R _).symm (nsData R).left)),
    forall_rel23.2 (kills_of_data (nsData R))⟩

/-- The projection of the free operad onto `BinComTrias` is the morphism with the projected
generators as values. -/
lemma linHom_proj :
    FreeSet.linHom R (vals
        ((SymOperadIdeal.span R (rel23 {BinRel.comm R ComTriOp.mid} (comTriasRel R))).proj _
          (bin2 .mid 1))
        ((SymOperadIdeal.span R (rel23 {BinRel.comm R ComTriOp.mid} (comTriasRel R))).proj _
          (bin2 .left 1)))
      = (SymOperadIdeal.span R (rel23 {BinRel.comm R ComTriOp.mid} (comTriasRel R))).projHom := by
  apply Pres.lin_hom_ext
  intro n g
  cases g with
  | op g => cases g <;> simp [vals, bin2_one_eq_single]

omit [CommRing R] in
lemma homEquiv_symm_single {R : Type u} [CommRing R]
    {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]
    (D : ComTriasData (Und R Q)) {A : Type} [Fintype A] [DecidableEq A] (s : NonemptySubset A) :
    ((ComTrias.homEquiv R).symm D).app A (Finsupp.single s 1)
      = (Und.of R Q).symm (D.lift.app A s) := by
  show Finsupp.lift (Q A) R (NonemptySubset A) _ (Finsupp.single s 1) = _
  simp
  rfl

/-- **`ComTrias → BinComTrias`**, by the universal property of `ComTrias`. -/
noncomputable def ofComTrias : SymOperadHom R (ComTrias R) (BinComTrias R) :=
  (ComTrias.homEquiv R).symm (dataOfKills (R := R)
    ((SymOperadIdeal.span R (rel23 {BinRel.comm R ComTriOp.mid} (comTriasRel R))).proj _
      (bin2 .mid 1))
    ((SymOperadIdeal.span R (rel23 {BinRel.comm R ComTriOp.mid} (comTriasRel R))).proj _
      (bin2 .left 1))
    (fun x hx => by
      rw [linHom_proj, SymOperadIdeal.projHom_app, SymOperadIdeal.proj_eq_zero_iff]
      exact SymOperadIdeal.subset_span (R := R) 2 hx)
    (fun x hx => by
      rw [linHom_proj, SymOperadIdeal.projHom_app, SymOperadIdeal.proj_eq_zero_iff]
      exact SymOperadIdeal.subset_span (R := R) 3 hx))

lemma ofComTrias_mid :
    (ofComTrias R).app _ (Finsupp.single NonemptySubset.mid 1)
      = (SymOperadIdeal.span R (rel23 {BinRel.comm R ComTriOp.mid} (comTriasRel R))).proj _
          (bin2 .mid 1) := by
  rw [ofComTrias, homEquiv_symm_single, ComTriasData.lift_mid]
  rfl

lemma ofComTrias_left :
    (ofComTrias R).app _ (Finsupp.single NonemptySubset.left 1)
      = (SymOperadIdeal.span R (rel23 {BinRel.comm R ComTriOp.mid} (comTriasRel R))).proj _
          (bin2 .left 1) := by
  rw [ofComTrias, homEquiv_symm_single, ComTriasData.lift_left]
  rfl

/-- **`ComTrias` is the binary quadratic operad `BinComTrias`**: Vallette's commutative
trialgebras, the linearization of the nonempty subsets, are presented by `⊥` commutative and `⊣`
with the relations `comTriasRel`. -/
noncomputable def isoComTrias : SymOperadIso R (BinComTrias R) (ComTrias R) where
  hom := toComTrias R
  inv := ofComTrias R
  hom_inv_id := by
    apply presLin_hom_ext
    intro n g
    cases g with
    | op g =>
      rw [SymOperadHom.comp_app, SymOperadHom.id_app, toComTrias,
        SymOperadIdeal.presHomEquiv_symm_proj, FreeSet.linHom_gen, ← bin2_one_eq_single]
      cases g
      · exact ofComTrias_mid R
      · exact ofComTrias_left R
  inv_hom_id := by
    apply (ComTrias.homEquiv R).injective
    apply ComTriasData.ext'
    · show Und.of R _ ((toComTrias R).app _ ((ofComTrias R).app _
          (Finsupp.single NonemptySubset.mid 1))) = Und.of R _ (Finsupp.single _ 1)
      rw [ofComTrias_mid, toComTrias, SymOperadIdeal.presHomEquiv_symm_proj, linHom_bin2,
        show (1 : Equiv.Perm (Fin 2)) = Equiv.refl _ from rfl, SymOperad.map_refl]
      rfl
    · show Und.of R _ ((toComTrias R).app _ ((ofComTrias R).app _
          (Finsupp.single NonemptySubset.left 1))) = Und.of R _ (Finsupp.single _ 1)
      rw [ofComTrias_left, toComTrias, SymOperadIdeal.presHomEquiv_symm_proj, linHom_bin2,
        show (1 : Equiv.Perm (Fin 2)) = Equiv.refl _ from rfl, SymOperad.map_refl]
      rfl

end Iso

end BinComTrias

end Operad
