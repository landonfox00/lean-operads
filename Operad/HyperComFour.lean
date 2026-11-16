/-
# The hypercommutative operad in arity four: `dim HyperCom(4) = 7`

**`dim HyperCom(4) = 7`** over any field (`HyperCom.finrank_four`). The seven operations
`HyperCom.seven` are a basis: `m₄`, the iterated product (`HyperCom.bin4`),
`m₃(m₂(x₀, x₁), x₂, x₃)`, and the four operations `m₂(m₃(…), x_a)`.

* **A relabelling of a composite of totally symmetric operations only depends on where the inner
  inputs go** (`SymOperad.map_comp_eq_of_symm`). So the composites `m₂ ∘ m₃` are the four
  operations `tOp a = m₂(m₃(…), x_a)` (`HyperCom.map_c23_eq_tOp`), and the composites `m₃ ∘ m₂`
  are the six operations `pOp a b = m₃(m₂(x_a, x_b), …)` (`HyperCom.map_c32_eq_pOp`,
  `HyperCom.pOp_comm`).
* **The product `m₂` is commutative and associative in the operad** (`HyperCom.isComm_m2`,
  `HyperCom.isAssoc_m2`), so the commutative operad maps to `HyperCom` (`HyperCom.ofCom`) and the
  iterated products with the same inputs agree (`HyperCom.IsBin.eq`).
* **Upper bound.** The relabellings of these operations and of `m₄` span, together with the
  operations of arity at most three of `Operad.HyperComDim` and everything of arity at least
  five, a suboperad containing the generators (`HyperCom.trunc4Sub`,
  `HyperCom.mem_span_basic4`). The WDVV relation of arity four reads
  `pOp i j + tOp k = pOp i k + tOp j` (`HyperCom.pOp_add_tOp`), so the operations `pOp a b` agree
  modulo the operations `tOp c` (`HyperCom.pOp_sub_mem_tSpan`), and seven operations span
  (`HyperCom.span_seven`).
* **Lower bound.** The hypercommutative algebra on `K × K` of `Operad.HyperComModel` separates
  the seven operations (`HyperCom.linearIndependent_seven`): the first coordinates of their
  values on inputs equal to `1` or `(0, 1)` form a triangular system.

The dimensions in arity five and beyond are not computed.
-/
import Operad.HyperComModel
import Operad.CyclicExt
import Operad.ComSet
import Mathlib.GroupTheory.Perm.Finite

universe u v

namespace Operad

open Sym Finset

namespace SymOperad

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]

/-- **A relabelling of a composite of totally symmetric operations only depends on where the
inner inputs go**: if two relabellings send the inner inputs into the same set, the relabelled
composites agree. -/
theorem map_comp_eq_of_symm {X Y A : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [Fintype A] [DecidableEq A] (i : X) {x : P X} {y : P Y}
    (hx : ∀ σ : Equiv.Perm X, map (R := R) σ x = x)
    (hy : ∀ τ : Equiv.Perm Y, map (R := R) τ y = y) (e e' : Without X i ⊕ Y ≃ A)
    (h : ∀ b : Y, ∃ b' : Y, e (Sum.inr b) = e' (Sum.inr b')) :
    map (R := R) e (comp (R := R) i x y) = map (R := R) e' (comp (R := R) i x y) := by
  set f : Equiv.Perm (Without X i ⊕ Y) := e.trans e'.symm with hf
  have hr : Set.MapsTo f (Set.range Sum.inr) (Set.range Sum.inr) := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨b', hb'⟩ := h b
    exact ⟨b', by rw [hf, Equiv.trans_apply, hb', Equiv.symm_apply_apply]⟩
  have hl : Set.MapsTo f (Set.range Sum.inl) (Set.range Sum.inl) :=
    (Equiv.Perm.perm_mapsTo_inl_iff_mapsTo_inr f).2 hr
  obtain ⟨⟨σ₁, τ⟩, hστ⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hl
  have hσi : Equiv.Perm.ofSubtype σ₁ i = i :=
    Equiv.Perm.ofSubtype_apply_of_not_mem σ₁ (by simp)
  have key := comp_map_map_of_eq (R := R) (Equiv.Perm.ofSubtype σ₁) τ hσi x y
  rw [hx, hy] at key
  have hE : compEquiv' (Equiv.Perm.ofSubtype σ₁) τ hσi = f := by
    rw [← hστ]
    refine Equiv.ext fun w => ?_
    rcases w with ⟨a, ha⟩ | b
    · exact congrArg Sum.inl (Subtype.ext (Equiv.Perm.ofSubtype_apply_of_mem σ₁ ha))
    · rfl
  rw [hE] at key
  have he : e = f.trans e' := by
    refine Equiv.ext fun w => ?_
    rw [hf, Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [he, map_trans, ← key]

/-- Filling an input with the identity is a relabelling. -/
lemma comp_one_eq {A : Type} [Fintype A] [DecidableEq A] (i : A) (x : P A) :
    comp (R := R) i x (one R) = map (R := R) (rightUnitEquiv i).symm x := by
  have := congrArg (map (R := R) (rightUnitEquiv i).symm) (comp_one (R := R) i x)
  rwa [map_symm_map] at this

end SymOperad

namespace HyperCom

open SetOperad

variable {R : Type u} [CommRing R]

/-! ## The commutative operad inside the hypercommutative operad -/

/-- **A relabelling of `m₂ ∘₀ m₂`.** -/
def IsC22 {A : Type} [Fintype A] [DecidableEq A] (z : HyperComOp R A) : Prop :=
  ∃ e : W ≃ A, z = SymOperad.map (R := R) e (c22 R)

lemma IsC22.map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {z : HyperComOp R A} (hz : IsC22 z) (g : A ≃ B) : IsC22 (SymOperad.map (R := R) g z) := by
  obtain ⟨e, rfl⟩ := hz
  exact ⟨e.trans g, (SymOperad.map_trans (R := R) e g _).symm⟩

/-- **Two relabellings of `m₂ ∘₀ m₂` with the same inputs agree.** -/
lemma IsC22.eq {A : Type} [Fintype A] [DecidableEq A] {z z' : HyperComOp R A} (hz : IsC22 z)
    (hz' : IsC22 z') : z = z' := by
  obtain ⟨e, rfl⟩ := hz
  obtain ⟨e', rfl⟩ := hz'
  obtain ⟨g⟩ : Nonempty (A ≃ Fin 3) := ⟨e.symm.trans (Fintype.equivFinOfCardEq card_W)⟩
  have h := map_c22_eq_all (R := R) (e.trans g) (e'.trans g)
  rw [SymOperad.map_trans, SymOperad.map_trans] at h
  have h' := congrArg (SymOperad.map (R := R) g.symm) h
  rwa [SymOperad.map_symm_map, SymOperad.map_symm_map] at h'

/-- **A composite of `m₂` with itself, at either input, is a relabelling of `m₂ ∘₀ m₂`.** -/
lemma isC22_comp (j : Fin 2) :
    IsC22 (SymOperad.comp (R := R) j (opGen (R := R) 2 le_rfl) (opGen 2 le_rfl)) := by
  obtain ⟨σ, rfl⟩ : ∃ σ : Equiv.Perm (Fin 2), σ 0 = j :=
    ⟨Equiv.swap 0 j, Equiv.swap_apply_left _ _⟩
  have := SymOperad.map_comp (R := R) σ (Equiv.refl (Fin 2)) 0 (opGen (R := R) 2 le_rfl)
    (opGen 2 le_rfl)
  rw [map_opGen, SymOperad.map_refl] at this
  exact ⟨_, this.symm⟩

/-- The two inputs of `m₂` filled, in the operad. -/
noncomputable def binQ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (x : HyperComOp R A) (y : HyperComOp R B) : HyperComOp R (A ⊕ B) :=
  SymOperad.map (R := R) (binEquiv A B)
    (SymOperad.comp (R := R) (Sum.inl slotOne)
      (SymOperad.comp (R := R) (0 : Fin 2) (opGen 2 le_rfl) x) y)

/-- `m₂` with both inputs filled by the identity is a relabelling of `m₂`. -/
lemma binQ_one_one : ∃ E : Fin 2 ≃ Unit ⊕ Unit,
    binQ (SymOperad.one R : HyperComOp R Unit) (SymOperad.one R : HyperComOp R Unit) =
      SymOperad.map (R := R) E (opGen (R := R) 2 le_rfl) := by
  unfold binQ
  rw [SymOperad.comp_one_eq, SymOperad.comp_one_eq, ← SymOperad.map_trans, ← SymOperad.map_trans]
  exact ⟨_, rfl⟩

lemma isC22_binQ_left (E : Fin 2 ≃ Unit ⊕ Unit) :
    IsC22 (binQ (SymOperad.map (R := R) E (opGen (R := R) 2 le_rfl)) (SymOperad.one R)) := by
  unfold binQ
  rw [SymOperad.comp_one_eq, SymOperad.comp_map_right_of_eq]
  exact (((isC22_comp 0).map _).map _).map _

lemma isC22_binQ_right (E : Fin 2 ≃ Unit ⊕ Unit) :
    IsC22 (binQ (SymOperad.one R) (SymOperad.map (R := R) E (opGen (R := R) 2 le_rfl))) := by
  unfold binQ
  rw [SymOperad.comp_one_eq]
  have hi : (rightUnitEquiv (0 : Fin 2)).symm ((rightUnitEquiv (0 : Fin 2)) (Sum.inl slotOne)) =
      Sum.inl slotOne := Equiv.symm_apply_apply _ _
  rw [SymOperad.comp_map_map_of_eq (R := R) _ E hi]
  exact ((isC22_comp _).map _).map _

variable (R) in
/-- **The product `m₂`**, in the underlying set operad. -/
noncomputable def m2 : Und R (HyperComOp R) (Fin 2) := Und.of R _ (opGen 2 le_rfl)

lemma isComm_m2 : IsComm (m2 R) := map_opGen le_rfl _

/-- **The product `m₂` is associative**: both composites are relabellings of `m₂ ∘₀ m₂`, which
all agree by the WDVV relation of arity three. -/
lemma isAssoc_m2 : IsAssoc (m2 R) := by
  obtain ⟨E, hE⟩ := binQ_one_one (R := R)
  have h1 : IsC22 (SymOperad.map (R := R) (Equiv.sumAssoc Unit Unit Unit)
      (binQ (binQ (SymOperad.one R : HyperComOp R Unit) (SymOperad.one R : HyperComOp R Unit))
        (SymOperad.one R : HyperComOp R Unit))) := by
    rw [hE]
    exact (isC22_binQ_left E).map _
  have h2 : IsC22 (binQ (SymOperad.one R : HyperComOp R Unit)
      (binQ (SymOperad.one R : HyperComOp R Unit) (SymOperad.one R : HyperComOp R Unit))) := by
    rw [hE]
    exact isC22_binQ_right E
  exact h1.eq h2

variable (R) in
/-- **The commutative operad maps to the hypercommutative operad**, its product to `m₂`. -/
noncomputable def ofCom : SymOperadHom R (Lin R ComSet) (HyperComOp R) :=
  (ComSet.linHomEquiv R).symm ⟨m2 R, isComm_m2, isAssoc_m2⟩

/-- The commutative operad sends its product to `m₂`. -/
lemma ofCom_mu :
    (ofCom R).app (Fin 2) (Finsupp.single ComSet.mu 1) = opGen (R := R) 2 le_rfl :=
  congrArg Subtype.val ((ComSet.linHomEquiv R).apply_symm_apply ⟨m2 R, isComm_m2, isAssoc_m2⟩)

/-- **A binary operation**: the image of an operation of `ComSet`, that is, an iterated product
`m₂`. -/
def IsBin {A : Type} [Fintype A] [DecidableEq A] (z : HyperComOp R A) : Prop :=
  ∃ s : ComSet A, z = (ofCom R).app A (Finsupp.single s 1)

lemma isBin_m2 : IsBin (opGen (R := R) 2 le_rfl) := ⟨ComSet.mu, ofCom_mu.symm⟩

lemma IsBin.map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {z : HyperComOp R A} (hz : IsBin z) (g : A ≃ B) : IsBin (SymOperad.map (R := R) g z) := by
  obtain ⟨s, rfl⟩ := hz
  refine ⟨SetOperad.map g s, ?_⟩
  rw [← (ofCom R).app_map]
  exact congrArg _ (Lin.mapL_single (R := R) g s 1)

lemma IsBin.comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {z : HyperComOp R A} {z' : HyperComOp R B} (hz : IsBin z) (hz' : IsBin z') (i : A) :
    IsBin (SymOperad.comp (R := R) i z z') := by
  obtain ⟨s, rfl⟩ := hz
  obtain ⟨t, rfl⟩ := hz'
  refine ⟨SetOperad.comp i s t, ?_⟩
  rw [← (ofCom R).app_comp]
  refine congrArg _ ?_
  show Lin.compL R i (Finsupp.single s 1) (Finsupp.single t 1) = _
  rw [Lin.compL_single, mul_one]

/-- **Two binary operations with the same inputs agree**: `ComSet` has one operation on each
nonempty set of inputs. -/
lemma IsBin.eq {A : Type} [Fintype A] [DecidableEq A] {z z' : HyperComOp R A} (hz : IsBin z)
    (hz' : IsBin z') : z = z' := by
  obtain ⟨s, rfl⟩ := hz
  obtain ⟨t, rfl⟩ := hz'
  rw [Subsingleton.elim s t]

lemma isBin_c22 : IsBin (c22 R) := isBin_m2.comp isBin_m2 0

variable (R) in
/-- **The binary operation of arity four**: the iterated product of four inputs. -/
noncomputable def bin4 : HyperComOp R (Fin 4) :=
  (ofCom R).app (Fin 4) (Finsupp.single ⟨⟨0⟩⟩ 1)

lemma isBin_bin4 : IsBin (bin4 R) := ⟨_, rfl⟩

/-! ## The operations of arity four -/

/-- The inputs of `m₂ ∘ⱼ m₃`. -/
abbrev W23 (j : Fin 2) := Without (Fin 2) j ⊕ Fin 3

/-- The inputs of `m₃ ∘ⱼ m₂`. -/
abbrev W32 (j : Fin 3) := Without (Fin 3) j ⊕ Fin 2

lemma card_W23 (j : Fin 2) : Fintype.card (W23 j) = 4 := by
  have := card_comp (X := Fin 2) (Y := Fin 3) j
  rw [Fintype.card_fin, Fintype.card_fin] at this
  show Fintype.card (Without (Fin 2) j ⊕ Fin 3) = 4
  omega

lemma card_W32 (j : Fin 3) : Fintype.card (W32 j) = 4 := by
  have := card_comp (X := Fin 3) (Y := Fin 2) j
  rw [Fintype.card_fin, Fintype.card_fin] at this
  show Fintype.card (Without (Fin 3) j ⊕ Fin 2) = 4
  omega

variable (R) in
/-- **`m₂ ∘ⱼ m₃`**: the product of `m₃` of three inputs with a fourth. -/
noncomputable def c23 (j : Fin 2) : HyperComOp R (W23 j) :=
  SymOperad.comp (R := R) j (opGen 2 le_rfl) (opGen 3 (by norm_num))

variable (R) in
/-- **`m₃ ∘ⱼ m₂`**: `m₃` of a product of two inputs and two more. -/
noncomputable def c32 (j : Fin 3) : HyperComOp R (W32 j) :=
  SymOperad.comp (R := R) j (opGen 3 (by norm_num)) (opGen 2 le_rfl)

variable (R) in
/-- **The basic operations of arity four** with inputs `A`: the relabellings of `m₄`, of the
composites `m₂ ∘ⱼ m₃` and `m₃ ∘ⱼ m₂`, and of the binary operation. -/
def basic4 (A : Type) [Fintype A] [DecidableEq A] : Set (HyperComOp R A) :=
  {x | (∃ e : Fin 4 ≃ A, x = SymOperad.map (R := R) e (opGen 4 (by norm_num))) ∨
    (∃ (j : Fin 2) (e : W23 j ≃ A), x = SymOperad.map (R := R) e (c23 R j)) ∨
    (∃ (j : Fin 3) (e : W32 j ≃ A), x = SymOperad.map (R := R) e (c32 R j)) ∨
    (∃ e : Fin 4 ≃ A, x = SymOperad.map (R := R) e (bin4 R))}

variable (R) in
/-- **The suboperad truncated above arity four**: spanned by the basic operations in arities at
most four, and everything in higher arities. -/
noncomputable def trunc4 (A : Type) [Fintype A] [DecidableEq A] :
    Submodule R (HyperComOp R A) :=
  if 5 ≤ Fintype.card A then ⊤ else Submodule.span R (basic R A ∪ basic4 R A)

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

lemma mem_trunc4_of_card (h : 5 ≤ Fintype.card A) (x : HyperComOp R A) : x ∈ trunc4 R A := by
  rw [trunc4, if_pos h]
  exact Submodule.mem_top

lemma mem_trunc4_of_gen {x : HyperComOp R A} (hx : x ∈ basic R A ∪ basic4 R A) :
    x ∈ trunc4 R A := by
  unfold trunc4
  split_ifs
  · exact Submodule.mem_top
  · exact Submodule.subset_span hx

lemma map_mem_basic4 (e : A ≃ B) {x : HyperComOp R A} (hx : x ∈ basic4 R A) :
    SymOperad.map (R := R) e x ∈ basic4 R B := by
  rcases hx with ⟨f, rfl⟩ | ⟨j, f, rfl⟩ | ⟨j, f, rfl⟩ | ⟨f, rfl⟩
  · exact Or.inl ⟨f.trans e, (SymOperad.map_trans (R := R) f e _).symm⟩
  · exact Or.inr (Or.inl ⟨j, f.trans e, (SymOperad.map_trans (R := R) f e _).symm⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨j, f.trans e, (SymOperad.map_trans (R := R) f e _).symm⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨f.trans e, (SymOperad.map_trans (R := R) f e _).symm⟩))

lemma map_mem_trunc4 (e : A ≃ B) {x : HyperComOp R A} (hx : x ∈ trunc4 R A) :
    SymOperad.map (R := R) e x ∈ trunc4 R B := by
  have hc := Fintype.card_congr e
  unfold trunc4 at hx ⊢
  split_ifs at hx ⊢ with h₁ h₂ h₂
  · exact Submodule.mem_top
  · exact absurd (hc ▸ h₁) h₂
  · exact absurd (hc ▸ h₂) h₁
  · refine (Submodule.span_le.2 ?_ : Submodule.span R (basic R A ∪ basic4 R A) ≤
      (Submodule.span R (basic R B ∪ basic4 R B)).comap (SymOperad.map (R := R) e)) hx
    rintro y (hy | hy)
    · exact Submodule.subset_span (Or.inl (map_mem_basic e hy))
    · exact Submodule.subset_span (Or.inr (map_mem_basic4 e hy))

/-- **A binary operation of arity four is basic.** -/
lemma mem_basic4_of_isBin {x : HyperComOp R A} (hx : IsBin x) (hA : Fintype.card A = 4) :
    x ∈ basic4 R A := by
  refine Or.inr (Or.inr (Or.inr ⟨(Fintype.equivFinOfCardEq hA).symm, ?_⟩))
  exact hx.eq (isBin_bin4.map _)

lemma nonempty_of_basic4 {x : HyperComOp R A} (hx : x ∈ basic4 R A) : Nonempty A := by
  rcases hx with ⟨f, -⟩ | ⟨j, f, -⟩ | ⟨j, f, -⟩ | ⟨f, -⟩
  exacts [⟨f 0⟩, ⟨f (Sum.inr 0)⟩, ⟨f (Sum.inr 0)⟩, ⟨f 0⟩]

/-- Compositions of relabellings are relabellings of compositions. -/
lemma comp_map_mem4 {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (g : HyperComOp R X) (g' : HyperComOp R Y)
    (H : ∀ j : X, SymOperad.comp (R := R) j g g' ∈ trunc4 R (Without X j ⊕ Y))
    (e : X ≃ A) (f : Y ≃ B) (i : A) :
    SymOperad.comp (R := R) i (SymOperad.map (R := R) e g) (SymOperad.map (R := R) f g')
      ∈ trunc4 R (Without A i ⊕ B) := by
  obtain ⟨j, rfl⟩ := e.surjective i
  rw [← SymOperad.map_comp]
  exact map_mem_trunc4 _ (H j)

lemma comp_one_left4 {Y : Type} [Fintype Y] [DecidableEq Y] {g' : HyperComOp R Y}
    (hg' : g' ∈ trunc4 R Y) (j : Unit) :
    SymOperad.comp (R := R) j (SymOperad.one R) g' ∈ trunc4 R (Without Unit j ⊕ Y) := by
  have := congrArg (SymOperad.map (R := R) (leftUnitEquiv Y).symm)
    (SymOperad.one_comp (R := R) g')
  rw [SymOperad.map_symm_map] at this
  rw [this]
  exact map_mem_trunc4 _ hg'

lemma comp_one_right4 {X : Type} [Fintype X] [DecidableEq X] {g : HyperComOp R X}
    (hg : g ∈ trunc4 R X) (j : X) :
    SymOperad.comp (R := R) j g (SymOperad.one R) ∈ trunc4 R (Without X j ⊕ Unit) := by
  rw [SymOperad.comp_one_eq]
  exact map_mem_trunc4 _ hg

lemma comp_big4 {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (h : 6 ≤ Fintype.card X + Fintype.card Y) (g : HyperComOp R X) (g' : HyperComOp R Y)
    (j : X) : SymOperad.comp (R := R) j g g' ∈ trunc4 R (Without X j ⊕ Y) :=
  mem_trunc4_of_card (by have := card_comp (Y := Y) j; omega) _

lemma one_mem4 : SymOperad.one R ∈ trunc4 R Unit :=
  mem_trunc4_of_gen (Or.inl (Or.inl ⟨Equiv.refl _, (SymOperad.map_refl (R := R) _).symm⟩))

lemma m2_mem4 : opGen (R := R) 2 le_rfl ∈ trunc4 R (Fin 2) :=
  mem_trunc4_of_gen
    (Or.inl (Or.inr (Or.inl ⟨Equiv.refl _, (SymOperad.map_refl (R := R) _).symm⟩)))

lemma m3_mem4 : opGen (R := R) 3 (by norm_num) ∈ trunc4 R (Fin 3) :=
  mem_trunc4_of_gen
    (Or.inl (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, (SymOperad.map_refl (R := R) _).symm⟩))))

lemma c22_mem4 : c22 R ∈ trunc4 R W :=
  mem_trunc4_of_gen
    (Or.inl (Or.inr (Or.inr (Or.inr ⟨Equiv.refl _, (SymOperad.map_refl (R := R) _).symm⟩))))

lemma m4_mem4 : opGen (R := R) 4 (by norm_num) ∈ trunc4 R (Fin 4) :=
  mem_trunc4_of_gen (Or.inr (Or.inl ⟨Equiv.refl _, (SymOperad.map_refl (R := R) _).symm⟩))

lemma c23_mem4 (j : Fin 2) : c23 R j ∈ trunc4 R (W23 j) :=
  mem_trunc4_of_gen
    (Or.inr (Or.inr (Or.inl ⟨j, Equiv.refl _, (SymOperad.map_refl (R := R) _).symm⟩)))

lemma c32_mem4 (j : Fin 3) : c32 R j ∈ trunc4 R (W32 j) :=
  mem_trunc4_of_gen
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, Equiv.refl _, (SymOperad.map_refl (R := R) _).symm⟩))))

lemma bin4_mem4 : bin4 R ∈ trunc4 R (Fin 4) :=
  mem_trunc4_of_gen
    (Or.inr (Or.inr (Or.inr (Or.inr ⟨Equiv.refl _, (SymOperad.map_refl (R := R) _).symm⟩))))

lemma comp_m2_m2_mem4 (j : Fin 2) :
    SymOperad.comp (R := R) j (opGen 2 le_rfl) (opGen 2 le_rfl)
      ∈ trunc4 R (Without (Fin 2) j ⊕ Fin 2) := by
  obtain ⟨e, he⟩ := isC22_comp (R := R) j
  exact mem_trunc4_of_gen (Or.inl (Or.inr (Or.inr (Or.inr ⟨e, he⟩))))

lemma comp_m2_m3_mem4 (j : Fin 2) :
    SymOperad.comp (R := R) j (opGen 2 le_rfl) (opGen 3 (by norm_num)) ∈ trunc4 R (W23 j) :=
  c23_mem4 j

lemma comp_m3_m2_mem4 (j : Fin 3) :
    SymOperad.comp (R := R) j (opGen 3 (by norm_num)) (opGen 2 le_rfl) ∈ trunc4 R (W32 j) :=
  c32_mem4 j

lemma comp_m2_c22_mem4 (j : Fin 2) :
    SymOperad.comp (R := R) j (opGen 2 le_rfl) (c22 R) ∈ trunc4 R (Without (Fin 2) j ⊕ W) := by
  refine mem_trunc4_of_gen (Or.inr (mem_basic4_of_isBin (isBin_m2.comp isBin_c22 j) ?_))
  have := card_comp (X := Fin 2) (Y := W) j
  rw [Fintype.card_fin, card_W] at this
  omega

lemma comp_c22_m2_mem4 (j : W) :
    SymOperad.comp (R := R) j (c22 R) (opGen 2 le_rfl) ∈ trunc4 R (Without W j ⊕ Fin 2) := by
  refine mem_trunc4_of_gen (Or.inr (mem_basic4_of_isBin (isBin_c22.comp isBin_m2 j) ?_))
  have := card_comp (X := W) (Y := Fin 2) j
  rw [Fintype.card_fin, card_W] at this
  omega

lemma comp_mem_trunc4 (i : A) {x : HyperComOp R A} {y : HyperComOp R B}
    (hx : x ∈ trunc4 R A) (hy : y ∈ trunc4 R B) :
    SymOperad.comp (R := R) i x y ∈ trunc4 R (Without A i ⊕ B) := by
  by_cases h5 : 5 ≤ Fintype.card (Without A i ⊕ B)
  · exact mem_trunc4_of_card h5 _
  have hc := card_comp (Y := B) i
  have hA1 := Fintype.card_pos_iff.2 ⟨i⟩
  have hyS : y ∈ Submodule.span R (basic R B ∪ basic4 R B) := by
    unfold trunc4 at hy
    rwa [if_neg (by omega)] at hy
  by_cases hA : 5 ≤ Fintype.card A
  · have hB : Fintype.card B = 0 := by omega
    haveI := Fintype.card_eq_zero_iff.1 hB
    have hT : basic R B ∪ basic4 R B = ∅ := Set.eq_empty_of_forall_notMem fun z hz =>
      hz.elim (fun h => (nonempty_of_basic h).elim isEmptyElim)
        (fun h => (nonempty_of_basic4 h).elim isEmptyElim)
    rw [hT, Submodule.span_empty, Submodule.mem_bot] at hyS
    rw [hyS, map_zero]
    exact zero_mem _
  have hxS : x ∈ Submodule.span R (basic R A ∪ basic4 R A) := by
    unfold trunc4 at hx
    rwa [if_neg hA] at hx
  have hm := Submodule.apply_mem_map₂ (SymOperad.comp (R := R) i) hxS hyS
  rw [Submodule.map₂_span_span] at hm
  refine (Submodule.span_le.2 ?_) hm
  rintro _ ⟨x, hx, y, hy, rfl⟩
  rcases hx with (⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩) |
    (⟨e, rfl⟩ | ⟨j₁, e, rfl⟩ | ⟨j₁, e, rfl⟩ | ⟨e, rfl⟩) <;>
  rcases hy with (⟨f, rfl⟩ | ⟨f, rfl⟩ | ⟨f, rfl⟩ | ⟨f, rfl⟩) |
    (⟨f, rfl⟩ | ⟨j₂, f, rfl⟩ | ⟨j₂, f, rfl⟩ | ⟨f, rfl⟩) <;>
  refine comp_map_mem4 _ _ ?_ e f i
  · exact comp_one_left4 one_mem4
  · exact comp_one_left4 m2_mem4
  · exact comp_one_left4 m3_mem4
  · exact comp_one_left4 c22_mem4
  · exact comp_one_left4 m4_mem4
  · exact comp_one_left4 (c23_mem4 _)
  · exact comp_one_left4 (c32_mem4 _)
  · exact comp_one_left4 bin4_mem4
  · exact comp_one_right4 m2_mem4
  · exact comp_m2_m2_mem4
  · exact comp_m2_m3_mem4
  · exact comp_m2_c22_mem4
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_one_right4 m3_mem4
  · exact comp_m3_m2_mem4
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_one_right4 c22_mem4
  · exact comp_c22_m2_mem4
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_one_right4 m4_mem4
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_one_right4 (c23_mem4 _)
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_one_right4 (c32_mem4 _)
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_one_right4 bin4_mem4
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _
  · exact comp_big4 (by simp) _ _

variable (R) in
/-- **The suboperad truncated above arity four.** -/
noncomputable def trunc4Sub : SymSuboperad R (HyperComOp R) where
  sub := trunc4 R
  map_mem e _ hx := map_mem_trunc4 e hx
  one_mem := one_mem4
  comp_mem i _ _ hx hy := comp_mem_trunc4 i hx hy

/-- **Every operation is in the suboperad truncated above arity four**: it contains the
generators. -/
theorem mem_trunc4 (x : HyperComOp R A) : x ∈ trunc4 R A := by
  refine SymSuboperad.mem_of_presGen (trunc4Sub R) (fun n g => ?_) x
  obtain ⟨hg⟩ := g
  obtain rfl | rfl | rfl | h5 : n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n := by omega
  · exact m2_mem4
  · exact m3_mem4
  · exact m4_mem4
  · exact mem_trunc4_of_card (by simpa using h5) _

/-- **In arity four, the operations are spanned by the basic operations of arity four.** -/
theorem mem_span_basic4 (hA : Fintype.card A = 4) (x : HyperComOp R A) :
    x ∈ Submodule.span R (basic4 R A) := by
  have h := mem_trunc4 x
  unfold trunc4 at h
  rw [if_neg (by omega)] at h
  have he : basic R A = ∅ := Set.eq_empty_of_forall_notMem fun z hz => by
    rcases hz with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · exact absurd (Fintype.card_congr e) (by simp [hA])
    · exact absurd (Fintype.card_congr e) (by simp [hA])
    · exact absurd (Fintype.card_congr e) (by simp [hA])
    · exact absurd (Fintype.card_congr e) (by rw [card_W, hA]; norm_num)
  rwa [he, Set.empty_union] at h

/-! ## The orbits of the mixed composites -/

lemma c23_eq_map (j : Fin 2) :
    ∃ E : W23 0 ≃ W23 j, c23 R j = SymOperad.map (R := R) E (c23 R 0) := by
  obtain ⟨σ, rfl⟩ : ∃ σ : Equiv.Perm (Fin 2), σ 0 = j :=
    ⟨Equiv.swap 0 j, Equiv.swap_apply_left _ _⟩
  have := SymOperad.map_comp (R := R) σ (Equiv.refl (Fin 3)) 0 (opGen (R := R) 2 le_rfl)
    (opGen 3 (by norm_num))
  rw [map_opGen, SymOperad.map_refl] at this
  exact ⟨_, this.symm⟩

lemma c32_eq_map (j : Fin 3) :
    ∃ E : W32 0 ≃ W32 j, c32 R j = SymOperad.map (R := R) E (c32 R 0) := by
  obtain ⟨σ, rfl⟩ : ∃ σ : Equiv.Perm (Fin 3), σ 0 = j :=
    ⟨Equiv.swap 0 j, Equiv.swap_apply_left _ _⟩
  have := SymOperad.map_comp (R := R) σ (Equiv.refl (Fin 2)) 0
    (opGen (R := R) 3 (by norm_num)) (opGen 2 le_rfl)
  rw [map_opGen, SymOperad.map_refl] at this
  exact ⟨_, this.symm⟩

/-- **A relabelling of `m₂ ∘₀ m₃` only depends on where the outer input goes.** -/
lemma map_c23_eq (e e' : W23 0 ≃ A) (h : e (Sum.inl slotOne) = e' (Sum.inl slotOne)) :
    SymOperad.map (R := R) e (c23 R 0) = SymOperad.map (R := R) e' (c23 R 0) := by
  refine SymOperad.map_comp_eq_of_symm (0 : Fin 2) (fun σ => map_opGen _ σ)
    (fun τ => map_opGen _ τ) e e' fun b => ?_
  rcases hb : e'.symm (e (Sum.inr b)) with x | b'
  · exfalso
    have h1 : e (Sum.inr b) = e' (Sum.inl x) := by rw [← hb, Equiv.apply_symm_apply]
    rw [eq_slotOne x, ← h] at h1
    exact Sum.inr_ne_inl (e.injective h1)
  · exact ⟨b', by rw [← hb, Equiv.apply_symm_apply]⟩

/-- **A relabelling of `m₃ ∘₀ m₂` only depends on where the two inner inputs go.** -/
lemma map_c32_eq (e e' : W32 0 ≃ A) (h : ∀ b, ∃ b', e (Sum.inr b) = e' (Sum.inr b')) :
    SymOperad.map (R := R) e (c32 R 0) = SymOperad.map (R := R) e' (c32 R 0) :=
  SymOperad.map_comp_eq_of_symm (0 : Fin 3) (fun σ => map_opGen _ σ) (fun τ => map_opGen _ τ)
    e e' h

/-- A relabelling of the inputs of `m₂ ∘₀ m₃` sending the outer input to `a`. -/
noncomputable def eT (a : Fin 4) : W23 0 ≃ Fin 4 :=
  (Fintype.equivFinOfCardEq (card_W23 0)).trans
    (Equiv.swap ((Fintype.equivFinOfCardEq (card_W23 0)) (Sum.inl slotOne)) a)

lemma eT_outer (a : Fin 4) : eT a (Sum.inl slotOne) = a := by
  rw [eT, Equiv.trans_apply, Equiv.swap_apply_left]

variable (R) in
/-- **The operation `m₂(m₃(…), x_a)`**: the product of `m₃` of the three other inputs with the
input `a`. -/
noncomputable def tOp (a : Fin 4) : HyperComOp R (Fin 4) :=
  SymOperad.map (R := R) (eT a) (c23 R 0)

lemma map_c23_eq_tOp (e : W23 0 ≃ Fin 4) :
    SymOperad.map (R := R) e (c23 R 0) = tOp R (e (Sum.inl slotOne)) :=
  map_c23_eq e _ (eT_outer _).symm

/-- A relabelling of the inputs of `m₃ ∘₀ m₂` sending the inner inputs to `a` and `b`. -/
noncomputable def eP (a b : Fin 4) : W32 0 ≃ Fin 4 :=
  ((Fintype.equivFinOfCardEq (card_W32 0)).trans
    (Equiv.swap ((Fintype.equivFinOfCardEq (card_W32 0)) (Sum.inr 0)) a)).trans
    (Equiv.swap (Equiv.swap ((Fintype.equivFinOfCardEq (card_W32 0)) (Sum.inr 0)) a
      ((Fintype.equivFinOfCardEq (card_W32 0)) (Sum.inr 1))) b)

lemma eP_one (a b : Fin 4) : eP a b (Sum.inr 1) = b := by
  rw [eP, Equiv.trans_apply, Equiv.trans_apply, Equiv.swap_apply_left]

lemma eP_zero {a b : Fin 4} (hab : a ≠ b) : eP a b (Sum.inr 0) = a := by
  rw [eP, Equiv.trans_apply, Equiv.trans_apply, Equiv.swap_apply_left]
  refine Equiv.swap_apply_of_ne_of_ne (fun h => ?_) hab
  have h1 := (Equiv.swap ((Fintype.equivFinOfCardEq (card_W32 0)) (Sum.inr 0)) a).injective
    ((Equiv.swap_apply_left _ _).trans h)
  exact absurd ((Fintype.equivFinOfCardEq (card_W32 0)).injective h1) (by simp)

variable (R) in
/-- **The operation `m₃(m₂(x_a, x_b), …)`**: `m₃` of the product of the inputs `a` and `b` and
the two other inputs. -/
noncomputable def pOp (a b : Fin 4) : HyperComOp R (Fin 4) :=
  SymOperad.map (R := R) (eP a b) (c32 R 0)

lemma map_c32_eq_pOp (e : W32 0 ≃ Fin 4) :
    SymOperad.map (R := R) e (c32 R 0) = pOp R (e (Sum.inr 0)) (e (Sum.inr 1)) := by
  have hne : e (Sum.inr 0) ≠ e (Sum.inr 1) := fun h => by
    simpa using e.injective h
  refine map_c32_eq e _ fun t => ?_
  fin_cases t
  · exact ⟨0, (eP_zero hne).symm⟩
  · exact ⟨1, (eP_one _ _).symm⟩

lemma pOp_comm {a b : Fin 4} (hab : a ≠ b) : pOp R a b = pOp R b a := by
  refine map_c32_eq _ _ fun t => ?_
  fin_cases t
  · exact ⟨1, (eP_zero hab).trans (eP_one _ _).symm⟩
  · exact ⟨0, (eP_one _ _).trans (eP_zero hab.symm).symm⟩

/-! ## The WDVV relation of arity four -/

local notation "I" => SymOperadIdeal.span R (hcRel R)

lemma filter_four (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    univ.filter (fun S : Finset (Fin 4) => i ∈ S ∧ j ∈ S ∧ k ∉ S) = {{i, j}, {k}ᶜ} := by
  revert i j k
  decide

lemma pair_ne_compl (i j k : Fin 4) (hij : i ≠ j) :
    ({i, j} : Finset (Fin 4)) ≠ {k}ᶜ := fun h => by
  have := congrArg Finset.card h
  rw [Finset.card_pair hij, Finset.card_compl, Finset.card_singleton, Fintype.card_fin] at this
  omega

/-- **A WDVV composite of arity four on a pair** is a relabelling of `m₃ ∘₀ m₂`, the inner
inputs going into the pair. -/
lemma proj_wTerm_two (S : Finset (Fin 4)) (hS : S.card = 2) :
    ∃ e : W32 0 ≃ Fin 4, (I).proj _ (wTerm (R := R) S) = SymOperad.map (R := R) e (c32 R 0) ∧
      ∀ t, e (Sum.inr t) ∈ S := by
  have hc : Sᶜ.card = 2 := by rw [Finset.card_compl, hS]; rfl
  have key : ∀ (a b : ℕ) (_ : a = 2) (_ : b = 2) (E : Without (Fin (a + 1)) 0 ⊕ Fin b ≃ Fin 4)
      (h1 : 2 ≤ a + 1) (h2 : 2 ≤ b), (∀ t, E (Sum.inr t) ∈ S) →
      ∃ e : W32 0 ≃ Fin 4, (I).proj _ (Finsupp.single (Pres.mk (.map E
        (.comp 0 (gen (a + 1) h1) (gen b h2)))) (1 : R) : FreeHC R (Fin 4)) =
        SymOperad.map (R := R) e (c32 R 0) ∧ ∀ t, e (Sum.inr t) ∈ S := by
    rintro a b rfl rfl E h1 h2 hE
    refine ⟨E, ?_, hE⟩
    have h0 : (Finsupp.single (Pres.mk (.map E (.comp 0 (gen (2 + 1) h1) (gen 2 h2)))) (1 : R) :
        FreeHC R (Fin 4)) = SymOperad.map (R := R) (P := FreeHC R) E
          (SymOperad.comp (R := R) (0 : Fin 3)
            (Finsupp.single (Pres.gen (⟨by norm_num⟩ : HCGen 3)) 1)
            (Finsupp.single (Pres.gen (⟨le_rfl⟩ : HCGen 2)) 1)) := by
      show _ = Lin.mapL R E (Lin.compL R 0 _ _)
      rw [Lin.compL_single, Lin.mapL_single, mul_one]
      rfl
    rw [h0, ← SymOperadIdeal.projHom_app, SymOperadHom.app_map, SymOperadHom.app_comp]
    rfl
  unfold wTerm
  rw [dif_pos ⟨by omega, by omega⟩]
  exact key _ _ hc hS (wEquiv S) _ _ fun t => by
    rw [wEquiv_inr]
    exact Finset.orderEmbOfFin_mem _ _ _

/-- **A WDVV composite of arity four on a triple** is a relabelling of `m₂ ∘₀ m₃`, the outer
input going out of the triple. -/
lemma proj_wTerm_three (S : Finset (Fin 4)) (hS : S.card = 3) :
    ∃ e : W23 0 ≃ Fin 4, (I).proj _ (wTerm (R := R) S) = SymOperad.map (R := R) e (c23 R 0) ∧
      ∀ x, e (Sum.inl x) ∉ S := by
  have hc : Sᶜ.card = 1 := by rw [Finset.card_compl, hS]; rfl
  have key : ∀ (a b : ℕ) (_ : a = 1) (_ : b = 3) (E : Without (Fin (a + 1)) 0 ⊕ Fin b ≃ Fin 4)
      (h1 : 2 ≤ a + 1) (h2 : 2 ≤ b), (∀ x, E (Sum.inl x) ∉ S) →
      ∃ e : W23 0 ≃ Fin 4, (I).proj _ (Finsupp.single (Pres.mk (.map E
        (.comp 0 (gen (a + 1) h1) (gen b h2)))) (1 : R) : FreeHC R (Fin 4)) =
        SymOperad.map (R := R) e (c23 R 0) ∧ ∀ x, e (Sum.inl x) ∉ S := by
    rintro a b rfl rfl E h1 h2 hE
    refine ⟨E, ?_, hE⟩
    have h0 : (Finsupp.single (Pres.mk (.map E (.comp 0 (gen (1 + 1) h1) (gen 3 h2)))) (1 : R) :
        FreeHC R (Fin 4)) = SymOperad.map (R := R) (P := FreeHC R) E
          (SymOperad.comp (R := R) (0 : Fin 2)
            (Finsupp.single (Pres.gen (⟨le_rfl⟩ : HCGen 2)) 1)
            (Finsupp.single (Pres.gen (⟨by norm_num⟩ : HCGen 3)) 1)) := by
      show _ = Lin.mapL R E (Lin.compL R 0 _ _)
      rw [Lin.compL_single, Lin.mapL_single, mul_one]
      rfl
    rw [h0, ← SymOperadIdeal.projHom_app, SymOperadHom.app_map, SymOperadHom.app_comp]
    rfl
  unfold wTerm
  rw [dif_pos ⟨by omega, by omega⟩]
  exact key _ _ hc hS (wEquiv S) _ _ fun x => by
    rw [wEquiv_inl]
    exact Finset.mem_compl.1 (Finset.orderEmbOfFin_mem _ _ _)

lemma proj_wTerm_pair {i j : Fin 4} (hij : i ≠ j) :
    (I).proj _ (wTerm (R := R) {i, j}) = pOp R i j := by
  obtain ⟨e, he, hm⟩ := proj_wTerm_two (R := R) {i, j} (Finset.card_pair hij)
  rw [he]
  refine map_c32_eq e _ fun t => ?_
  rcases Finset.mem_insert.1 (hm t) with h | h
  · exact ⟨0, h.trans (eP_zero hij).symm⟩
  · exact ⟨1, (Finset.mem_singleton.1 h).trans (eP_one _ _).symm⟩

lemma proj_wTerm_compl (k : Fin 4) : (I).proj _ (wTerm (R := R) {k}ᶜ) = tOp R k := by
  obtain ⟨e, he, hm⟩ := proj_wTerm_three (R := R) {k}ᶜ (by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin])
  rw [he, map_c23_eq_tOp]
  have := hm slotOne
  rw [Finset.mem_compl, Finset.mem_singleton, not_not] at this
  rw [this]

/-- **The WDVV relation of arity four**: for distinct inputs `i, j, k`,
`m₃(m₂(xᵢ, xⱼ), …) + m₂(m₃(…), x_k) = m₃(m₂(xᵢ, x_k), …) + m₂(m₃(…), xⱼ)`. -/
theorem pOp_add_tOp {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    pOp R i j + tOp R k = pOp R i k + tOp R j := by
  have hrel : wdvv (R := R) i j k ∈ (I).sub (Fin 4) :=
    SymOperadIdeal.subset_span (R := R) 4 (Or.inr ⟨i, j, k, hij, hik, hjk, rfl⟩)
  rw [← SymOperadIdeal.proj_eq_zero_iff, wdvv, filter_four _ _ _ hij hik hjk,
    filter_four _ _ _ hik hij hjk.symm, Finset.sum_pair (pair_ne_compl i j k hij),
    Finset.sum_pair (pair_ne_compl i k j hik), map_sub, map_add, map_add, sub_eq_zero,
    proj_wTerm_pair hij, proj_wTerm_pair hik, proj_wTerm_compl, proj_wTerm_compl] at hrel
  exact hrel

/-! ## Seven operations span arity four -/

variable (R) in
/-- The span of the operations `m₂(m₃(…), x_a)`. -/
noncomputable def tSpan : Submodule R (HyperComOp R (Fin 4)) :=
  Submodule.span R (Set.range (tOp R))

lemma pOp_sub_mem {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    pOp R i j - pOp R i k ∈ tSpan R := by
  have h : pOp R i j - pOp R i k = tOp R j - tOp R k :=
    sub_eq_sub_iff_add_eq_add.2 ((pOp_add_tOp hij hik hjk).trans (add_comm _ _))
  rw [h]
  exact Submodule.sub_mem _ (Submodule.subset_span ⟨j, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)

lemma pOp_zero_sub_mem {a : Fin 4} (ha : a ≠ 0) : pOp R 0 a - pOp R 0 1 ∈ tSpan R := by
  by_cases h1 : a = 1
  · rw [h1, sub_self]
    exact zero_mem _
  · exact pOp_sub_mem (Ne.symm ha) (by decide) h1

/-- **The operations `m₃(m₂(x_a, x_b), …)` agree modulo the operations `m₂(m₃(…), x_c)`**, by
the WDVV relations. -/
theorem pOp_sub_mem_tSpan {a b : Fin 4} (hab : a ≠ b) : pOp R a b - pOp R 0 1 ∈ tSpan R := by
  by_cases ha : a = 0
  · subst ha
    exact pOp_zero_sub_mem (Ne.symm hab)
  by_cases hb : b = 0
  · subst hb
    rw [pOp_comm hab]
    exact pOp_zero_sub_mem ha
  have h1 := pOp_sub_mem (R := R) hab ha hb
  have h2 := pOp_zero_sub_mem (R := R) ha
  have h : pOp R a b - pOp R 0 1 = (pOp R a b - pOp R a 0) + (pOp R 0 a - pOp R 0 1) := by
    rw [pOp_comm ha]
    abel
  rw [h]
  exact add_mem h1 h2

variable (R) in
/-- **The seven operations of arity four**: `m₄`, the iterated product, `m₃(m₂(x₀, x₁), x₂, x₃)`
and the four operations `m₂(m₃(…), x_a)`. -/
noncomputable def seven : Fin 7 → HyperComOp R (Fin 4) :=
  ![opGen 4 (by norm_num), bin4 R, pOp R 0 1, tOp R 0, tOp R 1, tOp R 2, tOp R 3]

lemma tSpan_le : tSpan R ≤ Submodule.span R (Set.range (seven R)) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, rfl⟩
  fin_cases a
  · exact Submodule.subset_span ⟨3, rfl⟩
  · exact Submodule.subset_span ⟨4, rfl⟩
  · exact Submodule.subset_span ⟨5, rfl⟩
  · exact Submodule.subset_span ⟨6, rfl⟩

lemma basic4_subset : basic4 R (Fin 4) ⊆ Submodule.span R (Set.range (seven R)) := by
  rintro x (⟨e, rfl⟩ | ⟨j, e, rfl⟩ | ⟨j, e, rfl⟩ | ⟨e, rfl⟩)
  · rw [map_opGen]
    exact Submodule.subset_span ⟨0, rfl⟩
  · obtain ⟨E, hE⟩ := c23_eq_map (R := R) j
    rw [hE, ← SymOperad.map_trans, map_c23_eq_tOp]
    exact tSpan_le (Submodule.subset_span ⟨_, rfl⟩)
  · obtain ⟨E, hE⟩ := c32_eq_map (R := R) j
    rw [hE, ← SymOperad.map_trans, map_c32_eq_pOp]
    have hne : (E.trans e) (Sum.inr 0) ≠ (E.trans e) (Sum.inr 1) := fun h => by
      simpa using (E.trans e).injective h
    rw [← sub_add_cancel (pOp R ((E.trans e) (Sum.inr 0)) ((E.trans e) (Sum.inr 1)))
      (pOp R 0 1)]
    exact add_mem (tSpan_le (pOp_sub_mem_tSpan hne)) (Submodule.subset_span ⟨2, rfl⟩)
  · rw [(isBin_bin4.map e).eq isBin_bin4]
    exact Submodule.subset_span ⟨1, rfl⟩

/-- **The seven operations span the operations of arity four.** -/
theorem span_seven : Submodule.span R (Set.range (seven R)) = ⊤ :=
  eq_top_iff.2 fun x _ => Submodule.span_le.2 basic4_subset (mem_span_basic4 (by simp) x)

/-! ## The model separates the seven operations -/

section Eval

open HCAlg

/-- The algebra structure of the model. -/
noncomputable abbrev modelAlg (c : ℕ → R) : SymAlgebra R (HyperComOp R) (R × R) :=
  (HyperComOp.algebraEquiv R (R × R)).symm (HCAlg.model c)

lemma alg_map (Φ : SymAlgebra R (HyperComOp R) (R × R)) (e : A ≃ B) (z : HyperComOp R A)
    (w : B → R × R) :
    Φ.app B (SymOperad.map (R := R) e z) w = Φ.app A z fun a => w (e a) := by
  rw [SymOperadHom.app_map]
  rfl

lemma alg_comp (Φ : SymAlgebra R (HyperComOp R) (R × R)) (i : A) (x : HyperComOp R A)
    (y : HyperComOp R B) (w : Without A i ⊕ B → R × R) :
    Φ.app _ (SymOperad.comp (R := R) i x y) w =
      Φ.app A x (feed i w (Φ.app B y fun b => w (Sum.inr b))) := by
  rw [SymOperadHom.app_comp]
  rfl

lemma model_opGen (c : ℕ → R) {n : ℕ} (h : 2 ≤ n) :
    (modelAlg c).app (Fin n) (opGen n h) = modelOps R c n h :=
  alg_opGen (HCAlg.model c) h

/-- The value of `m₂ ∘₀ m₃` in the model. -/
lemma model_c23 (c : ℕ → R) (w : W23 0 → R × R) :
    (modelAlg c).app _ (c23 R 0) w =
      ((c 3 * ∏ t, hL R (w (Sum.inr t))) • (1 : R × R)) * w (Sum.inl slotOne) := by
  rw [c23, alg_comp, model_opGen, model_opGen, modelOps_two c _ rfl, Fin.prod_univ_two,
    feed_self, feed_of_ne (by decide), modelOps_of_ne c _ (by norm_num)]
  rfl

/-- The value of `m₂(m₃(…), x_b)` in the model. -/
lemma model_tOp (c : ℕ → R) (w : Fin 4 → R × R) (b : Fin 4) :
    (modelAlg c).app _ (tOp R b) w =
      ((c 3 * ∏ t, hL R (w (eT b (Sum.inr t)))) • (1 : R × R)) * w b := by
  rw [tOp, alg_map, model_c23, eT_outer]

/-- The value of `m₃(m₂(x_a, x_b), …)` in the model, on equal inputs. -/
lemma model_pOp_const (c : ℕ → R) (u : R × R) (a b : Fin 4) :
    (modelAlg c).app _ (pOp R a b) (fun _ => u) =
      (c 3 * (hL R (u * u) * (hL R u * hL R u))) • (1 : R × R) := by
  rw [pOp, alg_map, c32, alg_comp, model_opGen, model_opGen, modelOps_of_ne c _ (by norm_num),
    modelOps_two c _ rfl, Fin.prod_univ_two, Fin.prod_univ_three, feed_self,
    feed_of_ne (by decide), feed_of_ne (by decide), _root_.mul_assoc]

/-- The value of `m₄` in the model. -/
lemma model_m4 (c : ℕ → R) (w : Fin 4 → R × R) :
    (modelAlg c).app _ (opGen 4 (by norm_num)) w = (c 4 * ∏ i, hL R (w i)) • (1 : R × R) := by
  rw [model_opGen, modelOps_of_ne c _ (by norm_num)]

/-- The value of the iterated product in the model, on equal inputs. -/
lemma model_bin4_const (c : ℕ → R) (u : R × R) :
    (modelAlg c).app _ (bin4 R) (fun _ => u) = u * u * u * u := by
  obtain ⟨e⟩ : Nonempty (Without (Fin 2) 0 ⊕ W ≃ Fin 4) := ⟨Fintype.equivFinOfCardEq (by
    have := card_comp (X := Fin 2) (Y := W) 0
    rw [Fintype.card_fin, card_W] at this
    omega)⟩
  rw [isBin_bin4.eq ((isBin_m2.comp isBin_c22 0).map e), alg_map, alg_comp, model_opGen,
    modelOps_two c _ rfl, Fin.prod_univ_two, feed_self, feed_of_ne (by decide), c22, alg_comp,
    model_opGen, modelOps_two c _ rfl, modelOps_two c _ rfl, Fin.prod_univ_two,
    Fin.prod_univ_two, feed_self, feed_of_ne (by decide)]

/-- **The first coordinate of the value in the model**, a linear functional on the operations
of arity four. -/
noncomputable def evalFst (c : ℕ → R) (w : Fin 4 → R × R) : HyperComOp R (Fin 4) →ₗ[R] R where
  toFun x := ((modelAlg c).app (Fin 4) x w).1
  map_add' x y := by rw [map_add, MultilinearMap.add_apply, Prod.fst_add]
  map_smul' s x := by
    rw [map_smul, MultilinearMap.smul_apply, Prod.smul_fst, RingHom.id_apply]

lemma evalFst_apply (c : ℕ → R) (w : Fin 4 → R × R) (x : HyperComOp R (Fin 4)) :
    evalFst c w x = ((modelAlg c).app (Fin 4) x w).1 := rfl

lemma evalFst_m4 (c : ℕ → R) (w : Fin 4 → R × R) :
    evalFst c w (opGen 4 (by norm_num)) = c 4 * ∏ i, hL R (w i) := by
  rw [evalFst_apply, model_m4, Prod.smul_fst, Prod.fst_one, smul_eq_mul, mul_one]

lemma evalFst_bin4 (c : ℕ → R) (u : R × R) :
    evalFst c (fun _ => u) (bin4 R) = u.1 * u.1 * u.1 * u.1 := by
  rw [evalFst_apply, model_bin4_const, Prod.fst_mul, Prod.fst_mul, Prod.fst_mul]

lemma evalFst_pOp (c : ℕ → R) (u : R × R) (a b : Fin 4) :
    evalFst c (fun _ => u) (pOp R a b) = c 3 * (hL R (u * u) * (hL R u * hL R u)) := by
  rw [evalFst_apply, model_pOp_const, Prod.smul_fst, Prod.fst_one, smul_eq_mul, mul_one]

lemma evalFst_tOp (c : ℕ → R) (w : Fin 4 → R × R) (b : Fin 4) :
    evalFst c w (tOp R b) = c 3 * (∏ t, hL R (w (eT b (Sum.inr t)))) * (w b).1 := by
  rw [evalFst_apply, model_tOp, Prod.fst_mul, Prod.smul_fst, Prod.fst_one, smul_eq_mul, mul_one]

/-- The input `(0, 1)`, on which the functional is `1`. -/
def uH : R × R := (0, 1)

lemma hL_uH : hL R (uH : R × R) = 1 := sub_zero _

lemma uH_mul : (uH : R × R) * uH = uH := Prod.ext (mul_zero _) (mul_one _)

/-- The inputs equal to `(0, 1)` except the input `a`, equal to `1`. -/
def wA (a : Fin 4) : Fin 4 → R × R := Function.update (fun _ => uH) a 1

lemma prod_eT_self (a : Fin 4) : ∏ t, hL R (wA (R := R) a (eT a (Sum.inr t))) = 1 := by
  refine Finset.prod_eq_one fun t _ => ?_
  have hne : eT a (Sum.inr t) ≠ a := fun h =>
    Sum.inr_ne_inl ((eT a).injective (h.trans (eT_outer a).symm))
  rw [wA, Function.update_of_ne hne, hL_uH]

lemma prod_eT_ne {a b : Fin 4} (hab : a ≠ b) :
    ∏ t, hL R (wA (R := R) a (eT b (Sum.inr t))) = 0 := by
  obtain ⟨t, ht⟩ : ∃ t, eT b (Sum.inr t) = a := by
    rcases h : (eT b).symm a with x | t
    · exfalso
      have h1 : a = eT b (Sum.inl x) := by rw [← h, Equiv.apply_symm_apply]
      rw [eq_slotOne x, eT_outer] at h1
      exact hab h1
    · exact ⟨t, by rw [← h, Equiv.apply_symm_apply]⟩
  refine Finset.prod_eq_zero (Finset.mem_univ t) ?_
  rw [ht, wA, Function.update_self, hL_one]

lemma evalFst_tOp_wA (a b : Fin 4) :
    evalFst (R := R) (fun n => if n = 3 then 1 else 0) (wA a) (tOp R b) =
      if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst h
    rw [evalFst_tOp, prod_eT_self, if_pos rfl, if_pos rfl, wA, Function.update_self, Prod.fst_one,
      mul_one, mul_one]
  · rw [evalFst_tOp, prod_eT_ne h, if_neg h, mul_zero, zero_mul]

end Eval

/-! ## The dimension -/

section Dim

variable (K : Type u) [Field K]

/-- **The seven operations of arity four are linearly independent**: the model separates them,
first the iterated product, then `m₄`, then `m₃(m₂(x₀, x₁), x₂, x₃)`, then the four operations
`m₂(m₃(…), x_a)`. -/
theorem linearIndependent_seven : LinearIndependent K (seven K) := by
  rw [Fintype.linearIndependent_iff]
  intro s hs
  have hsum : s 0 • opGen (R := K) 4 (by norm_num) + s 1 • bin4 K + s 2 • pOp K 0 1 +
      s 3 • tOp K 0 + s 4 • tOp K 1 + s 5 • tOp K 2 + s 6 • tOp K 3 = 0 := by
    rw [← hs, Fin.sum_univ_seven]
    rfl
  have key : ∀ ψ : HyperComOp K (Fin 4) →ₗ[K] K,
      s 0 * ψ (opGen 4 (by norm_num)) + s 1 * ψ (bin4 K) + s 2 * ψ (pOp K 0 1) +
        s 3 * ψ (tOp K 0) + s 4 * ψ (tOp K 1) + s 5 * ψ (tOp K 2) + s 6 * ψ (tOp K 3) = 0 :=
    fun ψ => by
      have := congrArg ψ hsum
      simpa only [map_add, map_smul, smul_eq_mul, map_zero] using this
  have h1 : s 1 = 0 := by
    have := key (evalFst (fun _ => 0) fun _ => 1)
    simpa [evalFst_m4, evalFst_bin4, evalFst_pOp, evalFst_tOp] using this
  have h0 : s 0 = 0 := by
    have := key (evalFst (fun n => if n = 4 then 1 else 0) fun _ => uH)
    simpa [evalFst_m4, evalFst_pOp, evalFst_tOp, hL_uH, h1, uH] using this
  have h2 : s 2 = 0 := by
    have := key (evalFst (fun n => if n = 3 then 1 else 0) fun _ => uH)
    simpa [evalFst_m4, evalFst_pOp, evalFst_tOp, hL_uH, uH_mul, h0, h1, uH] using this
  have h3 : s 3 = 0 := by
    have := key (evalFst (fun n => if n = 3 then 1 else 0) (wA 0))
    simpa [evalFst_tOp_wA, h0, h1, h2] using this
  have h4 : s 4 = 0 := by
    have := key (evalFst (fun n => if n = 3 then 1 else 0) (wA 1))
    simpa [evalFst_tOp_wA, h0, h1, h2] using this
  have h5 : s 5 = 0 := by
    have := key (evalFst (fun n => if n = 3 then 1 else 0) (wA 2))
    simpa [evalFst_tOp_wA, h0, h1, h2] using this
  have h6 : s 6 = 0 := by
    have := key (evalFst (fun n => if n = 3 then 1 else 0) (wA 3))
    simpa [evalFst_tOp_wA, h0, h1, h2] using this
  intro i
  fin_cases i
  exacts [h0, h1, h2, h3, h4, h5, h6]

/-- **`dim HyperCom(4) = 7`**, on the inputs `Fin 4`. -/
theorem finrank_fin_four : Module.finrank K (HyperComOp K (Fin 4)) = 7 := by
  rw [← finrank_top, ← span_seven (R := K), finrank_span_eq_card (linearIndependent_seven K)]
  simp

variable {K}

/-- **The hypercommutative operad has seven operations of arity four**, over any field: `m₄`,
the iterated product, and five of the ten composites of `m₂` and `m₃`. -/
theorem finrank_four (hA : Fintype.card A = 4) : Module.finrank K (HyperComOp K A) = 7 := by
  rw [← (SymOperad.mapEquiv (R := K) (P := HyperComOp K)
    (Fintype.equivFinOfCardEq hA).symm).finrank_eq, finrank_fin_four]

end Dim

end HyperCom

end Operad
