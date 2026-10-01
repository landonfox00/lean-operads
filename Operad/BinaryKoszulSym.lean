/-
# Koszul duality with relators of arity two

`Operad.BinaryKoszul` dualizes binary quadratic operads whose generators carry the regular action
of `𝔖₂`. Here generators may be commutative or anticommutative: the presentation has relators
`r₂` of arity two as well.

* **The relations of arity three of relators of arity two** (`ideal3Of`) are their composites
  with the operations of arity two, on either side, relabelled; the relations of arity three of
  the operad presented by `r₂` and `r₃` are these and the relabellings of `r₃`
  (`span_sub_three_23`), so the operad is determined by `r₂` up to relabelling and by that space
  (`span_le_23`). These are computed in the free model of labelled trees (`evalW`,
  `evalW_injective`), where composites of monomials of arity two are monomials of arity three
  (`comp_e0_bin2`, `comp_e1_bin2`), and spanned by the relabelled composites of the relators with
  the monomials (`ideal3Of_le`); the monomials of arity two are a basis (`basis2`).
* **The Koszul dual** (`BinPres.dual23`): the relators of arity two twisted by the signature
  (`twist2`), so that a commutative generator becomes anticommutative and conversely, and in
  arity three the orthogonal, for the Koszul pairing, of all the relations of arity three
  (`dualRel23`). Without relators of arity two it is the Koszul dual of `Operad.BinaryKoszul`
  (`BinPres.dual23_empty`).
* **`Com^! = Lie`** (`BinCom.dual`), over a field in which `2 ≠ 0`: the relations of arity three
  of `Com` are the elements whose coordinates sum to zero (`sumCoord_eq_zero`,
  `finrank_comRel3`), so the dual relations are spanned by the antisymmetrized associator
  (`asym3`, `dualRel23_com`), which modulo antisymmetry is four times the Jacobiator
  (`asym3_eq`).
-/
import Operad.BinaryKoszul

universe u v

namespace Operad

open Sym SetOperad

namespace FreeBin

variable (R : Type u) [CommRing R] {G : Type v}

/-! ## The relations of arity three of relators of arity two -/

section Ideal23

/-- The relabellings of a set of elements of arity two. -/
def orbit2 (r : Set (FreeBin R G (Fin 2))) : Set (FreeBin R G (Fin 2)) :=
  {x | ∃ τ : Equiv.Perm (Fin 2), ∃ y ∈ r, x = SymOperad.map (R := R) τ y}

/-- **The relations of arity three implied by relators of arity two**: their composites with the
operations of arity two, on either side, relabelled. -/
noncomputable def ideal3Of (r : Set (FreeBin R G (Fin 2))) : Submodule R (FreeBin R G (Fin 3)) :=
  Submodule.span R {v | ∃ (i : Fin 2) (f : Without (Fin 2) i ⊕ Fin 2 ≃ Fin 3)
    (x y : FreeBin R G (Fin 2)), (x ∈ r ∨ y ∈ r) ∧
      v = SymOperad.map (R := R) f (SymOperad.comp (R := R) i x y)}

variable {R}

lemma map_mem_span_orbit2 {r : Set (FreeBin R G (Fin 2))} (τ : Equiv.Perm (Fin 2))
    {x : FreeBin R G (Fin 2)} (hx : x ∈ Submodule.span R (orbit2 R r)) :
    SymOperad.map (R := R) τ x ∈ Submodule.span R (orbit2 R r) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨τ', y, hy, rfl⟩ := hy
    exact Submodule.subset_span ⟨τ * τ', y, hy, by rw [SymOperad.map_map, Equiv.Perm.mul_def]⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

lemma ideal3Of_map_mem {r : Set (FreeBin R G (Fin 2))} (τ : Equiv.Perm (Fin 3))
    {x : FreeBin R G (Fin 3)} (hx : x ∈ ideal3Of R r) :
    SymOperad.map (R := R) τ x ∈ ideal3Of R r := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, f, a, b, hab, rfl⟩ := hy
    exact Submodule.subset_span ⟨i, f.trans τ, a, b, hab, by rw [SymOperad.map_map]⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

/-- Composites of relabelled relators, on the left. -/
lemma comp_mem_ideal3Of_left {r : Set (FreeBin R G (Fin 2))} (i : Fin 2)
    (f : Without (Fin 2) i ⊕ Fin 2 ≃ Fin 3) {x : FreeBin R G (Fin 2)}
    (hx : x ∈ Submodule.span R (orbit2 R r)) (y : FreeBin R G (Fin 2)) :
    SymOperad.map (R := R) f (SymOperad.comp (R := R) i x y) ∈ ideal3Of R r := by
  induction hx using Submodule.span_induction generalizing i with
  | mem z hz =>
    obtain ⟨τ, z, hz, rfl⟩ := hz
    obtain ⟨j, rfl⟩ := τ.surjective i
    rw [SymOperad.comp_map_left, SymOperad.map_map]
    exact Submodule.subset_span ⟨j, _, z, y, Or.inl hz, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, map_add]; exact add_mem (ha i f) (hb i f)
  | smul c a _ ha =>
    rw [map_smul, LinearMap.smul_apply, map_smul]
    exact Submodule.smul_mem _ c (ha i f)

/-- Composites with relabelled relators, on the right. -/
lemma comp_mem_ideal3Of_right {r : Set (FreeBin R G (Fin 2))} (i : Fin 2)
    (f : Without (Fin 2) i ⊕ Fin 2 ≃ Fin 3) (x : FreeBin R G (Fin 2)) {y : FreeBin R G (Fin 2)}
    (hy : y ∈ Submodule.span R (orbit2 R r)) :
    SymOperad.map (R := R) f (SymOperad.comp (R := R) i x y) ∈ ideal3Of R r := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨τ, z, hz, rfl⟩ := hz
    rw [SymOperad.comp_map_right, SymOperad.map_map]
    exact Submodule.subset_span ⟨i, _, x, z, Or.inr hz, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul, map_smul]; exact Submodule.smul_mem _ c ha

variable (R)

/-- The components of the ideal of relators `r₂` of arity two and a space `W` of arity three:
the relabellings of `r₂` in arity two, of `W` in arity three, and everything above. -/
noncomputable def ideal23Sub (r₂ : Set (FreeBin R G (Fin 2)))
    (W : Submodule R (FreeBin R G (Fin 3)))
    (A : Type) [Fintype A] [DecidableEq A] : Submodule R (FreeBin R G A) :=
  if Fintype.card A = 2 then
    ⨅ f : A ≃ Fin 2, (Submodule.span R (orbit2 R r₂)).comap (SymOperad.map (R := R) f)
  else ideal3Sub R W A

variable {R}

lemma mem_ideal23Sub_two {r₂ : Set (FreeBin R G (Fin 2))} {W : Submodule R (FreeBin R G (Fin 3))}
    {A : Type} [Fintype A] [DecidableEq A] (hA : Fintype.card A = 2) {x : FreeBin R G A} :
    x ∈ ideal23Sub R r₂ W A ↔
      ∀ f : A ≃ Fin 2, SymOperad.map (R := R) f x ∈ Submodule.span R (orbit2 R r₂) := by
  unfold ideal23Sub
  rw [if_pos hA]
  simp only [Submodule.mem_iInf, Submodule.mem_comap]

lemma mem_ideal23Sub_ne {r₂ : Set (FreeBin R G (Fin 2))} {W : Submodule R (FreeBin R G (Fin 3))}
    {A : Type} [Fintype A] [DecidableEq A] (hA : Fintype.card A ≠ 2) {x : FreeBin R G A} :
    x ∈ ideal23Sub R r₂ W A ↔ x ∈ ideal3Sub R W A := by
  unfold ideal23Sub
  rw [if_neg hA]

variable {r₂ : Set (FreeBin R G (Fin 2))} {W : Submodule R (FreeBin R G (Fin 3))}

lemma ideal23_map_mem {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) {x : FreeBin R G A} (hx : x ∈ ideal23Sub R r₂ W A) :
    SymOperad.map (R := R) e x ∈ ideal23Sub R r₂ W B := by
  have hcard := Fintype.card_congr e
  by_cases hA : Fintype.card A = 2
  · rw [mem_ideal23Sub_two hA] at hx
    rw [mem_ideal23Sub_two (by omega)]
    intro f
    rw [SymOperad.map_map]
    exact hx (e.trans f)
  · rw [mem_ideal23Sub_ne hA] at hx
    rw [mem_ideal23Sub_ne (by omega)]
    exact ideal3_map_mem R e hx

lemma equiv_fin_two {A : Type} [Fintype A] (h : Fintype.card A = 2) : Nonempty (A ≃ Fin 2) :=
  ⟨Fintype.equivOfCardEq (by rw [h, Fintype.card_fin])⟩

lemma ideal23_comp_left (hW : ideal3Of R r₂ ≤ W) {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (i : A) (y : FreeBin R G B) {x : FreeBin R G A}
    (hx : x ∈ ideal23Sub R r₂ W A) :
    SymOperad.comp (R := R) i x y ∈ ideal23Sub R r₂ W (Without A i ⊕ B) := by
  have hc := card_target (B := B) i
  have hA0 : 0 < Fintype.card A := Fintype.card_pos_iff.2 ⟨i⟩
  by_cases hA : Fintype.card A = 2
  · rw [mem_ideal23Sub_two hA] at hx
    by_cases hb0 : Fintype.card B = 0
    · rw [freeBin_eq_zero R hb0 y, map_zero]
      exact Submodule.zero_mem _
    by_cases hb1 : Fintype.card B = 1
    · obtain ⟨u⟩ : Nonempty (Unit ≃ B) :=
        ⟨Fintype.equivOfCardEq (by rw [Fintype.card_unit, hb1])⟩
      rw [freeBin_eq_smul_single R hb1 (SetOperad.map u SetOperad.one) y, map_smul,
        comp_single_unit, mem_ideal23Sub_two (by omega)]
      intro f
      rw [map_smul, SymOperad.map_map]
      exact Submodule.smul_mem _ _ (hx _)
    by_cases hb2 : Fintype.card B = 2
    · rw [mem_ideal23Sub_ne (by omega), mem_ideal3Sub]
      refine ⟨fun h => absurd h (by omega), fun f => ?_⟩
      obtain ⟨eA⟩ := equiv_fin_two hA
      obtain ⟨eB⟩ := equiv_fin_two hb2
      obtain ⟨j, rfl⟩ := eA.symm.surjective i
      obtain ⟨x', rfl⟩ : ∃ x', x = SymOperad.map (R := R) eA.symm x' :=
        ⟨SymOperad.map (R := R) eA x, by rw [SymOperad.map_map, Equiv.self_trans_symm,
          SymOperad.map_refl]⟩
      obtain ⟨y', rfl⟩ : ∃ y', y = SymOperad.map (R := R) eB.symm y' :=
        ⟨SymOperad.map (R := R) eB y, by rw [SymOperad.map_map, Equiv.self_trans_symm,
          SymOperad.map_refl]⟩
      have hx' := hx eA
      rw [SymOperad.map_map, Equiv.symm_trans_self, SymOperad.map_refl] at hx'
      rw [SymOperad.comp_map_right, SymOperad.comp_map_left, SymOperad.map_map,
        SymOperad.map_map]
      exact hW (comp_mem_ideal3Of_left j _ hx' y')
    · rw [mem_ideal23Sub_ne (by omega), mem_ideal3Sub]
      exact ⟨fun h => absurd h (by omega), fun f => (not_equiv_fin3 (by omega) f).elim⟩
  · rw [mem_ideal23Sub_ne hA] at hx
    by_cases ht : Fintype.card (Without A i ⊕ B) = 2
    · by_cases hb0 : Fintype.card B = 0
      · rw [freeBin_eq_zero R hb0 y, map_zero]
        exact Submodule.zero_mem _
      · rw [((mem_ideal3Sub R).1 hx).1 (by omega), map_zero, LinearMap.zero_apply]
        exact Submodule.zero_mem _
    · rw [mem_ideal23Sub_ne ht]
      exact ideal3_comp_left R i y hx

lemma ideal23_comp_right (hW : ideal3Of R r₂ ≤ W) {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (i : A) (x : FreeBin R G A) {y : FreeBin R G B}
    (hy : y ∈ ideal23Sub R r₂ W B) :
    SymOperad.comp (R := R) i x y ∈ ideal23Sub R r₂ W (Without A i ⊕ B) := by
  have hc := card_target (B := B) i
  have hA0 : 0 < Fintype.card A := Fintype.card_pos_iff.2 ⟨i⟩
  by_cases hB : Fintype.card B = 2
  · rw [mem_ideal23Sub_two hB] at hy
    by_cases ha1 : Fintype.card A = 1
    · obtain ⟨u⟩ : Nonempty (Unit ≃ A) :=
        ⟨Fintype.equivOfCardEq (by rw [Fintype.card_unit, ha1])⟩
      have hi : u () = i := by
        haveI : Subsingleton A := Fintype.card_le_one_iff_subsingleton.1 ha1.le
        exact Subsingleton.elim _ _
      rw [freeBin_eq_smul_single R ha1 (SetOperad.map u SetOperad.one) x, map_smul,
        LinearMap.smul_apply, comp_unit_single R u hi, mem_ideal23Sub_two (by omega)]
      intro f
      rw [map_smul, SymOperad.map_map]
      exact Submodule.smul_mem _ _ (hy _)
    by_cases ha2 : Fintype.card A = 2
    · rw [mem_ideal23Sub_ne (by omega), mem_ideal3Sub]
      refine ⟨fun h => absurd h (by omega), fun f => ?_⟩
      obtain ⟨eA⟩ := equiv_fin_two ha2
      obtain ⟨eB⟩ := equiv_fin_two hB
      obtain ⟨j, rfl⟩ := eA.symm.surjective i
      obtain ⟨x', rfl⟩ : ∃ x', x = SymOperad.map (R := R) eA.symm x' :=
        ⟨SymOperad.map (R := R) eA x, by rw [SymOperad.map_map, Equiv.self_trans_symm,
          SymOperad.map_refl]⟩
      obtain ⟨y', rfl⟩ : ∃ y', y = SymOperad.map (R := R) eB.symm y' :=
        ⟨SymOperad.map (R := R) eB y, by rw [SymOperad.map_map, Equiv.self_trans_symm,
          SymOperad.map_refl]⟩
      have hy' := hy eB
      rw [SymOperad.map_map, Equiv.symm_trans_self, SymOperad.map_refl] at hy'
      rw [SymOperad.comp_map_right, SymOperad.comp_map_left, SymOperad.map_map,
        SymOperad.map_map]
      exact hW (comp_mem_ideal3Of_right j _ x' hy')
    · rw [mem_ideal23Sub_ne (by omega), mem_ideal3Sub]
      exact ⟨fun h => absurd h (by omega), fun f => (not_equiv_fin3 (by omega) f).elim⟩
  · rw [mem_ideal23Sub_ne hB] at hy
    by_cases ht : Fintype.card (Without A i ⊕ B) = 2
    · rw [((mem_ideal3Sub R).1 hy).1 (by omega), map_zero]
      exact Submodule.zero_mem _
    · rw [mem_ideal23Sub_ne ht]
      exact ideal3_comp_right R i x hy

variable (R) in
/-- **The ideal of relators of arity two and of a space of arity three** containing their
relations of arity three. -/
noncomputable def ideal23 (r₂ : Set (FreeBin R G (Fin 2))) (W : Submodule R (FreeBin R G (Fin 3)))
    (hW : ideal3Of R r₂ ≤ W) : SymOperadIdeal R (FreeBin R G) where
  sub A _ _ := ideal23Sub R r₂ W A
  map_mem e _ hx := ideal23_map_mem e hx
  comp_mem_left i _ y hx := ideal23_comp_left hW i y hx
  comp_mem_right i x _ hy := ideal23_comp_right hW i x hy

variable (R) in
/-- **The relations of arity three of a binary quadratic operad**: the relations of arity three of
its relators of arity two, and the relabellings of its relators of arity three. -/
theorem span_sub_three_23 (r₂ : Set (FreeBin R G (Fin 2))) (r₃ : Set (FreeBin R G (Fin 3))) :
    (SymOperadIdeal.span R (rel23 r₂ r₃)).sub (Fin 3)
      = ideal3Of R r₂ ⊔ Submodule.span R (orbit3 R r₃) := by
  apply le_antisymm
  · have hle : SymOperadIdeal.span R (rel23 r₂ r₃)
        ≤ ideal23 R r₂ (ideal3Of R r₂ ⊔ Submodule.span R (orbit3 R r₃)) le_sup_left := by
      rw [SymOperadIdeal.span_le]
      intro n x hx
      rcases n with _ | _ | _ | _ | n
      · exact absurd hx (by simp [rel23])
      · exact absurd hx (by simp [rel23])
      · show x ∈ ideal23Sub R r₂ (ideal3Of R r₂ ⊔ Submodule.span R (orbit3 R r₃)) (Fin 2)
        rw [mem_ideal23Sub_two (by simp)]
        exact fun f => Submodule.subset_span ⟨f, x, hx, rfl⟩
      · show x ∈ ideal23Sub R r₂ (ideal3Of R r₂ ⊔ Submodule.span R (orbit3 R r₃)) (Fin 3)
        rw [mem_ideal23Sub_ne (by simp), mem_ideal3Sub]
        exact ⟨fun h => absurd h (by simp), fun f =>
          Submodule.mem_sup_right (Submodule.subset_span ⟨f, x, hx, rfl⟩)⟩
      · exact absurd hx (by simp [rel23])
    intro x hx
    have h := hle (Fin 3) hx
    change x ∈ ideal23Sub R r₂ (ideal3Of R r₂ ⊔ Submodule.span R (orbit3 R r₃)) (Fin 3) at h
    rw [mem_ideal23Sub_ne (by simp), mem_ideal3Sub] at h
    have := h.2 (Equiv.refl _)
    rwa [SymOperad.map_refl] at this
  · refine sup_le ?_ ?_
    · rw [ideal3Of, Submodule.span_le]
      rintro _ ⟨i, f, a, b, hab, rfl⟩
      rcases hab with ha | hb
      · exact (SymOperadIdeal.span R _).map_mem f
          ((SymOperadIdeal.span R _).comp_mem_left i b (SymOperadIdeal.subset_span 2 ha))
      · exact (SymOperadIdeal.span R _).map_mem f
          ((SymOperadIdeal.span R _).comp_mem_right i a (SymOperadIdeal.subset_span 2 hb))
    · rw [Submodule.span_le]
      rintro _ ⟨τ, y, hy, rfl⟩
      exact (SymOperadIdeal.span R _).map_mem τ (SymOperadIdeal.subset_span 3 hy)

/-- **Comparing presentations**: relators of arity two among the relabellings of others, and
relators of arity three among the relations of arity three of the others, generate a smaller
ideal. -/
theorem span_le_23 {r₂ r₂' : Set (FreeBin R G (Fin 2))} {r₃ r₃' : Set (FreeBin R G (Fin 3))}
    (h2 : ∀ x ∈ r₂, x ∈ Submodule.span R (orbit2 R r₂'))
    (h3 : ∀ x ∈ r₃, x ∈ ideal3Of R r₂' ⊔ Submodule.span R (orbit3 R r₃')) :
    SymOperadIdeal.span R (rel23 r₂ r₃) ≤ SymOperadIdeal.span R (rel23 r₂' r₃') := by
  rw [SymOperadIdeal.span_le]
  intro n x hx
  rcases n with _ | _ | _ | _ | n
  · exact absurd hx (by simp [rel23])
  · exact absurd hx (by simp [rel23])
  · have hle : Submodule.span R (orbit2 R r₂')
        ≤ (SymOperadIdeal.span R (rel23 r₂' r₃')).sub (Fin 2) := by
      rw [Submodule.span_le]
      rintro _ ⟨τ, y, hy, rfl⟩
      exact (SymOperadIdeal.span R _).map_mem τ (SymOperadIdeal.subset_span 2 hy)
    exact hle (h2 x hx)
  · rw [span_sub_three_23]
    exact h3 x hx
  · exact absurd hx (by simp [rel23])

end Ideal23

/-! ## The monomials of arity two -/

section Basis2

variable (G) in
/-- **The monomials of arity two**: a generator and the relabelling of its inputs. -/
abbrev Mono2 := G × Equiv.Perm (Fin 2)

/-- The operation of the free set operad of a monomial of arity two. -/
def mono2Set (m : Mono2 G) : FreeSet (BinGen G) (Fin 2) := Pres.mk (.map m.2 (gen m.1))

/-- The word of a monomial of arity two. -/
def word2 (m : Mono2 G) : LTree G := .node m.1 (.leaf (m.2 0)) (.leaf (m.2 1))

lemma word2_injective : Function.Injective (word2 (G := G)) := by
  rintro ⟨g, σ⟩ ⟨g', σ'⟩ h
  simp only [word2, LTree.node.injEq, LTree.leaf.injEq] at h
  obtain ⟨rfl, h0, h1⟩ := h
  refine Prod.ext rfl (Equiv.ext fun k => ?_)
  fin_cases k
  · exact Fin.ext h0
  · exact Fin.ext h1

lemma binHom_bin2_word (m : Mono2 G) :
    (binHom (fun g => bilinOp (graftL R g))).app (Fin 2) (bin2 m.1 m.2)
      (fun k => Finsupp.single (.leaf k) 1) = Finsupp.single (word2 m) 1 := by
  rw [binHom_bin2, bilinOp_apply, graftL_single]
  rfl

/-- **The monomials of arity two are linearly independent.** -/
theorem mono2_independent : LinearIndependent R fun m : Mono2 G => bin2 (R := R) m.1 m.2 := by
  classical
  rw [linearIndependent_iff']
  intro s c hc m hm
  have := congrArg (fun x => (binHom (fun g => bilinOp (graftL R g))).app (Fin 2) x
    (fun k => Finsupp.single (.leaf k) 1)) hc
  simp only [map_sum, map_smul, MultilinearMap.coe_sum, MultilinearMap.smul_apply,
    Finset.sum_apply, binHom_bin2_word, map_zero, MultilinearMap.zero_apply] at this
  have h2 := congrArg (fun f : Words G R => f (word2 m)) this
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply,
    smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply] at h2
  rw [Finset.sum_eq_single m] at h2
  · simpa using h2
  · intro b _ hb
    rw [Finsupp.single_apply, if_neg (fun h => hb (word2_injective h)), mul_zero]
  · intro hm'
    exact absurd hm hm'

variable [Fintype G] [DecidableEq G]

/-- **There are `|G|` trees of arity two.** -/
lemma card_ofArity_two : Fintype.card (BTree.OfArity G 2) = Fintype.card G := by
  refine Fintype.card_congr (Equiv.ofBijective (fun t => ?_) ⟨?_, ?_⟩)
  · exact match t with
    | ⟨.node g _ _, _⟩ => g
    | ⟨.leaf, h⟩ => absurd h (by simp)
  · rintro ⟨_ | ⟨g, a, b⟩, ha⟩ ⟨_ | ⟨g', a', b'⟩, hb⟩ h
    · simp at ha
    · simp at ha
    · simp at hb
    · simp only [BTree.arity_node] at ha hb
      have := BTree.arity_pos a
      have := BTree.arity_pos b
      have := BTree.arity_pos a'
      have := BTree.arity_pos b'
      obtain rfl : g = g' := h
      apply Subtype.ext
      show BTree.node g a b = BTree.node g a' b'
      rw [BTree.eq_leaf_of_arity_eq_one (by omega : a.arity = 1),
        BTree.eq_leaf_of_arity_eq_one (by omega : b.arity = 1),
        BTree.eq_leaf_of_arity_eq_one (by omega : a'.arity = 1),
        BTree.eq_leaf_of_arity_eq_one (by omega : b'.arity = 1)]
  · intro g
    exact ⟨⟨.node g .leaf .leaf, rfl⟩, rfl⟩

/-- **There are `2 |G|` operations of arity two** in the free set operad. -/
lemma natCard_freeSet_two : Nat.card (FreeSet (BinGen G) (Fin 2)) = 2 * Fintype.card G := by
  rw [Nat.card_congr (regIso.equiv (Fin 2)), card_reg, Fintype.card_fin, Nat.card_eq_fintype_card,
    card_ofArity_two]
  rfl

/-- **Every operation of arity two of the free set operad is a monomial**, in exactly one way. -/
theorem mono2Set_bijective : Function.Bijective (mono2Set (G := G)) := by
  have hinj : Function.Injective (mono2Set (G := G)) := fun m m' h =>
    (mono2_independent (G := G) ℤ).injective (by
      show Finsupp.single (mono2Set m) (1 : ℤ) = Finsupp.single (mono2Set m') 1
      rw [h])
  haveI := finite_reg (BTree.OfArity G) (Fin 2)
  haveI : Finite (FreeSet (BinGen G) (Fin 2)) := Finite.of_equiv _ (regIso.equiv (Fin 2)).symm
  refine hinj.bijective_of_nat_card_le ?_
  rw [natCard_freeSet_two, Nat.card_eq_fintype_card]
  simp only [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]
  rw [show (2 : ℕ).factorial = 2 from rfl, mul_comm]

/-- **The monomials of arity two span.** -/
theorem span_mono2 :
    Submodule.span R (Set.range fun m : Mono2 G => bin2 (R := R) m.1 m.2) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | single a r =>
    obtain ⟨m, rfl⟩ := mono2Set_bijective.2 a
    have : Finsupp.single (mono2Set m) r = r • bin2 (R := R) m.1 m.2 := by
      rw [bin2, Finsupp.smul_single, smul_eq_mul, mul_one]
      rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

/-- **The basis of monomials** of arity two. -/
noncomputable def basis2 : Module.Basis (Mono2 G) R (FreeBin R G (Fin 2)) :=
  Module.Basis.mk (mono2_independent R) (span_mono2 R).ge

@[simp] lemma basis2_apply (m : Mono2 G) : basis2 R m = bin2 m.1 m.2 := by
  simp [basis2]

/-- **The signature twist in arity two**: each monomial scaled by the signature of its
relabelling. It exchanges commutativity and anticommutativity. -/
noncomputable def twist2 : FreeBin R G (Fin 2) →ₗ[R] FreeBin R G (Fin 2) :=
  (basis2 R).constr R fun m => ((Equiv.Perm.sign m.2 : ℤ) : R) • bin2 m.1 m.2

lemma twist2_bin2 (g : G) (σ : Equiv.Perm (Fin 2)) :
    twist2 R (bin2 g σ) = ((Equiv.Perm.sign σ : ℤ) : R) • bin2 g σ := by
  have h := (basis2 R).constr_basis R
    (fun m : Mono2 G => ((Equiv.Perm.sign m.2 : ℤ) : R) • bin2 (R := R) m.1 m.2) (g, σ)
  rw [basis2_apply] at h
  exact h

end Basis2

/-! ## Composites of monomials of arity two, in the free model -/

section Composites

/-- **Evaluation in the free model**, in arity three: the labelled trees of an element. -/
noncomputable def evalW : FreeBin R G (Fin 3) →ₗ[R] Words G R where
  toFun x := (binHom (fun g => bilinOp (graftL R g))).app (Fin 3) x
    (fun k => Finsupp.single (.leaf k) 1)
  map_add' x y := by simp only [map_add, MultilinearMap.add_apply]
  map_smul' c x := by simp only [map_smul, MultilinearMap.smul_apply, RingHom.id_apply]

lemma evalW_mono3 (m : Mono3 G) : evalW R (mono3 R m) = Finsupp.single (word m) 1 :=
  binHom_mono3_word R m

/-- The value of a composite in the free model. -/
lemma evalW_comp (i : Fin 2) (f : Without (Fin 2) i ⊕ Fin 2 ≃ Fin 3) (a b : FreeBin R G (Fin 2)) :
    evalW R (SymOperad.map (R := R) f (SymOperad.comp (R := R) i a b))
      = (binHom (fun g => bilinOp (graftL R g))).act a
          (feed i (fun c => Finsupp.single (.leaf (f c)) 1)
            ((binHom (fun g => bilinOp (graftL R g))).act b
              fun k => Finsupp.single (.leaf (f (Sum.inr k))) 1)) := by
  show (binHom (fun g => bilinOp (graftL R g))).act
    (SymOperad.map (R := R) f (SymOperad.comp (R := R) i a b)) _ = _
  rw [SymAlgebra.act_map, SymAlgebra.act_comp]

lemma act_bin2 (g : G) (σ : Equiv.Perm (Fin 2)) (v : Fin 2 → Words G R) :
    (binHom (fun g => bilinOp (graftL R g))).act (bin2 g σ) v = graftL R g (v (σ 0)) (v (σ 1)) := by
  show (binHom (fun g => bilinOp (graftL R g))).app (Fin 2) (bin2 g σ) v = _
  rw [binHom_bin2, bilinOp_apply]

variable [Fintype G] [DecidableEq G]

/-- **Elements of arity three are determined by their value in the free model.** -/
theorem evalW_injective : Function.Injective (evalW R (G := G)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  apply (basis3 R).repr.injective
  ext m
  rw [map_zero, Finsupp.zero_apply]
  have h := congrArg (fun f : Words G R => f (word m)) hx
  rw [← (basis3 R).sum_repr x] at h
  simp only [map_sum, map_smul, basis3_apply, evalW_mono3, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finsupp.coe_zero,
    Pi.zero_apply] at h
  rw [Finset.sum_eq_single m] at h
  · simpa using h
  · intro b _ hb
    rw [Finsupp.single_apply, if_neg (fun h => hb (word_injective h)), mul_zero]
  · intro hm
    exact absurd (Finset.mem_univ m) hm

omit [Fintype G] [DecidableEq G] in
lemma perm2_cases (σ : Equiv.Perm (Fin 2)) : σ = 1 ∨ σ = Equiv.swap 0 1 := by
  revert σ
  decide

/-- **The inputs of a composite at the first input**: the inserted ones, then the other. -/
noncomputable def e0 : Without (Fin 2) 0 ⊕ Fin 2 ≃ Fin 3 :=
  Equiv.ofBijective (fun c => match c with
    | .inl _ => 2
    | .inr k => k.castSucc) (by decide)

/-- **The inputs of a composite at the second input**: the other one, then the inserted ones. -/
noncomputable def e1 : Without (Fin 2) 1 ⊕ Fin 2 ≃ Fin 3 :=
  Equiv.ofBijective (fun c => match c with
    | .inl _ => 0
    | .inr k => k.succ) (by decide)

/-- **Composing at the first input**: `g (x_{σ0}, x_{σ1})` with `h (y_{τ0}, y_{τ1})` in `x₀`, the
inputs ordered as `y₀, y₁, x₁`. -/
lemma comp_e0_bin2 (g h : G) (σ τ : Equiv.Perm (Fin 2)) :
    SymOperad.map (R := R) e0 (SymOperad.comp (R := R) 0 (bin2 g σ) (bin2 h τ)) =
      if σ = 1 then binL (R := R) g h (if τ = 1 then 1 else perm3 1 0 2)
      else binR (R := R) g h (if τ = 1 then perm3 2 0 1 else perm3 2 1 0) := by
  apply evalW_injective R
  rw [evalW_comp, act_bin2, act_bin2]
  rcases perm2_cases σ with rfl | rfl <;> rcases perm2_cases τ with rfl | rfl <;>
    simp [← mono3_false, ← mono3_true, evalW_mono3, feed, e0, word, graftL_single]

/-- **Composing at the second input**: `g (x_{σ0}, x_{σ1})` with `h (y_{τ0}, y_{τ1})` in `x₁`,
the inputs ordered as `x₀, y₀, y₁`. -/
lemma comp_e1_bin2 (g h : G) (σ τ : Equiv.Perm (Fin 2)) :
    SymOperad.map (R := R) e1 (SymOperad.comp (R := R) 1 (bin2 g σ) (bin2 h τ)) =
      if σ = 1 then binR (R := R) g h (if τ = 1 then 1 else perm3 0 2 1)
      else binL (R := R) g h (if τ = 1 then perm3 1 2 0 else perm3 2 1 0) := by
  apply evalW_injective R
  rw [evalW_comp, act_bin2, act_bin2]
  rcases perm2_cases σ with rfl | rfl <;> rcases perm2_cases τ with rfl | rfl <;>
    simp [← mono3_false, ← mono3_true, evalW_mono3, feed, e1, word, graftL_single]

/-- **The relations of arity three of relators of arity two are spanned by the relabellings of
their composites with the monomials**, at either input and on either side. -/
theorem ideal3Of_le {r : Set (FreeBin R G (Fin 2))} {S : Submodule R (FreeBin R G (Fin 3))}
    (hS : ∀ (τ : Equiv.Perm (Fin 3)) x, x ∈ S → SymOperad.map (R := R) τ x ∈ S)
    (h : ∀ a ∈ r, ∀ (g : G) (σ : Equiv.Perm (Fin 2)),
      SymOperad.map (R := R) e0 (SymOperad.comp (R := R) 0 a (bin2 g σ)) ∈ S ∧
      SymOperad.map (R := R) e1 (SymOperad.comp (R := R) 1 a (bin2 g σ)) ∈ S ∧
      SymOperad.map (R := R) e0 (SymOperad.comp (R := R) 0 (bin2 g σ) a) ∈ S ∧
      SymOperad.map (R := R) e1 (SymOperad.comp (R := R) 1 (bin2 g σ) a) ∈ S) :
    ideal3Of R r ≤ S := by
  have hspan : ∀ P : FreeBin R G (Fin 2) → Prop, P 0 → (∀ x y, P x → P y → P (x + y)) →
      (∀ (c : R) x, P x → P (c • x)) → (∀ (g : G) σ, P (bin2 g σ)) → ∀ x, P x := by
    intro P h0 hadd hsmul hb x
    have hx : x ∈ Submodule.span R (Set.range fun m : Mono2 G => bin2 (R := R) m.1 m.2) := by
      rw [span_mono2]
      trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, rfl⟩ := hy
      exact hb m.1 m.2
    | zero => exact h0
    | add y z _ _ hy hz => exact hadd y z hy hz
    | smul c y _ hy => exact hsmul c y hy
  rw [ideal3Of, Submodule.span_le]
  rintro _ ⟨i, f, a, b, hab, rfl⟩
  rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
  · rw [show SymOperad.map (R := R) f (SymOperad.comp (R := R) 0 a b) =
        SymOperad.map (R := R) (e0.symm.trans f)
          (SymOperad.map (R := R) e0 (SymOperad.comp (R := R) 0 a b)) by
      rw [SymOperad.map_map, ← Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.refl_trans]]
    refine hS _ _ ?_
    rcases hab with ha | hb
    · refine hspan (fun y => SymOperad.map (R := R) e0 (SymOperad.comp (R := R) 0 a y) ∈ S)
        (by simp) (fun x y hx hy => ?_) (fun c x hx => ?_) (fun g σ => (h a ha g σ).1) b
      · dsimp only at hx hy ⊢
        rw [map_add, map_add]; exact add_mem hx hy
      · dsimp only at hx ⊢
        rw [map_smul, map_smul]; exact Submodule.smul_mem _ c hx
    · refine hspan (fun x => SymOperad.map (R := R) e0 (SymOperad.comp (R := R) 0 x b) ∈ S)
        (by simp) (fun x y hx hy => ?_) (fun c x hx => ?_) (fun g σ => (h b hb g σ).2.2.1) a
      · dsimp only at hx hy ⊢
        rw [map_add, LinearMap.add_apply, map_add]; exact add_mem hx hy
      · dsimp only at hx ⊢
        rw [map_smul, LinearMap.smul_apply, map_smul]; exact Submodule.smul_mem _ c hx
  · rw [show SymOperad.map (R := R) f (SymOperad.comp (R := R) 1 a b) =
        SymOperad.map (R := R) (e1.symm.trans f)
          (SymOperad.map (R := R) e1 (SymOperad.comp (R := R) 1 a b)) by
      rw [SymOperad.map_map, ← Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.refl_trans]]
    refine hS _ _ ?_
    rcases hab with ha | hb
    · refine hspan (fun y => SymOperad.map (R := R) e1 (SymOperad.comp (R := R) 1 a y) ∈ S)
        (by simp) (fun x y hx hy => ?_) (fun c x hx => ?_) (fun g σ => (h a ha g σ).2.1) b
      · dsimp only at hx hy ⊢
        rw [map_add, map_add]; exact add_mem hx hy
      · dsimp only at hx ⊢
        rw [map_smul, map_smul]; exact Submodule.smul_mem _ c hx
    · refine hspan (fun x => SymOperad.map (R := R) e1 (SymOperad.comp (R := R) 1 x b) ∈ S)
        (by simp) (fun x y hx hy => ?_) (fun c x hx => ?_) (fun g σ => (h b hb g σ).2.2.2) a
      · dsimp only at hx hy ⊢
        rw [map_add, LinearMap.add_apply, map_add]; exact add_mem hx hy
      · dsimp only at hx ⊢
        rw [map_smul, LinearMap.smul_apply, map_smul]; exact Submodule.smul_mem _ c hx

end Composites

/-! ## The Koszul dual -/

section Dual

variable (K : Type u) [Field K] [Fintype G] [DecidableEq G]

/-- **The Koszul dual relations** of the operad presented by `r₂` and `r₃`: the orthogonal, for
the Koszul pairing, of all its relations of arity three. -/
noncomputable def dualRel23 (r₂ : Set (FreeBin K G (Fin 2))) (r₃ : Set (FreeBin K G (Fin 3))) :
    Submodule K (FreeBin K G (Fin 3)) :=
  dualRel K ((ideal3Of K r₂ ⊔ Submodule.span K (orbit3 K r₃) : Submodule K _) :
    Set (FreeBin K G (Fin 3)))

/-- **The Koszul dual of a binary quadratic operad** presented by relators `r₂` of arity two and
`r₃` of arity three: the relators of arity two twisted by the signature, a commutative generator
becoming anticommutative and conversely, and the dual relations in arity three. -/
abbrev BinPres.dual23 (r₂ : Set (FreeBin K G (Fin 2))) (r₃ : Set (FreeBin K G (Fin 3))) :=
  BinPres K (twist2 K '' r₂) (dualRel23 K r₂ r₃ : Set (FreeBin K G (Fin 3)))

omit [Fintype G] [DecidableEq G] in
lemma ideal3Of_empty : ideal3Of K (∅ : Set (FreeBin K G (Fin 2))) = ⊥ := by
  rw [ideal3Of, Submodule.span_eq_bot]
  rintro _ ⟨i, f, a, b, hab, rfl⟩
  simp at hab

/-- **Without relators of arity two, this is the Koszul dual of `Operad.BinaryKoszul`.** -/
theorem dualRel23_empty (r₃ : Set (FreeBin K G (Fin 3))) :
    dualRel23 K ∅ r₃ = dualRel K r₃ := by
  rw [dualRel23, ideal3Of_empty, bot_sup_eq, dualRel, dualRel,
    span_orbit3_eq K fun τ x hx => map_mem_span_orbit3 K τ hx]

theorem BinPres.dual23_empty (r₃ : Set (FreeBin K G (Fin 3))) :
    BinPres.dual23 K ∅ r₃ = BinPres.dual K r₃ := by
  rw [BinPres.dual23, Set.image_empty, dualRel23_empty]

end Dual

/-! ## `Com^! = Lie` -/

section ComLie

variable (K : Type u) [Field K]

/-- **The sum of the coordinates** in the monomials of arity three. -/
noncomputable def sumCoord : FreeBin K Unit (Fin 3) →ₗ[K] K :=
  (basis3 K).constr K fun _ => 1

lemma sumCoord_mono3 (m : Mono3 Unit) : sumCoord K (mono3 K m) = 1 := by
  rw [sumCoord, ← basis3_apply, Module.Basis.constr_basis]

lemma sumCoord_map (τ : Equiv.Perm (Fin 3)) (x : FreeBin K Unit (Fin 3)) :
    sumCoord K (SymOperad.map (R := K) τ x) = sumCoord K x := by
  have : sumCoord K ∘ₗ SymOperad.map (R := K) τ = sumCoord K :=
    (basis3 K).ext fun m => by
      simp only [LinearMap.coe_comp, Function.comp_apply, basis3_apply, map_mono3,
        sumCoord_mono3]
  exact congrArg (fun f => f x) this

/-- The six relabellings of three inputs, by name. -/
lemma perm3_enum (ρ : Equiv.Perm (Fin 3)) : ρ = 1 ∨ ρ = perm3 2 0 1 ∨ ρ = perm3 1 2 0 ∨
    ρ = perm3 1 0 2 ∨ ρ = perm3 0 2 1 ∨ ρ = perm3 2 1 0 := by
  revert ρ
  decide

lemma sign_perm3_201 : Equiv.Perm.sign (perm3 2 0 1) = 1 := by decide
lemma sign_perm3_120 : Equiv.Perm.sign (perm3 1 2 0) = 1 := by decide
lemma sign_perm3_102 : Equiv.Perm.sign (perm3 1 0 2) = -1 := by decide
lemma sign_perm3_210 : Equiv.Perm.sign (perm3 2 1 0) = -1 := by decide

/-- **The antisymmetrized associator**
`Σ_σ sgn σ ((x_{σ0} x_{σ1}) x_{σ2} - x_{σ0} (x_{σ1} x_{σ2}))`. -/
noncomputable def asym3 : FreeBin K Unit (Fin 3) :=
  (cL K 1 - cR K 1) + (cL K (perm3 2 0 1) - cR K (perm3 2 0 1))
    + (cL K (perm3 1 2 0) - cR K (perm3 1 2 0)) - (cL K (perm3 1 0 2) - cR K (perm3 1 0 2))
    - (cL K (perm3 0 2 1) - cR K (perm3 0 2 1)) - (cL K (perm3 2 1 0) - cR K (perm3 2 1 0))

/-- **Each monomial pairs to one with the antisymmetrized associator.** -/
lemma pair3_asym3 (x : FreeBin K Unit (Fin 3)) : pair3 Unit K x (asym3 K) = sumCoord K x := by
  have : (pair3 Unit K).flip (asym3 K) = sumCoord K := by
    refine (basis3 K).ext fun m => ?_
    rw [basis3_apply, sumCoord_mono3]
    show pair3 Unit K (mono3 K m) (asym3 K) = 1
    obtain ⟨b, u, v, ρ⟩ := m
    cases u
    cases v
    rcases perm3_enum ρ with rfl | rfl | rfl | rfl | rfl | rfl <;> cases b <;>
      simp (config := { decide := true }) [asym3, pair3_mono3, sign3, map_add, map_sub,
        sign_perm3_201, sign_perm3_120, sign_perm3_102, sign_perm3_021, sign_perm3_210]
  exact congrArg (fun f => f x) this

/-- The relations of arity three of `Com`. -/
noncomputable abbrev comRel3 : Submodule K (FreeBin K Unit (Fin 3)) :=
  ideal3Of K {BinRel.comm K ()} ⊔ Submodule.span K (orbit3 K {BinRel.assoc K ()})

lemma comp_comm_left0 (σ : Equiv.Perm (Fin 2)) :
    SymOperad.map (R := K) e0 (SymOperad.comp (R := K) 0 (BinRel.comm K ()) (bin2 () σ)) =
      binL (R := K) () () (if σ = 1 then 1 else perm3 1 0 2)
        - binR (R := K) () () (if σ = 1 then perm3 2 0 1 else perm3 2 1 0) := by
  rw [BinRel.comm, map_sub, LinearMap.sub_apply, map_sub, comp_e0_bin2, comp_e0_bin2]
  simp

lemma comp_comm_left1 (σ : Equiv.Perm (Fin 2)) :
    SymOperad.map (R := K) e1 (SymOperad.comp (R := K) 1 (BinRel.comm K ()) (bin2 () σ)) =
      binR (R := K) () () (if σ = 1 then 1 else perm3 0 2 1)
        - binL (R := K) () () (if σ = 1 then perm3 1 2 0 else perm3 2 1 0) := by
  rw [BinRel.comm, map_sub, LinearMap.sub_apply, map_sub, comp_e1_bin2, comp_e1_bin2]
  simp

lemma comp_comm_right0 (σ : Equiv.Perm (Fin 2)) :
    SymOperad.map (R := K) e0 (SymOperad.comp (R := K) 0 (bin2 () σ) (BinRel.comm K ())) =
      if σ = 1 then binL (R := K) () () 1 - binL (R := K) () () (perm3 1 0 2)
      else binR (R := K) () () (perm3 2 0 1) - binR (R := K) () () (perm3 2 1 0) := by
  rw [BinRel.comm, map_sub, map_sub, comp_e0_bin2, comp_e0_bin2]
  rcases perm2_cases σ with rfl | rfl <;> simp

lemma comp_comm_right1 (σ : Equiv.Perm (Fin 2)) :
    SymOperad.map (R := K) e1 (SymOperad.comp (R := K) 1 (bin2 () σ) (BinRel.comm K ())) =
      if σ = 1 then binR (R := K) () () 1 - binR (R := K) () () (perm3 0 2 1)
      else binL (R := K) () () (perm3 1 2 0) - binL (R := K) () () (perm3 2 1 0) := by
  rw [BinRel.comm, map_sub, map_sub, comp_e1_bin2, comp_e1_bin2]
  rcases perm2_cases σ with rfl | rfl <;> simp

lemma sumCoord_binL (σ : Equiv.Perm (Fin 3)) : sumCoord K (binL (R := K) () () σ) = 1 := by
  rw [← mono3_false, sumCoord_mono3]

lemma sumCoord_binR (σ : Equiv.Perm (Fin 3)) : sumCoord K (binR (R := K) () () σ) = 1 := by
  rw [← mono3_true, sumCoord_mono3]

/-- **The relations of `Com` have coordinates summing to zero.** -/
lemma sumCoord_eq_zero {x : FreeBin K Unit (Fin 3)} (hx : x ∈ comRel3 K) : sumCoord K x = 0 := by
  have h1 : ideal3Of K {BinRel.comm K ()} ≤ LinearMap.ker (sumCoord K) := by
    refine ideal3Of_le K (fun τ x hx => ?_) fun a ha g σ => ?_
    · rw [LinearMap.mem_ker, sumCoord_map]
      exact hx
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      cases g
      simp only [LinearMap.mem_ker, comp_comm_left0, comp_comm_left1, comp_comm_right0,
        comp_comm_right1, map_sub, sumCoord_binL, sumCoord_binR, sub_self, and_self,
        apply_ite (sumCoord K), ite_self]
  have h2 : Submodule.span K (orbit3 K {BinRel.assoc K ()}) ≤ LinearMap.ker (sumCoord K) := by
    rw [Submodule.span_le]
    rintro _ ⟨τ, y, hy, rfl⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [SetLike.mem_coe, LinearMap.mem_ker, sumCoord_map, BinRel.assoc, map_sub, sumCoord_binL,
      sumCoord_binR, sub_self]
  exact (sup_le h1 h2) hx

lemma mem_comRel3_A (ρ : Equiv.Perm (Fin 3)) : cL K ρ - cR K ρ ∈ comRel3 K :=
  Submodule.mem_sup_right (Submodule.subset_span ⟨ρ, _, rfl, (map_assoc K ρ).symm⟩)

lemma mem_comRel3_P (ρ : Equiv.Perm (Fin 3)) :
    cL K ρ - cR K (ρ * perm3 2 0 1) ∈ comRel3 K := by
  have h := ideal3Of_map_mem ρ (Submodule.subset_span (R := K)
    ⟨0, e0, BinRel.comm K (), bin2 () 1, Or.inl rfl, rfl⟩ :
      SymOperad.map (R := K) e0 (SymOperad.comp (R := K) 0 (BinRel.comm K ()) (bin2 () 1))
        ∈ ideal3Of K {BinRel.comm K ()})
  rw [comp_comm_left0, map_sub, map_binL, map_binR] at h
  simpa using Submodule.mem_sup_left h

lemma mem_comRel3_Q (ρ : Equiv.Perm (Fin 3)) :
    cL K ρ - cL K (ρ * perm3 1 0 2) ∈ comRel3 K := by
  have h := ideal3Of_map_mem ρ (Submodule.subset_span (R := K)
    ⟨0, e0, bin2 () 1, BinRel.comm K (), Or.inr rfl, rfl⟩ :
      SymOperad.map (R := K) e0 (SymOperad.comp (R := K) 0 (bin2 () 1) (BinRel.comm K ()))
        ∈ ideal3Of K {BinRel.comm K ()})
  rw [comp_comm_right0, if_pos rfl, map_sub, map_binL, map_binL] at h
  simpa using Submodule.mem_sup_left h

/-- **Every left comb is congruent to `(x₀x₁)x₂` modulo the relations of `Com`.** -/
lemma mem_comRel3_L (ρ : Equiv.Perm (Fin 3)) : cL K ρ - cL K 1 ∈ comRel3 K := by
  have hκ : cL K (perm3 2 0 1) - cL K 1 ∈ comRel3 K := by
    have := sub_mem (mem_comRel3_A K (perm3 2 0 1)) (mem_comRel3_P K 1)
    rwa [one_mul, sub_sub_sub_cancel_right] at this
  have hκ2 : cL K (perm3 1 2 0) - cL K 1 ∈ comRel3 K := by
    have h := sub_mem (mem_comRel3_A K (perm3 1 2 0)) (mem_comRel3_P K (perm3 2 0 1))
    rw [show perm3 2 0 1 * perm3 2 0 1 = perm3 1 2 0 by decide, sub_sub_sub_cancel_right] at h
    have := add_mem h hκ
    rwa [sub_add_sub_cancel] at this
  rcases perm3_enum ρ with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [sub_self]
    exact Submodule.zero_mem _
  · exact hκ
  · exact hκ2
  · have := neg_mem (mem_comRel3_Q K 1)
    rwa [one_mul, neg_sub] at this
  · have := add_mem (neg_mem (mem_comRel3_Q K (perm3 2 0 1))) hκ
    rwa [show perm3 2 0 1 * perm3 1 0 2 = perm3 0 2 1 by decide, neg_sub,
      sub_add_sub_cancel] at this
  · have := add_mem (neg_mem (mem_comRel3_Q K (perm3 1 2 0))) hκ2
    rwa [show perm3 1 2 0 * perm3 1 0 2 = perm3 2 1 0 by decide, neg_sub,
      sub_add_sub_cancel] at this

lemma mem_comRel3_R (ρ : Equiv.Perm (Fin 3)) : cR K ρ - cL K 1 ∈ comRel3 K := by
  have := sub_mem (mem_comRel3_L K ρ) (mem_comRel3_A K ρ)
  rwa [sub_sub_sub_cancel_left] at this

/-- **The relations of `Com` in arity three have dimension eleven** (at least): every monomial is
congruent to `(x₀x₁)x₂`. -/
lemma finrank_comRel3 : 11 ≤ Module.finrank K (comRel3 K) := by
  classical
  have h := le_finrank_of_private K (W := comRel3 K)
    (fun i : {m : Mono3 Unit // m ≠ (false, (), (), 1)} => mono3 K i.1 - cL K 1)
    (fun i => by
      obtain ⟨⟨b, u, v, ρ⟩, -⟩ := i
      cases u
      cases v
      cases b
      · exact mem_comRel3_L K ρ
      · exact mem_comRel3_R K ρ)
    (fun i => i.1) (fun i j => by
      rw [map_sub, Finsupp.sub_apply, repr_mono3, repr_mono3, if_neg (Ne.symm i.2), sub_zero]
      constructor
      · intro h
        by_contra hji
        exact h (if_neg fun h' => hji (Subtype.ext h'))
      · rintro rfl
        simp)
  have hc : Fintype.card {m : Mono3 Unit // m ≠ (false, (), (), 1)} = 11 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    simp [Fintype.card_perm, Nat.factorial]
  omega

lemma repr_asym3_one : (basis3 K).repr (asym3 K) (false, (), (), 1) = 1 := by
  simp (config := { decide := true }) [asym3, repr_mono3]

/-- **The Koszul dual relations of `Com`** are spanned by the antisymmetrized associator. -/
theorem dualRel23_com :
    dualRel23 K {BinRel.comm K ()} {BinRel.assoc K ()}
      = Submodule.span K (orbit3 K {asym3 K}) := by
  have hv := le_finrank_of_private K (W := Submodule.span K (orbit3 K {asym3 K}))
    (fun _ : Unit => asym3 K) (fun _ => by
      have := mem_orbit3 K (Set.mem_singleton (asym3 K)) 1
      rwa [show (1 : Equiv.Perm (Fin 3)) = Equiv.refl _ from rfl, SymOperad.map_refl] at this)
    (fun _ => (false, (), (), 1)) (fun i j => by
      rw [repr_asym3_one]
      simp)
  have hX : comRel3 K ≤ Submodule.span K (orbit3 K (comRel3 K : Set (FreeBin K Unit (Fin 3)))) :=
    fun x hx => Submodule.subset_span ⟨1, x, hx, by
      rw [show (1 : Equiv.Perm (Fin 3)) = Equiv.refl _ from rfl, SymOperad.map_refl]⟩
  have hdim := Submodule.finrank_mono hX
  have h11 := finrank_comRel3 K
  refine (dualRel_eq_of_orthogonal K (r := (comRel3 K : Set (FreeBin K Unit (Fin 3))))
    (s := {asym3 K}) (fun x hx y hy σ τ => ?_) ?_).1
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    have hmap : SymOperad.map (R := K) τ y
        = SymOperad.map (R := K) σ (SymOperad.map (R := K) (σ⁻¹ * τ) y) := by
      rw [SymOperad.map_map]
      congr 1
      rw [← Equiv.Perm.mul_def, mul_inv_cancel_left]
    rw [hmap, pair3_map, pair3_asym3, sumCoord_map, sumCoord_eq_zero K hy, mul_zero]
  · simp only [Fintype.card_unit] at hv ⊢
    omega

lemma twist2_comm : twist2 K (BinRel.comm K ()) = BinRel.antisymm K () := by
  rw [BinRel.comm, BinRel.antisymm, map_sub, twist2_bin2, twist2_bin2,
    Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1)]
  simp

/-- The relations of arity three of `Lie`. -/
noncomputable abbrev lieRel3 : Submodule K (FreeBin K Unit (Fin 3)) :=
  ideal3Of K {BinRel.antisymm K ()} ⊔ Submodule.span K (orbit3 K {BinRel.jacobi K ()})

lemma mem_lie_g1 (ρ : Equiv.Perm (Fin 3)) :
    cL K ρ + cL K (ρ * perm3 1 0 2) ∈ ideal3Of K {BinRel.antisymm K ()} := by
  have h := ideal3Of_map_mem ρ (Submodule.subset_span (R := K)
    ⟨0, e0, bin2 () 1, BinRel.antisymm K (), Or.inr rfl, rfl⟩ :
      SymOperad.map (R := K) e0 (SymOperad.comp (R := K) 0 (bin2 () 1) (BinRel.antisymm K ()))
        ∈ ideal3Of K {BinRel.antisymm K ()})
  rw [BinRel.antisymm, map_add, map_add, comp_e0_bin2, comp_e0_bin2, if_pos rfl, if_pos rfl,
    if_pos rfl, if_neg (by decide), map_add, map_binL, map_binL, mul_one] at h
  exact h

lemma mem_lie_g3 (ρ : Equiv.Perm (Fin 3)) :
    cL K ρ + cR K (ρ * perm3 2 0 1) ∈ ideal3Of K {BinRel.antisymm K ()} := by
  have h := ideal3Of_map_mem ρ (Submodule.subset_span (R := K)
    ⟨0, e0, BinRel.antisymm K (), bin2 () 1, Or.inl rfl, rfl⟩ :
      SymOperad.map (R := K) e0 (SymOperad.comp (R := K) 0 (BinRel.antisymm K ()) (bin2 () 1))
        ∈ ideal3Of K {BinRel.antisymm K ()})
  rw [BinRel.antisymm, map_add, LinearMap.add_apply, map_add, comp_e0_bin2, comp_e0_bin2,
    if_pos rfl, if_pos rfl, if_neg (by decide), if_pos rfl, map_add, map_binL, map_binR,
    mul_one] at h
  exact h

/-- **The antisymmetrized associator is four times the Jacobiator** modulo antisymmetry. -/
lemma asym3_eq : asym3 K = (4 : K) • BinRel.jacobi K ()
    - (2 : K) • ((cL K 1 + cL K (perm3 1 0 2)) + (cL K (perm3 2 0 1) + cL K (perm3 0 2 1))
        + (cL K (perm3 1 2 0) + cL K (perm3 2 1 0)))
    - ((cL K 1 + cR K (perm3 2 0 1)) + (cL K (perm3 2 0 1) + cR K (perm3 1 2 0))
        + (cL K (perm3 1 2 0) + cR K 1) - (cL K (perm3 1 0 2) + cR K (perm3 2 1 0))
        - (cL K (perm3 0 2 1) + cR K (perm3 1 0 2))
        - (cL K (perm3 2 1 0) + cR K (perm3 0 2 1))) := by
  rw [asym3, show BinRel.jacobi K () = cL K 1 + cL K (perm3 1 2 0) + cL K (perm3 2 0 1) from rfl]
  module

lemma g1_mem (ρ σ : Equiv.Perm (Fin 3)) (h : ρ * perm3 1 0 2 = σ) :
    cL K ρ + cL K σ ∈ ideal3Of K {BinRel.antisymm K ()} := h ▸ mem_lie_g1 K ρ

lemma g3_mem (ρ σ : Equiv.Perm (Fin 3)) (h : ρ * perm3 2 0 1 = σ) :
    cL K ρ + cR K σ ∈ ideal3Of K {BinRel.antisymm K ()} := h ▸ mem_lie_g3 K ρ

lemma g1_sum_mem : (cL K 1 + cL K (perm3 1 0 2)) + (cL K (perm3 2 0 1) + cL K (perm3 0 2 1))
    + (cL K (perm3 1 2 0) + cL K (perm3 2 1 0)) ∈ ideal3Of K {BinRel.antisymm K ()} :=
  add_mem (add_mem (g1_mem K _ _ (by decide)) (g1_mem K _ _ (by decide)))
    (g1_mem K _ _ (by decide))

lemma g3_sum_mem : (cL K 1 + cR K (perm3 2 0 1)) + (cL K (perm3 2 0 1) + cR K (perm3 1 2 0))
    + (cL K (perm3 1 2 0) + cR K 1) - (cL K (perm3 1 0 2) + cR K (perm3 2 1 0))
    - (cL K (perm3 0 2 1) + cR K (perm3 1 0 2)) - (cL K (perm3 2 1 0) + cR K (perm3 0 2 1))
      ∈ ideal3Of K {BinRel.antisymm K ()} :=
  sub_mem (sub_mem (sub_mem (add_mem (add_mem (g3_mem K _ _ (by decide))
    (g3_mem K _ _ (by decide))) (g3_mem K _ _ (by decide))) (g3_mem K _ _ (by decide)))
    (g3_mem K _ _ (by decide))) (g3_mem K _ _ (by decide))

lemma asym3_mem_lieRel3 : asym3 K ∈ lieRel3 K := by
  rw [asym3_eq]
  refine sub_mem (sub_mem ?_ (Submodule.mem_sup_left (Submodule.smul_mem _ _ (g1_sum_mem K))))
    (Submodule.mem_sup_left (g3_sum_mem K))
  refine Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, _, rfl, ?_⟩))
  rw [show (1 : Equiv.Perm (Fin 3)) = Equiv.refl _ from rfl, SymOperad.map_refl]

lemma jacobi_mem (h2 : (2 : K) ≠ 0) :
    BinRel.jacobi K ()
      ∈ ideal3Of K {BinRel.antisymm K ()} ⊔ Submodule.span K (orbit3 K {asym3 K}) := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have h4j : (4 : K) • BinRel.jacobi K () = asym3 K
      + (2 : K) • ((cL K 1 + cL K (perm3 1 0 2)) + (cL K (perm3 2 0 1) + cL K (perm3 0 2 1))
        + (cL K (perm3 1 2 0) + cL K (perm3 2 1 0)))
      + ((cL K 1 + cR K (perm3 2 0 1)) + (cL K (perm3 2 0 1) + cR K (perm3 1 2 0))
        + (cL K (perm3 1 2 0) + cR K 1) - (cL K (perm3 1 0 2) + cR K (perm3 2 1 0))
        - (cL K (perm3 0 2 1) + cR K (perm3 1 0 2))
        - (cL K (perm3 2 1 0) + cR K (perm3 0 2 1))) := by
    rw [asym3_eq]
    module
  have hj := congrArg (fun x => (4 : K)⁻¹ • x) h4j
  simp only [inv_smul_smul₀ h4] at hj
  rw [hj]
  refine Submodule.smul_mem _ _ (add_mem (add_mem ?_ (Submodule.mem_sup_left
    (Submodule.smul_mem _ _ (g1_sum_mem K)))) (Submodule.mem_sup_left (g3_sum_mem K)))
  refine Submodule.mem_sup_right (Submodule.subset_span ⟨1, _, rfl, ?_⟩)
  rw [show (1 : Equiv.Perm (Fin 3)) = Equiv.refl _ from rfl, SymOperad.map_refl]

lemma sup_map_mem {W W' : Submodule K (FreeBin K Unit (Fin 3))}
    (hW : ∀ (τ : Equiv.Perm (Fin 3)) x, x ∈ W → SymOperad.map (R := K) τ x ∈ W)
    (hW' : ∀ (τ : Equiv.Perm (Fin 3)) x, x ∈ W' → SymOperad.map (R := K) τ x ∈ W')
    (τ : Equiv.Perm (Fin 3)) {x : FreeBin K Unit (Fin 3)} (hx : x ∈ W ⊔ W') :
    SymOperad.map (R := K) τ x ∈ W ⊔ W' := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add]
  exact add_mem (Submodule.mem_sup_left (hW τ a ha)) (Submodule.mem_sup_right (hW' τ b hb))

/-- **`Com^! = Lie`**, at the level of the presenting ideals. -/
theorem BinPres.dual23_com_eq (h2 : (2 : K) ≠ 0) :
    SymOperadIdeal.span K (rel23 (twist2 K '' {BinRel.comm K ()})
        (dualRel23 K {BinRel.comm K ()} {BinRel.assoc K ()} : Set (FreeBin K Unit (Fin 3))))
      = SymOperadIdeal.span K (rel23 {BinRel.antisymm K ()} {BinRel.jacobi K ()}) := by
  have h2set : twist2 K '' {BinRel.comm K ()} = {BinRel.antisymm K ()} := by
    rw [Set.image_singleton, twist2_comm]
  rw [h2set, dualRel23_com]
  have hself : ∀ x ∈ ({BinRel.antisymm K ()} : Set (FreeBin K Unit (Fin 2))),
      x ∈ Submodule.span K (orbit2 K {BinRel.antisymm K ()}) := fun x hx =>
    Submodule.subset_span ⟨1, x, hx, by
      rw [show (1 : Equiv.Perm (Fin 2)) = Equiv.refl _ from rfl, SymOperad.map_refl]⟩
  apply le_antisymm
  · refine span_le_23 hself fun x hx => ?_
    have hle : Submodule.span K (orbit3 K {asym3 K}) ≤ lieRel3 K := by
      rw [Submodule.span_le]
      rintro _ ⟨τ, y, hy, rfl⟩
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact sup_map_mem K (fun τ x hx => ideal3Of_map_mem τ hx)
        (fun τ x hx => map_mem_span_orbit3 K τ hx) τ (asym3_mem_lieRel3 K)
    exact hle (by simpa using hx)
  · refine span_le_23 hself fun x hx => ?_
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have hle : Submodule.span K (orbit3 K {asym3 K}) ≤ Submodule.span K (orbit3 K
        ((Submodule.span K (orbit3 K {asym3 K}) : Submodule K _) :
          Set (FreeBin K Unit (Fin 3)))) := fun y hy => Submodule.subset_span ⟨1, y, hy, by
      rw [show (1 : Equiv.Perm (Fin 3)) = Equiv.refl _ from rfl, SymOperad.map_refl]⟩
    exact (sup_le_sup_left hle _) (jacobi_mem K h2)

end ComLie

/-- **The commutative operad**, as a binary quadratic operad: a commutative associative
product. -/
abbrev BinCom := BinPres R {BinRel.comm R ()} {BinRel.assoc R ()}

/-- **`Com^! = Lie`: the Koszul dual of the commutative operad is the Lie operad**, over a field
in which `2 ≠ 0`. -/
theorem BinCom.dual (K : Type u) [Field K] (h2 : (2 : K) ≠ 0) :
    BinPres.dual23 K {BinRel.comm K ()} {BinRel.assoc K ()} = Lie K :=
  congrArg SymOperadIdeal.Quot (BinPres.dual23_com_eq K h2)

end FreeBin

end Operad
