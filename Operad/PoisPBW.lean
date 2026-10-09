/-
# The Poisson operad has at most `n!` operations of arity `n`

The Poisson operad is presented by the commutative product `m` and the antisymmetric bracket `b`,
so its underlying shuffle operad is presented by the four generators `m`, `b` and their
transposed versions (`Operad.FreeSet.presEquiv`).

* **Sorting the monomials of arity three** (`PoisDim.toSh_binR_one`, `PoisDim.toSh_binL_one`,
  `PoisDim.toSh_binL_021`): the monomials `g(x₀, h(x₁, x₂))`, `g(h(x₀, x₁), x₂)` and
  `g(h(x₀, x₂), x₁)` of the free operad are the shuffle trees with untransposed generators.
-/
import Operad.PoisModel
import Operad.ShuffleSymPres
import Operad.ShuffleFreeBin
import Operad.BinaryKoszulSym
import Operad.ShuffleAnyOrder
import Mathlib.Data.Set.Finite.List

universe u

namespace Operad

namespace PoisDim

open STree FreeSet FreeSh FreeBin

variable (K : Type u) [Field K]

/-- The shuffle generators: the Poisson generators with a permutation of their inputs. -/
abbrev PE := SGen (BinGen PoisOp)

/-- **A vertex** with an untransposed generator. -/
def nd (g : PoisOp) (x y : STree PE) : STree PE :=
  node (BinGen.op g, (1 : Equiv.Perm (Fin 2))) ![x, y]

/-- `g (x₀, h (x₁, x₂))`. -/
def tR (g h : PoisOp) : STree PE := nd g (leaf 0) (nd h (leaf 1) (leaf 2))

/-- `g (h (x₀, x₁), x₂)`. -/
def tL₁ (g h : PoisOp) : STree PE := nd g (nd h (leaf 0) (leaf 1)) (leaf 2)

/-- `g (h (x₀, x₂), x₁)`. -/
def tL₂ (g h : PoisOp) : STree PE := nd g (nd h (leaf 0) (leaf 2)) (leaf 1)

lemma isShuffle_nd {g : PoisOp} {x y : STree PE} (hx : x.IsShuffle) (hy : y.IsShuffle)
    (hxy : x.first < y.first) : (nd g x y).IsShuffle := by
  refine ⟨by norm_num, fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i
    · exact hx
    · exact hy
  · fin_cases i <;> fin_cases j <;> simp_all

@[simp] lemma first_nd (g : PoisOp) (x y : STree PE) : (nd g x y).first = x.first := by
  rw [nd, first_node _ _ (by norm_num)]
  rfl

@[simp] lemma labels_nd (g : PoisOp) (x y : STree PE) :
    (nd g x y).labels = x.labels + y.labels := by
  rw [nd, labels_node, Fin.sum_univ_two]
  rfl

lemma labels_three :
    ((Finset.range (Fintype.card (Fin 3))).val : Multiset ℕ) = {0} + ({1} + {2}) := by
  rw [Fintype.card_fin]
  rfl

/-- The monomial `g (x₀, h (x₁, x₂))` on the positions. -/
def mR (g h : PoisOp) : SMono PE (Finset.range (Fintype.card (Fin 3))) :=
  ⟨tR g h, isShuffle_nd trivial (isShuffle_nd trivial trivial (by simp)) (by simp),
    by simp only [tR, labels_nd, labels_leaf]; rw [labels_three]⟩

instance : Fintype PoisOp := ⟨{.mul, .bracket}, fun x => by cases x <;> simp⟩

/-- The composite at the second input is a shuffle. -/
lemma isShuffle_e1 : Operad.IsShuffle (1 : Fin 2) e1 where
  mono_left a a' h := by
    have h0 : ∀ x : Without (Fin 2) 1, x.1 = 0 := fun x => by
      rcases x with ⟨v, hv⟩
      fin_cases v
      · rfl
      · exact absurd rfl hv
    rw [show a = a' from Subtype.ext ((h0 a).trans (h0 a').symm)] at h
    exact absurd h (lt_irrefl _)
  mono_right b b' h := by
    show (b.succ : Fin 3) < b'.succ
    exact Fin.succ_lt_succ_iff.2 h
  pointed a b _ := by
    have ha : a.1 = 0 := by
      rcases a with ⟨v, hv⟩
      fin_cases v
      · rfl
      · exact absurd rfl hv
    show a.1 < 1 ↔ (0 : Fin 3) < b.succ
    rw [ha]
    exact ⟨fun _ => Fin.succ_pos _, fun _ => by decide⟩

lemma toSh_bin2_one (g : PoisOp) :
    (toSh K (BinGen PoisOp)).app (Fin 2) (bin2 g 1) =
      Finsupp.single (FreeSh.genM (by norm_num) (BinGen.op g, 1)) 1 := by
  rw [bin2, show (Pres.mk (.map 1 (FreeBin.gen g)) : FreeSet (BinGen PoisOp) (Fin 2)) =
    SetOperad.map (1 : Equiv.Perm (Fin 2)) (Pres.gen (BinGen.op g)) from rfl, toSh_gen K
    (by norm_num)]
  rfl

/-- **Sorting `g (x₀, h (x₁, x₂))`.** -/
theorem toSh_binR_one (g h : PoisOp) :
    (toSh K (BinGen PoisOp)).app (Fin 3) (binR g h 1) = Finsupp.single (mR g h) 1 := by
  have h1 := comp_e1_bin2 (R := K) g h 1 1
  simp only [if_true] at h1
  rw [← h1]
  show (toSh K (BinGen PoisOp)).app (Fin 3) (ShuffleOperad.comp (R := K)
    (P := Shuf (FreeBin K PoisOp)) (1 : Fin 2) e1 isShuffle_e1 (bin2 g 1) (bin2 h 1)) = _
  rw [(toSh K (BinGen PoisOp)).app_comp, toSh_bin2_one, toSh_bin2_one]
  show FreeSh.bil (STree.graft isShuffle_e1) _ _ = _
  rw [FreeSh.bil_single, mul_one]
  congr 1
  refine Subtype.ext ?_
  show (STree.node (BinGen.op g, (1 : Equiv.Perm (Fin 2))) fun j : Fin 2 => leaf j.1).subst
      (graftFam (1 : Fin 2) e1 (STree.node (BinGen.op h, (1 : Equiv.Perm (Fin 2)))
        fun j : Fin 2 => leaf j.1)) = tR g h
  rw [subst_node, tR, nd, nd]
  congr 1
  funext j
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, subst, Matrix.cons_val_zero]
    have h0 := graftFam_ne (i := (1 : Fin 2)) (e := e1)
      (node (E := PE) (BinGen.op h, (1 : Equiv.Perm (Fin 2))) fun j : Fin 2 => leaf j.1) (0 : Fin 2)
      (by decide)
    rw [opos_fin] at h0
    rw [show ((0 : Fin 2) : ℕ) = 0 from rfl] at h0
    rw [h0, opos_fin]
    rfl
  · simp only [Fin.mk_one, Fin.isValue, subst, Matrix.cons_val_one]
    have h0 := graftFam_opos (i := (1 : Fin 2)) (e := e1)
      (node (E := PE) (BinGen.op h, (1 : Equiv.Perm (Fin 2))) fun j : Fin 2 => leaf j.1)
    rw [opos_fin, show ((1 : Fin 2) : ℕ) = 1 from rfl] at h0
    rw [h0, relabel, subst_node]
    congr 1
    funext j
    fin_cases j
    · show leaf (posR (1 : Fin 2) e1 ((0 : Fin 2) : ℕ)) = leaf 1
      rw [← opos_fin (0 : Fin 2), posR_opos, opos_fin]
      rfl
    · show leaf (posR (1 : Fin 2) e1 ((1 : Fin 2) : ℕ)) = leaf 2
      rw [← opos_fin (1 : Fin 2), posR_opos, opos_fin]
      rfl

/-- **Sorting a relabelled composite of two generators** grafts the corollas. -/
lemma toSh_comp_bin2 {C : Type} [Fintype C] [LinearOrder C] (i : Fin 2)
    {e : Without (Fin 2) i ⊕ Fin 2 ≃ C} (he : Operad.IsShuffle i e) (g h : PoisOp) :
    (toSh K (BinGen PoisOp)).app C (SymOperad.map (R := K) e
      (SymOperad.comp (R := K) i (bin2 g 1) (bin2 h 1))) =
      Finsupp.single (STree.graft he (FreeSh.genM (by norm_num) (BinGen.op g, 1))
        (FreeSh.genM (by norm_num) (BinGen.op h, 1))) 1 := by
  show (toSh K (BinGen PoisOp)).app C (ShuffleOperad.comp (R := K)
    (P := Shuf (FreeBin K PoisOp)) i e he (bin2 g 1) (bin2 h 1)) = _
  rw [(toSh K (BinGen PoisOp)).app_comp, toSh_bin2_one, toSh_bin2_one]
  show FreeSh.bil (STree.graft he) _ _ = _
  rw [FreeSh.bil_single, mul_one]

/-- The composite at the first input is a shuffle. -/
lemma isShuffle_e0 : Operad.IsShuffle (0 : Fin 2) e0 where
  mono_left a a' h := by
    have h0 : ∀ x : Without (Fin 2) 0, x.1 = 1 := fun x => by
      rcases x with ⟨v, hv⟩
      fin_cases v
      · exact absurd rfl hv
      · rfl
    rw [show a = a' from Subtype.ext ((h0 a).trans (h0 a').symm)] at h
    exact absurd h (lt_irrefl _)
  mono_right b b' h := by
    show (b.castSucc : Fin 3) < b'.castSucc
    exact Fin.castSucc_lt_castSucc_iff.2 h
  pointed a b hb := by
    have ha : a.1 = 1 := by
      rcases a with ⟨v, hv⟩
      fin_cases v
      · exact absurd rfl hv
      · rfl
    have hb0 : b = 0 := le_antisymm (hb 0) (Fin.zero_le _)
    subst hb0
    show a.1 < 0 ↔ (2 : Fin 3) < (0 : Fin 2).castSucc
    rw [ha]
    decide

/-- The permutation exchanging the last two inputs. -/
noncomputable def τ₁₂ : Equiv.Perm (Fin 3) := perm3 0 2 1

/-- The composite at the first input, the last two inputs exchanged, is a shuffle. -/
lemma isShuffle_e0' : Operad.IsShuffle (0 : Fin 2) (e0.trans τ₁₂) where
  mono_left a a' h := by
    have h0 : ∀ x : Without (Fin 2) 0, x.1 = 1 := fun x => by
      rcases x with ⟨v, hv⟩
      fin_cases v
      · exact absurd rfl hv
      · rfl
    rw [show a = a' from Subtype.ext ((h0 a).trans (h0 a').symm)] at h
    exact absurd h (lt_irrefl _)
  mono_right b b' h := by
    fin_cases b <;> fin_cases b' <;> first | exact absurd h (by decide) | decide
  pointed a b hb := by
    have ha : a.1 = 1 := by
      rcases a with ⟨v, hv⟩
      fin_cases v
      · exact absurd rfl hv
      · rfl
    have hb0 : b = 0 := le_antisymm (hb 0) (Fin.zero_le _)
    subst hb0
    show a.1 < 0 ↔ τ₁₂ 2 < τ₁₂ (0 : Fin 2).castSucc
    rw [ha]
    decide

/-- **Grafting two corollas at the first input.** -/
lemma graft_genM_zero {C : Type} [Fintype C] [LinearOrder C]
    {e : Without (Fin 2) 0 ⊕ Fin 2 ≃ C} (he : Operad.IsShuffle (0 : Fin 2) e) (g h : PoisOp) :
    (STree.graft he (FreeSh.genM (E := PE) (by norm_num) (BinGen.op g, 1))
      (FreeSh.genM (E := PE) (by norm_num) (BinGen.op h, 1))).1 =
      nd g (nd h (leaf (opos (e (.inr 0)))) (leaf (opos (e (.inr 1)))))
        (leaf (opos (e (.inl ⟨1, by decide⟩)))) := by
  show (STree.node (BinGen.op g, (1 : Equiv.Perm (Fin 2))) fun j : Fin 2 => leaf j.1).subst
      (graftFam (0 : Fin 2) e (STree.node (E := PE) (BinGen.op h, (1 : Equiv.Perm (Fin 2)))
        fun j : Fin 2 => leaf j.1)) = _
  rw [subst_node, nd]
  congr 1
  funext j
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, subst, Matrix.cons_val_zero]
    have h0 := graftFam_opos (i := (0 : Fin 2)) (e := e)
      (node (E := PE) (BinGen.op h, (1 : Equiv.Perm (Fin 2))) fun j : Fin 2 => leaf j.1)
    rw [opos_fin, show ((0 : Fin 2) : ℕ) = 0 from rfl] at h0
    rw [h0, relabel, subst_node, nd]
    congr 1
    funext j
    fin_cases j
    · show leaf (posR (0 : Fin 2) e ((0 : Fin 2) : ℕ)) = _
      rw [← opos_fin (0 : Fin 2), posR_opos]
      rfl
    · show leaf (posR (0 : Fin 2) e ((1 : Fin 2) : ℕ)) = _
      rw [← opos_fin (1 : Fin 2), posR_opos]
      rfl
  · simp only [Fin.mk_one, Fin.isValue, subst, Matrix.cons_val_one]
    have h0 := graftFam_ne (i := (0 : Fin 2)) (e := e)
      (node (E := PE) (BinGen.op h, (1 : Equiv.Perm (Fin 2))) fun j : Fin 2 => leaf j.1)
      (1 : Fin 2) (by decide)
    rw [opos_fin, show ((1 : Fin 2) : ℕ) = 1 from rfl] at h0
    rw [h0]
    rfl

/-- `g (h (x₀, x₁), x₂)` on the positions. -/
def mL₁ (g h : PoisOp) : SMono PE (Finset.range (Fintype.card (Fin 3))) :=
  ⟨tL₁ g h, isShuffle_nd (isShuffle_nd trivial trivial (by simp)) trivial (by simp),
    by simp only [tL₁, labels_nd, labels_leaf]; rw [labels_three]; rfl⟩

/-- `g (h (x₀, x₂), x₁)` on the positions. -/
def mL₂ (g h : PoisOp) : SMono PE (Finset.range (Fintype.card (Fin 3))) :=
  ⟨tL₂ g h, isShuffle_nd (isShuffle_nd trivial trivial (by simp)) trivial (by simp),
    by simp only [tL₂, labels_nd, labels_leaf]; rw [labels_three]; decide⟩

/-- **Sorting `g (h (x₀, x₁), x₂)`.** -/
theorem toSh_binL_one (g h : PoisOp) :
    (toSh K (BinGen PoisOp)).app (Fin 3) (binL g h 1) = Finsupp.single (mL₁ g h) 1 := by
  have h1 := comp_e0_bin2 (R := K) g h 1 1
  simp only [if_true] at h1
  rw [← h1, toSh_comp_bin2 K 0 isShuffle_e0]
  congr 1
  refine Subtype.ext ?_
  rw [graft_genM_zero]
  simp only [opos_fin]
  rfl

/-- **Sorting `g (h (x₀, x₂), x₁)`.** -/
theorem toSh_binL_021 (g h : PoisOp) :
    (toSh K (BinGen PoisOp)).app (Fin 3) (binL g h τ₁₂) = Finsupp.single (mL₂ g h) 1 := by
  have h1 := comp_e0_bin2 (R := K) g h 1 1
  simp only [if_true] at h1
  have h2 : binL (R := K) g h τ₁₂ = SymOperad.map (R := K) (e0.trans τ₁₂)
      (SymOperad.comp (R := K) 0 (bin2 g 1) (bin2 h 1)) := by
    rw [← SymOperad.map_map, h1, ← mono3_false, map_binL, mul_one]
  rw [h2, toSh_comp_bin2 K 0 isShuffle_e0']
  congr 1
  refine Subtype.ext ?_
  rw [graft_genM_zero]
  simp only [opos_fin]
  rfl

/-! ## The relations of arity three of the Poisson operad -/

/-- The relators of arity two. -/
abbrev r₂P : Set (FreeBin K PoisOp (Fin 2)) :=
  {BinRel.comm K PoisOp.mul, BinRel.antisymm K PoisOp.bracket}

/-- The relators of arity three. -/
abbrev r₃P : Set (FreeBin K PoisOp (Fin 3)) :=
  {BinRel.assoc K PoisOp.mul, BinRel.jacobi K PoisOp.bracket,
    BinRel.leibnizRule K PoisOp.mul PoisOp.bracket}

variable {K}

lemma swap_ne_one : (Equiv.swap (0 : Fin 2) 1) ≠ 1 := by decide

lemma comm_mem : BinRel.comm K PoisOp.mul ∈ Submodule.span K (orbit2 K (r₂P K)) :=
  Submodule.subset_span ⟨1, _, Or.inl rfl, (SymOperad.map_refl _).symm⟩

lemma antisymm_mem : BinRel.antisymm K PoisOp.bracket ∈ Submodule.span K (orbit2 K (r₂P K)) :=
  Submodule.subset_span ⟨1, _, Or.inr rfl, (SymOperad.map_refl _).symm⟩

/-- **Relators of arity two at the root.** -/
lemma outer_mem {x : FreeBin K PoisOp (Fin 2)} (hx : x ∈ Submodule.span K (orbit2 K (r₂P K)))
    (h : PoisOp) (π : Equiv.Perm (Fin 3)) :
    SymOperad.map (R := K) π (SymOperad.map (R := K) e0
      (SymOperad.comp (R := K) 0 x (bin2 h 1))) ∈ ideal3Of K (r₂P K) := by
  rw [SymOperad.map_map]
  exact comp_mem_ideal3Of_left 0 _ hx _

/-- **Relators of arity two at the first input.** -/
lemma inner_mem {y : FreeBin K PoisOp (Fin 2)} (hy : y ∈ Submodule.span K (orbit2 K (r₂P K)))
    (g : PoisOp) (π : Equiv.Perm (Fin 3)) :
    SymOperad.map (R := K) π (SymOperad.map (R := K) e0
      (SymOperad.comp (R := K) 0 (bin2 g 1) y)) ∈ ideal3Of K (r₂P K) := by
  rw [SymOperad.map_map]
  exact comp_mem_ideal3Of_right 0 _ _ hy

/-- **Relators of arity two at the second input.** -/
lemma innerR_mem {y : FreeBin K PoisOp (Fin 2)} (hy : y ∈ Submodule.span K (orbit2 K (r₂P K)))
    (g : PoisOp) (π : Equiv.Perm (Fin 3)) :
    SymOperad.map (R := K) π (SymOperad.map (R := K) e1
      (SymOperad.comp (R := K) 1 (bin2 g 1) y)) ∈ ideal3Of K (r₂P K) := by
  rw [SymOperad.map_map]
  exact comp_mem_ideal3Of_right 1 _ _ hy

lemma outer_val (g h : PoisOp) (π : Equiv.Perm (Fin 3)) (c : K) :
    SymOperad.map (R := K) π (SymOperad.map (R := K) e0 (SymOperad.comp (R := K) 0
      (bin2 (R := K) g 1 + c • bin2 g (Equiv.swap 0 1)) (bin2 h 1))) =
      binL (R := K) g h π + c • binR g h (π * perm3 2 0 1) := by
  rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
    comp_e0_bin2, comp_e0_bin2, if_pos rfl, if_neg swap_ne_one, if_pos rfl, if_pos rfl, map_add,
    map_smul, map_binL, map_binR, mul_one]
  rfl

lemma inner_val (g h : PoisOp) (π : Equiv.Perm (Fin 3)) (c : K) :
    SymOperad.map (R := K) π (SymOperad.map (R := K) e0 (SymOperad.comp (R := K) 0
      (bin2 (R := K) g 1) (bin2 h 1 + c • bin2 h (Equiv.swap 0 1)))) =
      binL (R := K) g h π + c • binL g h (π * perm3 1 0 2) := by
  rw [map_add, map_smul, map_add, map_smul, comp_e0_bin2, comp_e0_bin2, if_pos rfl, if_pos rfl,
    if_pos rfl, if_neg swap_ne_one, map_add, map_smul, map_binL,
    map_binL, mul_one]
  rfl

lemma innerR_val (g h : PoisOp) (π : Equiv.Perm (Fin 3)) (c : K) :
    SymOperad.map (R := K) π (SymOperad.map (R := K) e1 (SymOperad.comp (R := K) 1
      (bin2 (R := K) g 1) (bin2 h 1 + c • bin2 h (Equiv.swap 0 1)))) =
      binR (R := K) g h π + c • binR g h (π * perm3 0 2 1) := by
  rw [map_add, map_smul, map_add, map_smul, comp_e1_bin2, comp_e1_bin2, if_pos rfl, if_pos rfl,
    if_pos rfl, if_neg swap_ne_one, map_add, map_smul, map_binR,
    map_binR, mul_one]
  rfl

variable (K) in
/-- The relations of arity three of the Poisson operad. -/
noncomputable abbrev I3 : Submodule K (FreeBin K PoisOp (Fin 3)) :=
  ideal3Of K (r₂P K) ⊔ Submodule.span K (orbit3 K (r₃P K))

lemma I3_eq : (SymOperadIdeal.span K (rel23 (r₂P K) (r₃P K))).sub (Fin 3) = I3 K :=
  span_sub_three_23 K _ _

lemma antisymm_eq : BinRel.antisymm K PoisOp.bracket =
    bin2 (R := K) PoisOp.bracket 1 + (1 : K) • bin2 PoisOp.bracket (Equiv.swap 0 1) := by
  rw [one_smul]
  rfl

lemma comm_eq : BinRel.comm K PoisOp.mul =
    bin2 (R := K) PoisOp.mul 1 + (-1 : K) • bin2 PoisOp.mul (Equiv.swap 0 1) := by
  rw [neg_one_smul, ← sub_eq_add_neg]
  rfl

lemma rel_mem_orbit3 {x : FreeBin K PoisOp (Fin 3)} (hx : x ∈ r₃P K) (π : Equiv.Perm (Fin 3)) :
    SymOperad.map (R := K) π x ∈ I3 K :=
  Submodule.mem_sup_right (Submodule.subset_span ⟨π, x, hx, rfl⟩)

lemma rel_mem {x : FreeBin K PoisOp (Fin 3)} (hx : x ∈ r₃P K) : x ∈ I3 K := by
  have := rel_mem_orbit3 hx 1
  rwa [show SymOperad.map (R := K) (1 : Equiv.Perm (Fin 3)) x = x from SymOperad.map_refl x]
    at this

lemma outer_mem_anti (h : PoisOp) (π : Equiv.Perm (Fin 3)) :
    binL (R := K) .bracket h π + binR .bracket h (π * perm3 2 0 1) ∈ I3 K := by
  have := outer_mem (K := K) antisymm_mem h π
  rw [antisymm_eq, outer_val, one_smul] at this
  exact Submodule.mem_sup_left this

lemma outer_mem_comm (h : PoisOp) (π : Equiv.Perm (Fin 3)) :
    binL (R := K) .mul h π - binR .mul h (π * perm3 2 0 1) ∈ I3 K := by
  have := outer_mem (K := K) comm_mem h π
  rw [comm_eq, outer_val, neg_one_smul, ← sub_eq_add_neg] at this
  exact Submodule.mem_sup_left this

lemma inner_mem_anti (g : PoisOp) (π : Equiv.Perm (Fin 3)) :
    binL (R := K) g .bracket π + binL g .bracket (π * perm3 1 0 2) ∈ I3 K := by
  have := inner_mem (K := K) antisymm_mem g π
  rw [antisymm_eq, inner_val, one_smul] at this
  exact Submodule.mem_sup_left this

lemma innerR_mem_anti (g : PoisOp) (π : Equiv.Perm (Fin 3)) :
    binR (R := K) g .bracket π + binR g .bracket (π * perm3 0 2 1) ∈ I3 K := by
  have := innerR_mem (K := K) antisymm_mem g π
  rw [antisymm_eq, innerR_val, one_smul] at this
  exact Submodule.mem_sup_left this

lemma innerR_mem_comm (g : PoisOp) (π : Equiv.Perm (Fin 3)) :
    binR (R := K) g .mul π - binR g .mul (π * perm3 0 2 1) ∈ I3 K := by
  have := innerR_mem (K := K) comm_mem g π
  rw [comm_eq, innerR_val, neg_one_smul, ← sub_eq_add_neg] at this
  exact Submodule.mem_sup_left this

lemma perm_a : perm3 1 2 0 * perm3 2 0 1 = 1 := Equiv.ext fun i => by fin_cases i <;> rfl
lemma perm_b : perm3 2 0 1 * perm3 1 0 2 = τ₁₂ := Equiv.ext fun i => by fin_cases i <;> rfl
lemma perm_c : τ₁₂ * perm3 2 0 1 = perm3 1 0 2 := Equiv.ext fun i => by fin_cases i <;> rfl
lemma perm_d : perm3 1 0 2 * perm3 1 0 2 = 1 := Equiv.ext fun i => by fin_cases i <;> rfl
lemma perm_e : (1 : Equiv.Perm (Fin 3)) * perm3 2 0 1 = perm3 2 0 1 := one_mul _
lemma perm_f : τ₁₂ * perm3 0 2 1 = 1 := Equiv.ext fun i => by fin_cases i <;> rfl

/-- **The Jacobi rule**: `[[x₀, x₁], x₂] = [[x₀, x₂], x₁] + [x₀, [x₁, x₂]]`. -/
theorem y₁_mem : binL (R := K) .bracket .bracket 1 - binL .bracket .bracket τ₁₂
    - binR .bracket .bracket 1 ∈ I3 K := by
  have hJ := rel_mem (K := K) (x := BinRel.jacobi K .bracket) (by simp)
  have h1 := outer_mem_anti (K := K) .bracket (perm3 1 2 0)
  have h2 := inner_mem_anti (K := K) .bracket (perm3 2 0 1)
  rw [perm_a] at h1
  rw [perm_b] at h2
  rw [BinRel.jacobi] at hJ
  convert sub_mem (sub_mem hJ h1) h2 using 1
  abel

/-- **The Leibniz rule** `[x₀, x₁x₂] = [x₀, x₁]x₂ + [x₀, x₂]x₁`. -/
theorem y₂_mem : binR (R := K) .bracket .mul 1 - binL .mul .bracket 1 - binL .mul .bracket τ₁₂
    ∈ I3 K := by
  have hL := rel_mem (K := K) (x := BinRel.leibnizRule K .mul .bracket) (by simp)
  have h1 := outer_mem_comm (K := K) .bracket τ₁₂
  rw [perm_c] at h1
  rw [BinRel.leibnizRule] at hL
  convert sub_mem hL h1 using 1
  abel

/-- **The Leibniz rule** `[x₀x₂, x₁] = [x₀, x₁]x₂ - x₀[x₁, x₂]`. -/
theorem y₃_mem : binL (R := K) .bracket .mul τ₁₂ - binL .mul .bracket 1 + binR .mul .bracket 1
    ∈ I3 K := by
  have hL := rel_mem_orbit3 (K := K) (x := BinRel.leibnizRule K .mul .bracket) (by simp)
    (perm3 1 0 2)
  have ha := outer_mem_anti (K := K) .mul τ₁₂
  have hb := inner_mem_anti (K := K) .mul (perm3 1 0 2)
  rw [perm_c] at ha
  rw [perm_d] at hb
  rw [BinRel.leibnizRule, map_sub, map_add, map_binL, map_binR, map_binR, mul_one, perm_d]
    at hL
  convert sub_mem (add_mem (neg_mem hL) ha) hb using 1
  simp only [mono3_false, mono3_true]
  abel

/-- **The Leibniz rule** `[x₀x₁, x₂] = [x₀, x₂]x₁ + x₀[x₁, x₂]`. -/
theorem y₄_mem : binL (R := K) .bracket .mul 1 - binL .mul .bracket τ₁₂ - binR .mul .bracket 1
    ∈ I3 K := by
  have hL := rel_mem_orbit3 (K := K) (x := BinRel.leibnizRule K .mul .bracket) (by simp)
    (perm3 2 0 1)
  have ha := outer_mem_anti (K := K) .mul 1
  have hb := inner_mem_anti (K := K) .mul (perm3 2 0 1)
  have hc := innerR_mem_anti (K := K) .mul τ₁₂
  rw [perm_e] at ha
  rw [perm_b] at hb
  rw [perm_f] at hc
  rw [BinRel.leibnizRule, map_sub, map_add, map_binL, map_binR, map_binR, mul_one, perm_b]
    at hL
  convert sub_mem (sub_mem (add_mem (neg_mem hL) ha) hb) hc using 1
  simp only [mono3_false, mono3_true]
  abel

/-- **Associativity** `x₀(x₁x₂) = (x₀x₁)x₂`. -/
theorem y₅_mem : binR (R := K) .mul .mul 1 - binL .mul .mul 1 ∈ I3 K := by
  have hA := rel_mem (K := K) (x := BinRel.assoc K .mul) (by simp)
  rw [BinRel.assoc] at hA
  convert neg_mem hA using 1
  abel

/-- **Associativity and commutativity** `(x₀x₂)x₁ = (x₀x₁)x₂`. -/
theorem y₆_mem : binL (R := K) .mul .mul τ₁₂ - binL .mul .mul 1 ∈ I3 K := by
  have hA := rel_mem (K := K) (x := BinRel.assoc K .mul) (by simp)
  have hA' := rel_mem_orbit3 (K := K) (x := BinRel.assoc K .mul) (by simp) τ₁₂
  have hc := innerR_mem_comm (K := K) .mul τ₁₂
  rw [perm_f] at hc
  rw [BinRel.assoc] at hA
  rw [BinRel.assoc, map_sub, map_binL, map_binR, mul_one] at hA'
  convert sub_mem (add_mem hA' hc) hA using 1
  simp only [mono3_false, mono3_true]
  abel

/-! ## The order -/

/-- **The letter** of an input of a vertex: brackets after products, transposed generators after
untransposed ones, the second input after the first. -/
def code (g : PoisOp) (σ : Equiv.Perm (Fin 2)) (i : ℕ) : Fin 8 :=
  ⟨(match g with | .mul => 0 | .bracket => 4) + (if σ = 1 then 0 else 2) + min i 1, by
    cases g <;> split_ifs <;> simp only [] <;> omega⟩

/-- The letters of the vertices. -/
def ltr : ∀ k, PE k → ℕ → Fin 8
  | _, (BinGen.op g, σ), i => code g σ i

/-- The number of bracket letters. -/
def nb (w : List (Fin 8)) : ℕ := w.countP fun c => decide (4 ≤ c.val)

/-- The number of product letters. -/
def nm (w : List (Fin 8)) : ℕ := w.countP fun c => !decide (4 ≤ c.val)

/-- **The word order**: more brackets first, then fewer products, then lexicographically. -/
def PW (u w : List (Fin 8)) : Prop :=
  nb u < nb w ∨ nb u = nb w ∧ (nm w < nm u ∨ nm w = nm u ∧ List.Lex (· < ·) u w)

lemma length_eq (w : List (Fin 8)) : w.length = nb w + nm w := by
  rw [List.length_eq_countP_add_countP (fun c : Fin 8 => decide (4 ≤ c.val)) (l := w), nb, nm]
  congr 1
  refine List.countP_congr fun c _ => ?_
  simp

lemma PW_trans {u v w : List (Fin 8)} (h₁ : PW u v) (h₂ : PW v w) : PW u w := by
  rcases h₁ with h₁ | ⟨e₁, h₁ | ⟨f₁, l₁⟩⟩ <;> rcases h₂ with h₂ | ⟨e₂, h₂ | ⟨f₂, l₂⟩⟩
  all_goals first
    | exact Or.inl (by omega)
    | exact Or.inr ⟨by omega, Or.inl (by omega)⟩
    | exact Or.inr ⟨by omega, Or.inr ⟨by omega, lex_trans l₁ l₂⟩⟩

lemma lex_irrefl : ∀ u : List (Fin 8), ¬ List.Lex (· < ·) u u
  | [], h => by cases h
  | a :: u, h => by
    cases h with
    | cons h => exact lex_irrefl u h
    | rel h => exact lt_irrefl a h

lemma PW_irrefl (u : List (Fin 8)) : ¬ PW u u := by
  rintro (h | ⟨_, h | ⟨_, h⟩⟩)
  · exact lt_irrefl _ h
  · exact lt_irrefl _ h
  · exact lex_irrefl u h

lemma nb_append (u w : List (Fin 8)) : nb (u ++ w) = nb u + nb w := List.countP_append ..
lemma nm_append (u w : List (Fin 8)) : nm (u ++ w) = nm u + nm w := List.countP_append ..

/-- **Concatenation preserves the word order.** -/
lemma PW_append {u w : List (Fin 8)} (h : PW u w) (P Q : List (Fin 8)) :
    PW (P ++ (u ++ Q)) (P ++ (w ++ Q)) := by
  simp only [PW, nb_append, nm_append] at h ⊢
  rcases h with h | ⟨e, h | ⟨f, l⟩⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, Or.inl (by omega)⟩
  · refine Or.inr ⟨by omega, Or.inr ⟨by omega, List.Lex.append_left _ (lex_append_right l ?_ Q) P⟩⟩
    rw [length_eq, length_eq, e, f]

/-- **A word has at most as many letters as the tree has vertices.** -/
theorem length_pathWord_le : ∀ (t : STree PE) (q : List ℕ), (pathWord ltr t q).length ≤ t.weight
  | leaf _, _ => by simp [pathWord]
  | node _ _, [] => by simp
  | @node _ k e c, i :: q => by
    rw [pathWord_node_cons]
    split_ifs with h
    · have h1 := length_pathWord_le (c ⟨i, h⟩) q
      have h2 := Finset.single_le_sum (f := fun j => (c j).weight) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ ⟨i, h⟩)
      beta_reduce at h2
      simp only [List.length_cons, weight_node]
      omega
    · simp

/-- **A binary tree has one vertex fewer than leaves.** -/
theorem weight_add_one (t : STree PE) : t.weight + 1 = Multiset.card t.labels := by
  induction t with
  | leaf _ => rfl
  | @node k e c ih =>
    obtain ⟨⟨g⟩, σ⟩ := e
    rw [weight_node, labels_node, Fin.sum_univ_two, Fin.sum_univ_two, Multiset.card_add,
      ← ih 0, ← ih 1]
    omega

lemma length_word_le {A : Finset ℕ} (x : SMono PE A) (a : ℕ) :
    (word ltr x.1 a).length ≤ A.card := by
  have h1 := length_pathWord_le x.1 (x.1.pos a)
  have h2 := weight_add_one x.1
  rw [x.labels_eq] at h2
  rw [STree.word]
  have : Multiset.card A.val = A.card := rfl
  omega

/-- Words of bounded length. -/
abbrev BW (N : ℕ) := {w : List (Fin 8) // w.length ≤ N}

instance (N : ℕ) : Finite (BW N) := (List.finite_length_le (Fin 8) N).to_subtype

/-- The word order on words of bounded length. -/
def bwRel (N : ℕ) (u w : BW N) : Prop := PW u.1 w.1

instance (N : ℕ) : IsTrans (BW N) (bwRel N) := ⟨fun _ _ _ => PW_trans⟩

instance (N : ℕ) : Std.Irrefl (bwRel N) := ⟨fun u => PW_irrefl u.1⟩

/-- **The path order of the word order is well-founded**, the words of the monomials on a finite
set being of bounded length. -/
theorem pathLexBy_PW_wf (A : Finset ℕ) : WellFounded (pathLexBy ltr PW (A := A) (E := PE)) := by
  let F : SMono PE A → (A → BW A.card) := fun x a => ⟨STree.word ltr x.1 a, length_word_le x a⟩
  have hwf : WellFounded (Pi.Lex (· < ·) (fun {_} => bwRel A.card) :
      (A → BW A.card) → _ → Prop) :=
    Pi.Lex.wellFounded _ fun _ => Finite.wellFounded_of_trans_of_irrefl _
  refine Subrelation.wf (fun {x y} h => ?_) (InvImage.wf F hwf)
  obtain ⟨i, hi, hlt⟩ := h
  exact ⟨i, fun j hj => Subtype.ext (hi j hj), hlt⟩

/-- **The admissible order of the Poisson operad.** -/
def poisOrder : AdmOrder PE where
  lt := pathLexBy ltr PW
  wf := pathLexBy_PW_wf
  trans := pathLexBy_trans ltr (W := PW) fun h h' => PW_trans h h'
  lt_ctx hf _ _ h := pathLexBy_ctx ltr (W := PW) (fun h P Q => PW_append h P Q) hf h

/-! ## The rules -/

lemma word_eq {t : STree PE} (hn : t.labels.Nodup) {a : ℕ} {q : List ℕ}
    (h : t.get? q = some (leaf a)) : STree.word ltr t a = pathWord ltr t q := by
  rw [STree.word, pos_eq hn h]

/-- `g (h (x₀, x₁), x₂)` on the positions. -/
lemma words_L₁ (g h : PoisOp) :
    STree.word ltr (mL₁ g h).1 0 = [code g 1 0, code h 1 0] ∧
    STree.word ltr (mL₁ g h).1 1 = [code g 1 0, code h 1 1] ∧
    STree.word ltr (mL₁ g h).1 2 = [code g 1 1] :=
  ⟨word_eq (mL₁ g h).nodup (q := [0, 0]) rfl, word_eq (mL₁ g h).nodup (q := [0, 1]) rfl,
    word_eq (mL₁ g h).nodup (q := [1]) rfl⟩

lemma words_L₂ (g h : PoisOp) :
    STree.word ltr (mL₂ g h).1 0 = [code g 1 0, code h 1 0] ∧
    STree.word ltr (mL₂ g h).1 1 = [code g 1 1] ∧
    STree.word ltr (mL₂ g h).1 2 = [code g 1 0, code h 1 1] :=
  ⟨word_eq (mL₂ g h).nodup (q := [0, 0]) rfl, word_eq (mL₂ g h).nodup (q := [1]) rfl,
    word_eq (mL₂ g h).nodup (q := [0, 1]) rfl⟩

lemma words_R (g h : PoisOp) :
    STree.word ltr (mR g h).1 0 = [code g 1 0] ∧
    STree.word ltr (mR g h).1 1 = [code g 1 1, code h 1 0] ∧
    STree.word ltr (mR g h).1 2 = [code g 1 1, code h 1 1] :=
  ⟨word_eq (mR g h).nodup (q := [0]) rfl, word_eq (mR g h).nodup (q := [1, 0]) rfl,
    word_eq (mR g h).nodup (q := [1, 1]) rfl⟩

/-- The positions `0, 1, 2`. -/
abbrev p3 : Finset ℕ := Finset.range (Fintype.card (Fin 3))

lemma mem_p3 (a : ℕ) (h : a < 3 := by decide) : a ∈ p3 := by
  rw [Finset.mem_range, Fintype.card_fin]
  exact h

/-- **Comparing at the first leaf.** -/
lemma lt_at0 {x y : SMono PE p3} (h : PW (STree.word ltr x.1 0) (STree.word ltr y.1 0)) :
    poisOrder.lt x y :=
  ⟨⟨0, mem_p3 0⟩, fun j hj => absurd hj (by
    show ¬ j.1 < 0
    omega), h⟩

/-- **Comparing at the second leaf.** -/
lemma lt_at1 {x y : SMono PE p3} (h0 : STree.word ltr x.1 0 = STree.word ltr y.1 0)
    (h : PW (STree.word ltr x.1 1) (STree.word ltr y.1 1)) : poisOrder.lt x y :=
  ⟨⟨1, mem_p3 1⟩, fun j hj => by
    have : j.1 = 0 := by
      have : j.1 < 1 := hj
      omega
    show STree.word ltr x.1 j.1 = STree.word ltr y.1 j.1
    rw [this]
    exact h0, h⟩

/-- The positions `0, 1`. -/
abbrev p2 : Finset ℕ := Finset.range (Fintype.card (Fin 2))

lemma mem_p2 : (0 : ℕ) ∈ p2 := by
  rw [Finset.mem_range, Fintype.card_fin]
  omega

/-- A corolla with a transposed or untransposed generator. -/
def cor (g : PoisOp) (σ : Equiv.Perm (Fin 2)) : SMono PE p2 :=
  FreeSh.genM (by norm_num) (BinGen.op g, σ)

lemma word_cor (g : PoisOp) (σ : Equiv.Perm (Fin 2)) :
    STree.word ltr (cor g σ).1 0 = [code g σ 0] :=
  word_eq (cor g σ).nodup (q := [0]) rfl

/-- **The rules of the Poisson operad.** -/
inductive PR
  | jac | leib₁ | leib₂ | leib₃ | as₁ | as₂ | cm | an

/-- The arity of a rule. -/
def PR.src : PR → Finset ℕ
  | .cm | .an => p2
  | _ => p3

/-- The leading monomials. -/
def PR.lead : ∀ r : PR, SMono PE r.src
  | .jac => mL₁ .bracket .bracket
  | .leib₁ => mR .bracket .mul
  | .leib₂ => mL₂ .bracket .mul
  | .leib₃ => mL₁ .bracket .mul
  | .as₁ => mR .mul .mul
  | .as₂ => mL₂ .mul .mul
  | .cm => cor .mul (Equiv.swap 0 1)
  | .an => cor .bracket (Equiv.swap 0 1)

variable (K) in
/-- The tails. -/
noncomputable def PR.tail : ∀ r : PR, SMono PE r.src →₀ K
  | .jac => Finsupp.single (mL₂ .bracket .bracket) 1 + Finsupp.single (mR .bracket .bracket) 1
  | .leib₁ => Finsupp.single (mL₁ .mul .bracket) 1 + Finsupp.single (mL₂ .mul .bracket) 1
  | .leib₂ => Finsupp.single (mL₁ .mul .bracket) 1 - Finsupp.single (mR .mul .bracket) 1
  | .leib₃ => Finsupp.single (mL₂ .mul .bracket) 1 + Finsupp.single (mR .mul .bracket) 1
  | .as₁ => Finsupp.single (mL₁ .mul .mul) 1
  | .as₂ => Finsupp.single (mL₁ .mul .mul) 1
  | .cm => Finsupp.single (cor .mul 1) 1
  | .an => -Finsupp.single (cor .bracket 1) 1

lemma mem_support₂ {A : Finset ℕ} {a b m : SMono PE A} {c d : K}
    (h : m ∈ (Finsupp.single a c + Finsupp.single b d).support) : m = a ∨ m = b := by
  classical
  rcases Finset.mem_union.1 (Finsupp.support_add h) with h | h
  · exact Or.inl (Finset.mem_singleton.1 (Finsupp.support_single_subset h))
  · exact Or.inr (Finset.mem_singleton.1 (Finsupp.support_single_subset h))

lemma mem_support₁ {A : Finset ℕ} {a m : SMono PE A} {c : K}
    (h : m ∈ (Finsupp.single a c).support) : m = a := by
  classical
  exact Finset.mem_singleton.1 (Finsupp.support_single_subset h)

lemma mem_support_sub {A : Finset ℕ} {a b m : SMono PE A} {c d : K}
    (h : m ∈ (Finsupp.single a c - Finsupp.single b d).support) : m = a ∨ m = b := by
  classical
  rcases Finset.mem_union.1 (Finsupp.support_sub h) with h | h
  · exact Or.inl (Finset.mem_singleton.1 (Finsupp.support_single_subset h))
  · exact Or.inr (Finset.mem_singleton.1 (Finsupp.support_single_subset h))

/-- **The tails are smaller than the leading monomials.** -/
theorem PR.tail_lt : ∀ r : PR, ∀ m ∈ (r.tail K).support, poisOrder.lt m r.lead
  | .jac, m, hm => by
    dsimp only [PR.lead]
    rcases mem_support₂ hm with rfl | rfl
    · refine lt_at1 ((words_L₂ _ _).1.trans (words_L₁ _ _).1.symm) ?_
      rw [(words_L₂ _ _).2.1, (words_L₁ _ _).2.1]
      exact Or.inl (by decide)
    · refine lt_at0 ?_
      rw [(words_R _ _).1, (words_L₁ _ _).1]
      exact Or.inl (by decide)
  | .leib₁, m, hm => by
    dsimp only [PR.lead]
    rcases mem_support₂ hm with rfl | rfl
    · refine lt_at0 ?_
      rw [(words_L₁ _ _).1, (words_R _ _).1]
      exact Or.inr ⟨by decide, Or.inl (by decide)⟩
    · refine lt_at0 ?_
      rw [(words_L₂ _ _).1, (words_R _ _).1]
      exact Or.inr ⟨by decide, Or.inl (by decide)⟩
  | .leib₂, m, hm => by
    dsimp only [PR.lead]
    simp only [PR.tail] at hm
    rcases mem_support_sub hm with rfl | rfl
    · refine lt_at0 ?_
      rw [(words_L₁ _ _).1, (words_L₂ _ _).1]
      exact Or.inr ⟨by decide, Or.inr ⟨by decide, by decide⟩⟩
    · refine lt_at0 ?_
      rw [(words_R _ _).1, (words_L₂ _ _).1]
      exact Or.inl (by decide)
  | .leib₃, m, hm => by
    dsimp only [PR.lead]
    rcases mem_support₂ hm with rfl | rfl
    · refine lt_at0 ?_
      rw [(words_L₂ _ _).1, (words_L₁ _ _).1]
      exact Or.inr ⟨by decide, Or.inr ⟨by decide, by decide⟩⟩
    · refine lt_at0 ?_
      rw [(words_R _ _).1, (words_L₁ _ _).1]
      exact Or.inl (by decide)
  | .as₁, m, hm => by
    dsimp only [PR.lead]
    rcases mem_support₁ hm with rfl
    refine lt_at0 ?_
    rw [(words_L₁ _ _).1, (words_R _ _).1]
    exact Or.inr ⟨by decide, Or.inl (by decide)⟩
  | .as₂, m, hm => by
    dsimp only [PR.lead]
    rcases mem_support₁ hm with rfl
    refine lt_at1 ((words_L₁ _ _).1.trans (words_L₂ _ _).1.symm) ?_
    rw [(words_L₁ _ _).2.1, (words_L₂ _ _).2.1]
    exact Or.inr ⟨by decide, Or.inl (by decide)⟩
  | .cm, m, hm => by
    dsimp only [PR.lead]
    rcases mem_support₁ hm with rfl
    refine ⟨⟨0, mem_p2⟩, fun j hj => absurd hj (by
      show ¬ j.1 < 0
      omega), ?_⟩
    show PW (STree.word ltr (cor _ _).1 0) (STree.word ltr (cor _ _).1 0)
    rw [word_cor, word_cor]
    exact Or.inr ⟨by decide, Or.inr ⟨by decide, by decide⟩⟩
  | .an, m, hm => by
    dsimp only [PR.lead]
    simp only [PR.tail] at hm
    rw [← Finsupp.single_neg] at hm
    rcases mem_support₁ hm with rfl
    refine ⟨⟨0, mem_p2⟩, fun j hj => absurd hj (by
      show ¬ j.1 < 0
      omega), ?_⟩
    show PW (STree.word ltr (cor _ _).1 0) (STree.word ltr (cor _ _).1 0)
    rw [word_cor, word_cor]
    exact Or.inr ⟨by decide, Or.inr ⟨by decide, by decide⟩⟩

variable (K) in
/-- **The rewriting rules of the Poisson operad.** -/
noncomputable def rules : Rules K PR poisOrder.toCtxOrder where
  src := PR.src
  lead := PR.lead
  tail := PR.tail K
  tail_lt := PR.tail_lt

/-! ## The rules hold in the Poisson operad -/

variable (K) in
/-- **The shuffle ideal of the Poisson operad**: generated by the sorted relators. -/
noncomputable abbrev TP : ShuffleOperadIdeal K (FreeSh K PE) :=
  ShuffleOperadIdeal.span K (shuffleRel K (rel23 (r₂P K) (r₃P K)))

lemma toSh_mem3 {y : FreeBin K PoisOp (Fin 3)} (hy : y ∈ I3 K) :
    (toSh K (BinGen PoisOp)).app (Fin 3) y ∈ (TP K).sub (Fin 3) := by
  rw [← I3_eq, sub_eq_relabel] at hy
  exact span_relabel_le K _ (Fin 3) hy

lemma toSh_mem2 {y : FreeBin K PoisOp (Fin 2)} (hy : y ∈ r₂P K) :
    (toSh K (BinGen PoisOp)).app (Fin 2) y ∈ (TP K).sub (Fin 2) := by
  have : y ∈ (SymOperadIdeal.span K (rel23 (r₂P K) (r₃P K))).sub (Fin 2) :=
    SymOperadIdeal.subset_span 2 hy
  rw [sub_eq_relabel] at this
  exact span_relabel_le K _ (Fin 2) this

lemma toSh_bin2 (g : PoisOp) (σ : Equiv.Perm (Fin 2)) :
    (toSh K (BinGen PoisOp)).app (Fin 2) (bin2 g σ) =
      Finsupp.single (FreeSh.genM (by norm_num) (BinGen.op g, σ.symm)) 1 := by
  rw [bin2, show (Pres.mk (.map σ (FreeBin.gen g)) : FreeSet (BinGen PoisOp) (Fin 2)) =
    SetOperad.map σ (Pres.gen (BinGen.op g)) from rfl, toSh_gen K (by norm_num)]

lemma toSh_sub {n : ℕ} (x y : FreeBin K PoisOp (Fin n)) :
    (toSh K (BinGen PoisOp)).app (Fin n) (x - y) =
      (toSh K (BinGen PoisOp)).app (Fin n) x - (toSh K (BinGen PoisOp)).app (Fin n) y :=
  LinearMap.map_sub _ x y

lemma toSh_add {n : ℕ} (x y : FreeBin K PoisOp (Fin n)) :
    (toSh K (BinGen PoisOp)).app (Fin n) (x + y) =
      (toSh K (BinGen PoisOp)).app (Fin n) x + (toSh K (BinGen PoisOp)).app (Fin n) y :=
  LinearMap.map_add _ x y

lemma cast_rfl_eq {X : Finset ℕ} (h : X = X) (v : SMono PE X →₀ K) :
    Finsupp.mapDomain (SMono.cast h) v = v := by
  have : (SMono.cast h : SMono PE X → SMono PE X) = id := funext fun t => Subtype.ext rfl
  rw [this, Finsupp.mapDomain_id]

/-- **The relation of a rule** on its positions. -/
noncomputable def PR.rel (r : PR) : SMono PE r.src →₀ K :=
  Finsupp.single r.lead 1 - r.tail K

lemma toSh_y₁ : (toSh K (BinGen PoisOp)).app (Fin 3)
    ((binL (R := K) .bracket .bracket 1 - binL .bracket .bracket τ₁₂ -
      binR .bracket .bracket 1 :
      FreeBin K PoisOp (Fin 3))) =
    Finsupp.single (mL₁ .bracket .bracket) 1 - (Finsupp.single (mL₂ .bracket .bracket) 1 +
      Finsupp.single (mR .bracket .bracket) 1) := by
  rw [toSh_sub, toSh_sub, toSh_binL_one, toSh_binL_021, toSh_binR_one]
  abel

lemma toSh_y₂ : (toSh K (BinGen PoisOp)).app (Fin 3)
    ((binR (R := K) .bracket .mul 1 - binL .mul .bracket 1 -
      binL .mul .bracket τ₁₂ :
      FreeBin K PoisOp (Fin 3))) =
    Finsupp.single (mR .bracket .mul) 1 - (Finsupp.single (mL₁ .mul .bracket) 1 +
      Finsupp.single (mL₂ .mul .bracket) 1) := by
  rw [toSh_sub, toSh_sub, toSh_binL_one, toSh_binL_021, toSh_binR_one]
  abel

lemma toSh_y₃ : (toSh K (BinGen PoisOp)).app (Fin 3)
    ((binL (R := K) .bracket .mul τ₁₂ - binL .mul .bracket 1 +
      binR .mul .bracket 1 :
      FreeBin K PoisOp (Fin 3))) =
    Finsupp.single (mL₂ .bracket .mul) 1 - (Finsupp.single (mL₁ .mul .bracket) 1 -
      Finsupp.single (mR .mul .bracket) 1) := by
  rw [toSh_add, toSh_sub, toSh_binL_one, toSh_binL_021, toSh_binR_one]
  abel

lemma toSh_y₄ : (toSh K (BinGen PoisOp)).app (Fin 3)
    ((binL (R := K) .bracket .mul 1 - binL .mul .bracket τ₁₂ -
      binR .mul .bracket 1 :
      FreeBin K PoisOp (Fin 3))) =
    Finsupp.single (mL₁ .bracket .mul) 1 - (Finsupp.single (mL₂ .mul .bracket) 1 +
      Finsupp.single (mR .mul .bracket) 1) := by
  rw [toSh_sub, toSh_sub, toSh_binL_one, toSh_binL_021, toSh_binR_one]
  abel

lemma toSh_y₅ : (toSh K (BinGen PoisOp)).app (Fin 3)
    ((binR (R := K) .mul .mul 1 - binL .mul .mul 1 :
      FreeBin K PoisOp (Fin 3))) =
    Finsupp.single (mR .mul .mul) 1 - Finsupp.single (mL₁ .mul .mul) 1 := by
  rw [toSh_sub, toSh_binL_one, toSh_binR_one]

lemma toSh_y₆ : (toSh K (BinGen PoisOp)).app (Fin 3)
    ((binL (R := K) .mul .mul τ₁₂ - binL .mul .mul 1 :
      FreeBin K PoisOp (Fin 3))) =
    Finsupp.single (mL₂ .mul .mul) 1 - Finsupp.single (mL₁ .mul .mul) 1 := by
  rw [toSh_sub, toSh_binL_one, toSh_binL_021]

lemma toSh_comm : (toSh K (BinGen PoisOp)).app (Fin 2) (BinRel.comm K PoisOp.mul) =
    Finsupp.single (cor .mul 1) 1 - Finsupp.single (cor .mul (Equiv.swap 0 1)) 1 := by
  rw [BinRel.comm, toSh_sub, toSh_bin2, toSh_bin2, Equiv.symm_swap]
  rfl

lemma toSh_antisymm : (toSh K (BinGen PoisOp)).app (Fin 2) (BinRel.antisymm K PoisOp.bracket) =
    Finsupp.single (cor .bracket (Equiv.swap 0 1)) 1 - -Finsupp.single (cor .bracket 1) 1 := by
  rw [BinRel.antisymm, toSh_add, toSh_bin2, toSh_bin2, Equiv.symm_swap, sub_neg_eq_add, add_comm]
  rfl

/-- **The relations of the rules are sorted Poisson relations.** -/
theorem PR.rel_mem : ∀ r : PR, ∃ k, ∃ h : r.src = Finset.range (Fintype.card (Fin k)),
    Finsupp.mapDomain (SMono.cast h) (r.rel (K := K)) ∈ (TP K).sub (Fin k)
  | .jac => ⟨3, rfl, by
      erw [cast_rfl_eq]
      have := toSh_mem3 (y₁_mem (K := K))
      rw [toSh_y₁] at this
      exact this⟩
  | .leib₁ => ⟨3, rfl, by
      erw [cast_rfl_eq]
      have := toSh_mem3 (y₂_mem (K := K))
      rw [toSh_y₂] at this
      exact this⟩
  | .leib₂ => ⟨3, rfl, by
      erw [cast_rfl_eq]
      have := toSh_mem3 (y₃_mem (K := K))
      rw [toSh_y₃] at this
      exact this⟩
  | .leib₃ => ⟨3, rfl, by
      erw [cast_rfl_eq]
      have := toSh_mem3 (y₄_mem (K := K))
      rw [toSh_y₄] at this
      exact this⟩
  | .as₁ => ⟨3, rfl, by
      erw [cast_rfl_eq]
      have := toSh_mem3 (y₅_mem (K := K))
      rw [toSh_y₅] at this
      exact this⟩
  | .as₂ => ⟨3, rfl, by
      erw [cast_rfl_eq]
      have := toSh_mem3 (y₆_mem (K := K))
      rw [toSh_y₆] at this
      exact this⟩
  | .cm => ⟨2, rfl, by
      erw [cast_rfl_eq]
      have := neg_mem (toSh_mem2 (K := K) (y := BinRel.comm K PoisOp.mul) (Or.inl rfl))
      rw [toSh_comm, neg_sub] at this
      exact this⟩
  | .an => ⟨2, rfl, by
      erw [cast_rfl_eq]
      have := toSh_mem2 (K := K) (y := BinRel.antisymm K PoisOp.bracket) (Or.inr rfl)
      rw [toSh_antisymm] at this
      exact this⟩

lemma PR.src_eq : ∀ r : PR, ∃ n, (rules K).src r = Finset.range n
  | .jac | .leib₁ | .leib₂ | .leib₃ | .as₁ | .as₂ | .cm | .an => ⟨_, rfl⟩

/-- **The ideal of the rules lies in the ideal of the Poisson operad.** -/
theorem rules_le : (rules K).shuffleIdeal ≤ TP K := by
  rw [Rules.shuffleIdeal_eq_span _ PR.src_eq]
  refine ShuffleOperadIdeal.span_le.2 fun A _ _ x hx => ?_
  obtain ⟨r, h, rfl⟩ := hx
  obtain ⟨k, hk, hmem⟩ := PR.rel_mem (K := K) r
  have hc : Fintype.card A = k := by
    have := congrArg Finset.card (hk.symm.trans h)
    rw [Finset.card_range, Finset.card_range, Fintype.card_fin] at this
    exact this.symm
  have := (TP K).map_mem (Fintype.orderIsoFinOfCardEq A hc) hmem
  convert this using 1
  show _ = Finsupp.mapDomain _ (Finsupp.mapDomain _ _)
  rw [← Finsupp.mapDomain_comp]
  rfl

/-! ## Normal monomials -/

lemma not_normal {B : Finset ℕ} {U : SMono PE B} {p : List ℕ} (r : PR) {xs : ℕ → STree PE}
    (hU : U.1.get? p = some ((PR.lead r).1.subst xs))
    (hm : StrictMonoOn (fun a => (xs a).first) (r.src : Set ℕ)) : ¬ (rules K).Normal U :=
  fun h => h r _ (isSCtx_ctxOf U p (PR.lead r) xs hU hm) (ctxOf_self U p _ xs hU hm)

/-- The generator and the children of the root. -/
def kids : STree PE → Option (PoisOp × STree PE × STree PE)
  | leaf _ => none
  | node (BinGen.op g, _) c => some (g, c 0, c 1)

/-- **The conditions at the root** of a normal monomial: no product below a bracket, no product
as second input of a product, and the remaining leading monomials avoided. -/
def RootOK : PoisOp → STree PE → STree PE → Prop
  | .bracket, X, Y => (∀ g A B, kids X = some (g, A, B) → g = .bracket ∧ Y.first < B.first) ∧
      ∀ g A B, kids Y = some (g, A, B) → g = .bracket
  | .mul, X, Y => (∀ A B, kids X = some (.mul, A, B) → B.first < Y.first) ∧
      ∀ g A B, kids Y = some (g, A, B) → g = .bracket

/-- **Structurally normal trees.** -/
def NF : STree PE → Prop
  | leaf _ => True
  | node (BinGen.op g, σ) c => σ = 1 ∧ NF (c 0) ∧ NF (c 1) ∧ RootOK g (c 0) (c 1)

end PoisDim

end Operad
