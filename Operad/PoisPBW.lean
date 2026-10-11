/-
# The Poisson operad has `n!` operations of arity `n`

The Poisson operad is presented by the commutative product `m` and the antisymmetric bracket `b`,
so its underlying shuffle operad is presented by the four generators `m`, `b` and their
transposed versions (`Operad.FreeSet.presEquiv`). We bound its dimensions above by a rewriting
system and below by the Kirillov–Kostant model (`Operad.PoisDim.factorial_le_finrank`).

* **Sorting the monomials of arity three** (`PoisDim.toSh_binR_one`, `PoisDim.toSh_binL_one`,
  `PoisDim.toSh_binL_021`): the monomials `g(x₀, h(x₁, x₂))`, `g(h(x₀, x₁), x₂)` and
  `g(h(x₀, x₂), x₁)` of the free operad are the shuffle trees with untransposed generators.
* **The order** (`PoisDim.poisOrder`): the path order of the word order comparing first the
  number of brackets, then (reversed) the number of products, then lexicographically. It is
  admissible and well-founded.
* **The rules** (`PoisDim.rules`): Jacobi, three forms of the Leibniz rule, two forms of
  associativity, commutativity and antisymmetry, each with its leading monomial; their ideal lies in
  the ideal of the Poisson operad (`PoisDim.rules_le`), by explicit certificates in arity three.
* **Normal monomials** (`PoisDim.nf_of_normal`, `PoisDim.read_injective`): the monomials avoiding
  the leading monomials are left combs of products of Lie trees, and their reading words — brackets
  read left to right, products right to left — determine them. Hence there are at most `n!` of
  them (`PoisDim.card_irr_le`), and they span (`Operad.FreeSet.finrank_le_card_irr`).
* **The dimension** (`PoisDim.finrank_pois`, `PoisDim.finrank_pois_eq`):
  `dim Pois(n) = n!`.
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

/-- A vertex with any permutation of its inputs. -/
def ndσ (g : PoisOp) (σ : Equiv.Perm (Fin 2)) (x y : STree PE) : STree PE :=
  node (BinGen.op g, σ) ![x, y]

lemma node_eq_ndσ (g : PoisOp) (σ : Equiv.Perm (Fin 2)) (c : Fin 2 → STree PE) :
    node (E := PE) (BinGen.op g, σ) c = ndσ g σ (c 0) (c 1) := by
  rw [ndσ]
  congr 1
  funext i
  fin_cases i <;> rfl

lemma subst_ndσ (g : PoisOp) (σ : Equiv.Perm (Fin 2)) (x y : STree PE) (xs : ℕ → STree PE) :
    (ndσ g σ x y).subst xs = ndσ g σ (x.subst xs) (y.subst xs) := by
  rw [ndσ, subst_node, ndσ]
  congr 1
  funext i
  fin_cases i <;> rfl

lemma nd_eq (g : PoisOp) (x y : STree PE) : nd g x y = ndσ g 1 x y := rfl

@[simp] lemma first_ndσ (g : PoisOp) (σ : Equiv.Perm (Fin 2)) (x y : STree PE) :
    (ndσ g σ x y).first = x.first := by
  rw [ndσ, first_node _ _ (by norm_num)]
  rfl

@[simp] lemma labels_ndσ (g : PoisOp) (σ : Equiv.Perm (Fin 2)) (x y : STree PE) :
    (ndσ g σ x y).labels = x.labels + y.labels := by
  rw [ndσ, labels_node, Fin.sum_univ_two]
  rfl

lemma isShuffle_ndσ {g : PoisOp} {σ : Equiv.Perm (Fin 2)} {x y : STree PE}
    (h : (ndσ g σ x y).IsShuffle) : x.IsShuffle ∧ y.IsShuffle ∧ x.first < y.first :=
  ⟨h.child 0, h.child 1, h.mono (show (0 : Fin 2) < 1 by decide)⟩

/-- Three inputs. -/
def x3 (A B C : STree PE) : ℕ → STree PE := fun a => if a = 0 then A else if a = 1 then B else C

/-- Two inputs. -/
def x2 (A B : STree PE) : ℕ → STree PE := fun a => if a = 0 then A else B

lemma mono3 {A B C : STree PE} (h₁ : A.first < B.first) (h₂ : B.first < C.first) :
    StrictMonoOn (fun a => (x3 A B C a).first) (p3 : Set ℕ) := by
  intro a ha b hb hab
  have ha' : a < 3 := by simpa using ha
  have hb' : b < 3 := by simpa using hb
  interval_cases a <;> interval_cases b <;> first | omega | (simp only [x3]; simp_all; try omega)

lemma mono2 {A B : STree PE} (h : A.first < B.first) :
    StrictMonoOn (fun a => (x2 A B a).first) (p2 : Set ℕ) := by
  intro a ha b hb hab
  have ha' : a < 2 := by simpa using ha
  have hb' : b < 2 := by simpa using hb
  interval_cases a <;> interval_cases b
  all_goals first | omega | simpa [x2] using h

lemma subst_L₁ (g h : PoisOp) (A B C : STree PE) :
    (tL₁ g h).subst (x3 A B C) = nd g (nd h A B) C := by
  simp only [tL₁, nd_eq, subst_ndσ]
  rfl

lemma subst_L₂ (g h : PoisOp) (A B C : STree PE) :
    (tL₂ g h).subst (x3 A C B) = nd g (nd h A B) C := by
  simp only [tL₂, nd_eq, subst_ndσ]
  rfl

lemma subst_R (g h : PoisOp) (A B C : STree PE) :
    (tR g h).subst (x3 A B C) = nd g A (nd h B C) := by
  simp only [tR, nd_eq, subst_ndσ]
  rfl

lemma subst_cor (g : PoisOp) (σ : Equiv.Perm (Fin 2)) (A B : STree PE) :
    (cor g σ).1.subst (x2 A B) = ndσ g σ A B := by
  show (node (E := PE) (BinGen.op g, σ) fun j : Fin 2 => leaf j.1).subst _ = _
  rw [node_eq_ndσ, subst_ndσ]
  rfl

lemma kids_ndσ (g : PoisOp) (σ : Equiv.Perm (Fin 2)) (x y : STree PE) :
    kids (ndσ g σ x y) = some (g, x, y) := rfl

lemma NF_ndσ {g : PoisOp} {σ : Equiv.Perm (Fin 2)} {x y : STree PE} :
    NF (ndσ g σ x y) ↔ σ = 1 ∧ NF x ∧ NF y ∧ RootOK g x y := Iff.rfl

lemma eq_nd_of_kids {t A B : STree PE} {g : PoisOp} (ht : NF t)
    (h : kids t = some (g, A, B)) : t = nd g A B := by
  cases t with
  | leaf _ => exact absurd h (by simp [kids])
  | node e c =>
    obtain ⟨⟨g'⟩, σ⟩ := e
    rw [node_eq_ndσ] at ht h ⊢
    rw [kids_ndσ, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rw [ht.1]
    rfl

lemma perm2 (σ : Equiv.Perm (Fin 2)) : σ = 1 ∨ σ = Equiv.swap 0 1 := by
  revert σ
  decide

lemma first_ne {A B C : STree PE} {g h : PoisOp} (hs : (nd g (nd h A B) C).IsShuffle)
    (hn : (nd g (nd h A B) C).labels.Nodup) : B.first ≠ C.first := by
  obtain ⟨hAB, hC, -⟩ := isShuffle_ndσ hs
  obtain ⟨-, hB, -⟩ := isShuffle_ndσ hAB
  intro he
  rw [nd_eq, labels_ndσ, nd_eq, labels_ndσ] at hn
  have hd := (Multiset.nodup_add.1 hn).2.2
  exact Multiset.disjoint_left.1 hd (Multiset.mem_add.2 (Or.inr (first_mem hB)))
    (he ▸ first_mem hC)

/-- **Normal monomials are structurally normal.** -/
theorem nf_of_normal {B : Finset ℕ} {U : SMono PE B} (hU : (rules K).Normal U) :
    ∀ (t : STree PE) (p : List ℕ), U.1.get? p = some t → NF t := by
  intro t
  induction t with
  | leaf _ => intro _ _; trivial
  | node e c ih =>
    obtain ⟨⟨g⟩, σ⟩ := e
    intro p hp
    have hc : ∀ i : Fin 2, U.1.get? (p ++ [i.1]) = some (c i) := fun i => by
      rw [get?_append_of hp, get?_node_cons_fin, get?_nil]
    have h0 := ih 0 _ (hc 0)
    have h1 := ih 1 _ (hc 1)
    have hs := isShuffle_get? U.isShuffle hp
    have hn := Multiset.nodup_of_le (labels_get?_le hp) U.nodup
    rw [node_eq_ndσ] at hp hs hn ⊢
    have h01 := (isShuffle_ndσ hs).2.2
    set X := c 0
    set Y := c 1
    rcases perm2 σ with rfl | rfl
    swap
    · exact absurd hU (not_normal (K := K) (if g = .mul then .cm else .an) (xs := x2 X Y)
        (by cases g <;> (rw [hp]; exact congrArg some (subst_cor _ _ X Y).symm))
        (by cases g <;> exact mono2 h01))
    refine ⟨rfl, h0, h1, ?_⟩
    have hX := (isShuffle_ndσ hs).1
    have hY := (isShuffle_ndσ hs).2.1
    cases g with
    | bracket =>
      refine ⟨fun g' A B hk => ?_, fun g' A B hk => ?_⟩
      · have hXe := eq_nd_of_kids h0 hk
        rw [hXe] at hp hs hn hX h01
        have hAB := (isShuffle_ndσ hX).2.2
        rw [nd_eq, first_ndσ] at h01
        rcases lt_or_gt_of_ne (first_ne hs hn) with hlt | hgt
        · exfalso
          cases g'
          · exact not_normal (K := K) .leib₃ (xs := x3 A B Y)
              (by rw [hp]; exact congrArg some (subst_L₁ _ _ A B Y).symm) (mono3 hAB hlt) hU
          · exact not_normal (K := K) .jac (xs := x3 A B Y)
              (by rw [hp]; exact congrArg some (subst_L₁ _ _ A B Y).symm) (mono3 hAB hlt) hU
        · cases g'
          · exact absurd hU (not_normal (K := K) .leib₂ (xs := x3 A Y B)
              (by rw [hp]; exact congrArg some (subst_L₂ _ _ A B Y).symm) (mono3 h01 hgt))
          · exact ⟨rfl, hgt⟩
      · have hYe := eq_nd_of_kids h1 hk
        rw [hYe] at hp hY h01
        have hAB := (isShuffle_ndσ hY).2.2
        rw [nd_eq, first_ndσ] at h01
        cases g'
        · exact absurd hU (not_normal (K := K) .leib₁ (xs := x3 X A B)
            (by rw [hp]; exact congrArg some (subst_R _ _ X A B).symm) (mono3 h01 hAB))
        · rfl
    | mul =>
      refine ⟨fun A B hk => ?_, fun g' A B hk => ?_⟩
      · have hXe := eq_nd_of_kids h0 hk
        rw [hXe] at hp hs hn hX h01
        have hAB := (isShuffle_ndσ hX).2.2
        rw [nd_eq, first_ndσ] at h01
        rcases lt_or_gt_of_ne (first_ne hs hn) with hlt | hgt
        · exact hlt
        · exact absurd hU (not_normal (K := K) .as₂ (xs := x3 A Y B)
            (by rw [hp]; exact congrArg some (subst_L₂ _ _ A B Y).symm) (mono3 h01 hgt))
      · have hYe := eq_nd_of_kids h1 hk
        rw [hYe] at hp hY h01
        have hAB := (isShuffle_ndσ hY).2.2
        rw [nd_eq, first_ndσ] at h01
        cases g'
        · exact absurd hU (not_normal (K := K) .as₁ (xs := x3 X A B)
            (by rw [hp]; exact congrArg some (subst_R _ _ X A B).symm) (mono3 h01 hAB))
        · rfl

/-! ## Splitting words -/

lemma splitB_aux {u u' v v' m : List ℕ} {a a' : ℕ} (hu : u ≠ []) (h2 : ∀ x ∈ v, a < x)
    (h1' : ∀ x ∈ u'.tail, a' < x) (hm : u' = u ++ m) (hm' : a :: v = m ++ a' :: v') : m = [] := by
  cases m with
  | nil => rfl
  | cons b m' =>
    exfalso
    rw [List.cons_append, List.cons.injEq] at hm'
    obtain ⟨rfl, rfl⟩ := hm'
    have h₁ := h2 a' (by simp)
    obtain ⟨c, u₀, rfl⟩ := List.exists_cons_of_ne_nil hu
    have h₂ := h1' a (by rw [hm]; simp)
    omega

/-- **Splitting a bracket word** at the least letter of its tail. -/
lemma splitB {u u' v v' : List ℕ} {a a' : ℕ} (hu : u ≠ []) (hu' : u' ≠ [])
    (h1 : ∀ x ∈ u.tail, a < x) (h2 : ∀ x ∈ v, a < x) (h1' : ∀ x ∈ u'.tail, a' < x)
    (h2' : ∀ x ∈ v', a' < x) (h : u ++ a :: v = u' ++ a' :: v') :
    u = u' ∧ a :: v = a' :: v' := by
  rcases List.append_eq_append_iff.1 h with ⟨m, hm, hm'⟩ | ⟨m, hm, hm'⟩
  · obtain rfl := splitB_aux hu h2 h1' hm hm'
    rw [List.append_nil] at hm
    exact ⟨hm.symm, hm'⟩
  · obtain rfl := splitB_aux hu' h2' h1 hm hm'
    rw [List.append_nil] at hm
    exact ⟨hm, hm'.symm⟩

lemma splitM_aux {u u' v v' m : List ℕ} {a a' h : ℕ} (ha : a < h) (hu' : ∀ x ∈ u', h ≤ x)
    (hm : u' = u ++ m) (hm' : a :: v = m ++ a' :: v') : m = [] := by
  cases m with
  | nil => rfl
  | cons b m' =>
    exfalso
    rw [List.cons_append, List.cons.injEq] at hm'
    obtain ⟨rfl, -⟩ := hm'
    have := hu' a (by rw [hm]; simp)
    omega

/-- **Splitting a product word** at the first letter below its head. -/
lemma splitM {u u' v v' : List ℕ} {h h' a a' : ℕ} (hu : ∀ x ∈ u, h ≤ x) (ha : a < h)
    (hu' : ∀ x ∈ u', h' ≤ x) (ha' : a' < h') (e : (h :: u) ++ a :: v = (h' :: u') ++ a' :: v') :
    h :: u = h' :: u' ∧ a :: v = a' :: v' := by
  rw [List.cons_append, List.cons_append, List.cons.injEq] at e
  obtain ⟨rfl, e⟩ := e
  rcases List.append_eq_append_iff.1 e with ⟨m, hm, hm'⟩ | ⟨m, hm, hm'⟩
  · obtain rfl := splitM_aux ha hu' hm hm'
    rw [List.append_nil] at hm
    exact ⟨by rw [hm], hm'⟩
  · obtain rfl := splitM_aux ha' hu hm hm'
    rw [List.append_nil] at hm
    exact ⟨by rw [hm], hm'.symm⟩

/-! ## The reading word -/

/-- **The reading word**: the leaves under a bracket read left to right, under a product right
to left. -/
def read : STree PE → List ℕ
  | leaf a => [a]
  | node (BinGen.op .mul, _) c => read (c 1) ++ read (c 0)
  | node (BinGen.op .bracket, _) c => read (c 0) ++ read (c 1)

lemma read_mul (σ : Equiv.Perm (Fin 2)) (x y : STree PE) :
    read (ndσ .mul σ x y) = read y ++ read x := rfl

lemma read_bracket (σ : Equiv.Perm (Fin 2)) (x y : STree PE) :
    read (ndσ .bracket σ x y) = read x ++ read y := rfl

/-- **The reading word is an ordering of the leaves.** -/
theorem coe_read (t : STree PE) : (read t : Multiset ℕ) = t.labels := by
  induction t with
  | leaf a => rfl
  | node e c ih =>
    obtain ⟨⟨g⟩, σ⟩ := e
    rw [node_eq_ndσ, labels_ndσ, ← ih 0, ← ih 1]
    cases g
    · rw [read_mul, ← Multiset.coe_add, add_comm]
    · rw [read_bracket, ← Multiset.coe_add]

lemma read_ne_nil (t : STree PE) : read t ≠ [] := by
  induction t with
  | leaf a => simp [read]
  | node e c ih =>
    obtain ⟨⟨g⟩, σ⟩ := e
    rw [node_eq_ndσ]
    cases g
    · rw [read_mul]
      exact List.append_ne_nil_of_left_ne_nil (ih 1) _
    · rw [read_bracket]
      exact List.append_ne_nil_of_left_ne_nil (ih 0) _

lemma first_le_read {t : STree PE} (hs : t.IsShuffle) {x : ℕ} (hx : x ∈ read t) :
    t.first ≤ x :=
  first_le hs x (by rw [← coe_read]; exact Multiset.mem_coe.2 hx)

lemma nodup_read {t : STree PE} (hn : t.labels.Nodup) : (read t).Nodup := by
  rw [← coe_read] at hn
  exact Multiset.coe_nodup.1 hn

/-- **A Lie tree**: no product at the root. -/
def IsLie (t : STree PE) : Prop := ∀ g A B, kids t = some (g, A, B) → g = .bracket

section NFParts

variable {g : PoisOp} {σ : Equiv.Perm (Fin 2)} {x y : STree PE}

lemma NF.one (h : NF (ndσ g σ x y)) : σ = 1 := h.1
lemma NF.left (h : NF (ndσ g σ x y)) : NF x := h.2.1
lemma NF.right (h : NF (ndσ g σ x y)) : NF y := h.2.2.1

lemma NF.lie_right (h : NF (ndσ g σ x y)) : IsLie y := by
  have := h.2.2.2
  cases g
  · exact this.2
  · exact this.2

lemma NF.br_left (h : NF (ndσ .bracket σ x y)) :
    ∀ g A B, kids x = some (g, A, B) → g = .bracket ∧ y.first < B.first := h.2.2.2.1

lemma NF.mul_left (h : NF (ndσ .mul σ x y)) :
    ∀ A B, kids x = some (.mul, A, B) → B.first < y.first := h.2.2.2.1

lemma isLie_bracket : IsLie (ndσ .bracket σ x y) := fun g A B h => by
  rw [kids_ndσ, Option.some.injEq, Prod.mk.injEq] at h
  exact h.1.symm

lemma NF.lie_left (h : NF (ndσ .bracket σ x y)) : IsLie x := fun g A B hk => (h.br_left g A B hk).1

end NFParts

lemma read_lie (t : STree PE) (ht : NF t) (hL : IsLie t) : ∃ v, read t = t.first :: v := by
  induction t with
  | leaf a => exact ⟨[], rfl⟩
  | node e c ih =>
    obtain ⟨⟨g⟩, σ⟩ := e
    rw [node_eq_ndσ] at ht hL ⊢
    obtain rfl := hL _ _ _ (kids_ndσ _ _ _ _)
    obtain ⟨v, hv⟩ := ih 0 ht.left ht.lie_left
    exact ⟨v ++ read (c 1), by rw [read_bracket, hv, first_ndσ]; rfl⟩

lemma read_lie_strict {t : STree PE} (ht : NF t) (hs : t.IsShuffle) (hn : t.labels.Nodup)
    (hL : IsLie t) : ∃ v, read t = t.first :: v ∧ ∀ x ∈ v, t.first < x := by
  obtain ⟨v, hv⟩ := read_lie t ht hL
  have hnd := nodup_read hn
  rw [hv, List.nodup_cons] at hnd
  refine ⟨v, hv, fun x hx => lt_of_le_of_ne (first_le_read hs (by rw [hv]; simp [hx])) ?_⟩
  rintro rfl
  exact hnd.1 hx

/-- **The tail of the left input of a bracket** comes after its right input. -/
lemma tail_bracket (X : STree PE) : ∀ Y : STree PE, NF (ndσ .bracket 1 X Y) →
    (ndσ .bracket 1 X Y).IsShuffle → ∀ x ∈ (read X).tail, Y.first < x := by
  induction X with
  | leaf a => intro _ _ _ x hx; simp [read] at hx
  | node e c ih =>
    obtain ⟨⟨g⟩, σ⟩ := e
    intro Y ht hs x hx
    rw [node_eq_ndσ] at ht hs hx
    obtain ⟨rfl, hBY⟩ := ht.br_left _ _ _ (kids_ndσ _ _ _ _)
    have hX := ht.left
    obtain rfl := hX.one
    have hXs := (isShuffle_ndσ hs).1
    have ih' := ih 0 (c 1) hX hXs
    rw [read_bracket, List.tail_append_of_ne_nil (read_ne_nil _), List.mem_append] at hx
    rcases hx with hx | hx
    · exact hBY.trans (ih' x hx)
    · exact hBY.trans_le (first_le_read (isShuffle_ndσ hXs).2.1 hx)

/-- **The left input of a product begins below its right input.** -/
lemma head_mul (X Y : STree PE) (ht : NF (ndσ .mul 1 X Y)) (hs : (ndσ .mul 1 X Y).IsShuffle) :
    ∃ a v, read X = a :: v ∧ a < Y.first := by
  have hXY := (isShuffle_ndσ hs).2.2
  cases X with
  | leaf a => exact ⟨a, [], rfl, hXY⟩
  | node e c =>
    obtain ⟨⟨g⟩, σ⟩ := e
    rw [node_eq_ndσ] at ht hs hXY ⊢
    have hX := ht.left
    cases g
    · obtain ⟨v, hv⟩ := read_lie (c 1) hX.right hX.lie_right
      exact ⟨(c 1).first, v ++ read (c 0), by rw [read_mul, hv]; rfl,
        ht.mul_left _ _ (kids_ndσ _ _ _ _)⟩
    · obtain ⟨v, hv⟩ := read_lie _ hX isLie_bracket
      exact ⟨_, v, hv, hXY⟩

lemma read_bracket_ne_mul {X Y X' Y' : STree PE} (ht : NF (ndσ .bracket 1 X Y))
    (hs : (ndσ .bracket 1 X Y).IsShuffle) (ht' : NF (ndσ .mul 1 X' Y'))
    (hs' : (ndσ .mul 1 X' Y').IsShuffle) (hn' : (ndσ .mul 1 X' Y').labels.Nodup) :
    read (ndσ .bracket 1 X Y) ≠ read (ndσ .mul 1 X' Y') := by
  intro h
  obtain ⟨v, hv⟩ := read_lie _ ht isLie_bracket
  rw [labels_ndσ] at hn'
  have hn'' := Multiset.nodup_add.1 hn'
  obtain ⟨w, hw, -⟩ := read_lie_strict ht'.right (isShuffle_ndσ hs').2.1 hn''.2.1 ht'.lie_right
  have hX' := (isShuffle_ndσ hs').2.2
  have hmem : X'.first ∈ read (ndσ .bracket 1 X Y) := by
    rw [h, read_mul]
    exact List.mem_append_right _ (Multiset.mem_coe.1 (by
      rw [coe_read]; exact first_mem (isShuffle_ndσ hs').1))
  have hle := first_le_read hs hmem
  rw [h, read_mul, hw, List.cons_append, List.cons.injEq] at hv
  rw [first_ndσ] at hle hv
  omega

/-- **The reading word determines a structurally normal shuffle tree.** -/
theorem read_injective (t : STree PE) : ∀ t' : STree PE, NF t → NF t' → t.IsShuffle →
    t'.IsShuffle → t.labels.Nodup → t'.labels.Nodup → read t = read t' → t = t' := by
  induction t with
  | leaf a =>
    intro t' _ _ _ _ _ _ h
    cases t' with
    | leaf b => simpa [read] using h
    | node e c =>
      obtain ⟨⟨g⟩, σ⟩ := e
      rw [node_eq_ndσ] at h
      have := congrArg List.length h
      have h0 := List.length_pos_of_ne_nil (read_ne_nil (c 0))
      have h1 := List.length_pos_of_ne_nil (read_ne_nil (c 1))
      cases g
      · rw [read_mul, List.length_append] at this
        simp only [read, List.length_singleton] at this
        omega
      · rw [read_bracket, List.length_append] at this
        simp only [read, List.length_singleton] at this
        omega
  | node e c ih =>
    obtain ⟨⟨g⟩, σ⟩ := e
    intro t' ht ht' hs hs' hn hn' h
    rw [node_eq_ndσ] at ht hs hn h ⊢
    obtain rfl := ht.one
    cases t' with
    | leaf b =>
      have := congrArg List.length h
      have h0 := List.length_pos_of_ne_nil (read_ne_nil (c 0))
      have h1 := List.length_pos_of_ne_nil (read_ne_nil (c 1))
      cases g
      · rw [read_mul, List.length_append] at this
        simp only [read, List.length_singleton] at this
        omega
      · rw [read_bracket, List.length_append] at this
        simp only [read, List.length_singleton] at this
        omega
    | node e' c' =>
      obtain ⟨⟨g'⟩, σ'⟩ := e'
      rw [node_eq_ndσ] at ht' hs' hn' h ⊢
      obtain rfl := ht'.one
      rw [labels_ndσ] at hn hn'
      have hN := Multiset.nodup_add.1 hn
      have hN' := Multiset.nodup_add.1 hn'
      rw [← labels_ndσ (g := g) (σ := 1)] at hn
      rw [← labels_ndσ (g := g') (σ := 1)] at hn'
      have hS := isShuffle_ndσ hs
      have hS' := isShuffle_ndσ hs'
      have key : read (c 0) = read (c' 0) → read (c 1) = read (c' 1) →
          ndσ g 1 (c 0) (c 1) = ndσ g 1 (c' 0) (c' 1) := fun e₀ e₁ => by
        rw [ih 0 _ ht.left ht'.left hS.1 hS'.1 hN.1 hN'.1 e₀,
          ih 1 _ ht.right ht'.right hS.2.1 hS'.2.1 hN.2.1 hN'.2.1 e₁]
      obtain ⟨u, hu, hu'⟩ := read_lie_strict ht.right hS.2.1 hN.2.1 ht.lie_right
      obtain ⟨u', hv, hv'⟩ := read_lie_strict ht'.right hS'.2.1 hN'.2.1 ht'.lie_right
      cases g <;> cases g'
      · obtain ⟨a, w, ha, ha'⟩ := head_mul _ _ ht hs
        obtain ⟨a', w', hb, hb'⟩ := head_mul _ _ ht' hs'
        rw [read_mul, read_mul, hu, hv, ha, hb] at h
        obtain ⟨e₁, e₂⟩ := splitM (fun x hx => (hu' x hx).le) ha' (fun x hx => (hv' x hx).le)
          hb' h
        rw [← hu, ← hv] at e₁
        rw [← ha, ← hb] at e₂
        exact key e₂ e₁
      · exact absurd h.symm (read_bracket_ne_mul ht' hs' ht hs hn)
      · exact absurd h (read_bracket_ne_mul ht hs ht' hs' hn')
      · have hX := tail_bracket _ _ ht hs
        have hX' := tail_bracket _ _ ht' hs'
        rw [read_bracket, read_bracket, hu, hv] at h
        obtain ⟨e₁, e₂⟩ := splitB (read_ne_nil _) (read_ne_nil _) hX hu' hX' hv' h
        rw [← hu, ← hv] at e₂
        exact key e₁ e₂

/-! ## The upper bound -/

/-- **There are at most `n!` normal monomials on `n` leaves.** -/
theorem card_irr_le (n : ℕ) : Finite ((rules K).rw (Finset.range n)).Irr ∧
    Nat.card ((rules K).rw (Finset.range n)).Irr ≤ n.factorial := by
  set L := (List.range n).permutations.toFinset
  have hmem : ∀ U : SMono PE (Finset.range n), read U.1 ∈ L := fun U => by
    rw [List.mem_toFinset, List.mem_permutations, ← Multiset.coe_eq_coe, coe_read, U.labels_eq]
    rfl
  let f : ((rules K).rw (Finset.range n)).Irr → L := fun U => ⟨read U.1.1, hmem U.1⟩
  have hf : Function.Injective f := by
    rintro ⟨U, hU⟩ ⟨U', hU'⟩ h
    have h' : read U.1 = read U'.1 := congrArg Subtype.val h
    rw [(rules K).mem_irr_iff] at hU hU'
    exact Subtype.ext (Subtype.ext (read_injective U.1 U'.1
      (nf_of_normal hU U.1 [] (get?_nil _)) (nf_of_normal hU' U'.1 [] (get?_nil _))
      U.isShuffle U'.isShuffle U.nodup U'.nodup h'))
  refine ⟨Finite.of_injective f hf, ?_⟩
  have hL : Nat.card L = n.factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup
      (List.nodup_permutations _ List.nodup_range), List.length_permutations,
      List.length_range]
  exact (Nat.card_le_card_of_injective f hf).trans hL.le

variable (K) in
/-- **The Poisson operad has at most `n!` operations of arity `n`**, and finitely many: the normal
monomials of the rules span. -/
theorem finite_finrank_le (A : Type) [Fintype A] [LinearOrder A] :
    Module.Finite K (Pois K A) ∧ Module.finrank K (Pois K A) ≤ (Fintype.card A).factorial := by
  have := (card_irr_le (K := K) (Fintype.card A)).1
  obtain ⟨h1, h2⟩ := FreeSet.finrank_le_card_irr (rel23 (r₂P K) (r₃P K)) (rules K) rules_le A
  exact ⟨h1, h2.trans (card_irr_le _).2⟩

variable (K) in
/-- **The Poisson operad has exactly `n!` operations of arity `n`.** -/
theorem finrank_pois {n : ℕ} (hn : 0 < n) :
    Module.finrank K (Pois K (Finset.range n)) = n.factorial := by
  obtain ⟨hfin, hle⟩ := finite_finrank_le K (Finset.range n)
  rw [Fintype.card_coe, Finset.card_range] at hle
  exact le_antisymm hle (@factorial_le_finrank K _ n hn hfin)

variable (K) in
/-- **The Poisson operad has exactly `n!` operations on `n` inputs**, on any nonempty finite set
of inputs. -/
theorem finrank_pois_eq (A : Type) [Fintype A] [DecidableEq A] [Nonempty A] :
    Module.finrank K (Pois K A) = (Fintype.card A).factorial := by
  let e : A ≃ Finset.range (Fintype.card A) := Fintype.equivOfCardEq (by simp)
  rw [(SymOperad.mapEquiv (R := K) (P := Pois K) e).finrank_eq,
    finrank_pois K Fintype.card_pos]

end PoisDim

end Operad
