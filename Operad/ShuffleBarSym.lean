/-
# The bar construction of the free graded operad on binary generators

Step (2b) of the bridge between symmetric and shuffle operads (Dotsenko–Khoroshkin). Let `E` be a
graded linear species over a commutative ring `K` with an **even** basis `c k` of each
`E (Fin k)` indexed by `BinGen G k`, `G` a finite type (`hc`: `par false (c k β) = c k β`), so
that `E` is concentrated in arity two and `E (Fin 2)` is free on `G`. Let `T = FreeGrL K E`.

* **The ideal** (`GrOperadIdeal.atLeastTwo`): for a graded operad without operations in arity
  zero, the operations with at least two inputs form an ideal, and it has no operations with at
  most one input (`GrOperadIdeal.atLeastTwo_hI1`, the hypothesis `hI1` of `Koszul.isKoszul_iff`).
  For `T` it is `ShuffleBarSym.Ibar`, written `Ī` below; `T` vanishes in arity zero
  (`ShuffleBarSym.free_zero`).
* **Bases.** `T(A)` has the basis of binary shuffle trees `ShuffleBarSym.tBasis` (step 2a through
  `LTree.binMonoEquiv`), of even vectors (`ShuffleBarSym.par_tBasis`). So `Ī (Fin k)` and the
  generators `sĪ (Fin k)` of the bar construction have the basis `ShuffleBarSym.genBasis`, indexed
  by the binary shuffle trees on `0, …, k - 1` with `k ≥ 2` (`ShuffleBarSym.VMono`), of odd
  vectors (`ShuffleBarSym.par_genBasis`). By step 2a, **`B(T, Ī) A = FreeGrL K (sĪ) A` has the
  basis `ShuffleBarSym.barBasis` of shuffle trees whose vertices are labelled by binary shuffle
  trees** (`ShuffleBarSym.barBasisN` on `Fin n`, with leaves `0, …, n - 1`).
* **Bar trees** (`ShuffleBarSym.toBar`): grafting the bar tree of each child on the corresponding
  leaf of the vertex monomial, along a cut edge (`ShuffleBarSym.cutRoot`). It is a shuffle tree with
  the same leaves and least leaf, uncut at the root (`ShuffleBarSym.isShuffle_toBar`,
  `ShuffleBarSym.labels_toBar`, `ShuffleBarSym.minLabel_toBar`, `ShuffleBarSym.rootFlag_toBar`),
  injective on shuffle trees (`ShuffleBarSym.toBar_injective`, through `ShuffleBar.top` and
  `ShuffleBar.hang`), and every valid bar tree is one (`ShuffleBarSym.exists_toBar`). So
  **`ShuffleBarSym.treeEquiv n` is a bijection from the shuffle trees of monomials on
  `0, …, n - 1` to the valid bar trees whose labels are a permutation of `0, …, n - 1`**
  (`ShuffleBarSym.barSet`). A tree with a vertex and `s` vertices in all has `s - 1` cut edges
  (`ShuffleBarSym.card_cutKeys_toBar`), so in arity `n ≥ 2` its bar tree is admissible of degree
  `s` (`ShuffleBarSym.adm_iff`).
* **The comparison** (`ShuffleBarSym.Φ`, `ShuffleBarSym.ΦL`): a linear equivalence from
  `B(T, Ī)(Fin n)` onto `Finsupp.supported K K (barSet G n)`, the span of the bar trees of arity
  `n`. **Sign convention**: a basis vector `t` goes to `sign t • single (toBar t) 1`
  (`ShuffleBarSym.Φ_barBasisN`), where `ShuffleBarSym.sign t = (-1)^inv`, `inv` the number of
  inversions of the keys `(least leaf, number of leaves)` of the non-root vertices of `t` listed in
  preorder (`ShuffleBarSym.preKeys`). The preorder is the order in which `FreeGrL` composes the
  vertices; the key order is the one of `ShuffleBar.sgn`.
* **Vertex counts.** The evaluation of a shuffle tree with `s` vertices lies in the eigenspace
  `FreeGrL.vx s` of the vertex count (`FreeGrL.shEv_mem_vx`, for any homogeneous basis as in step
  2a), by splitting off a child that is not a leaf and composing it back (`FreeGrL.comp_shEv`).
* **Degrees.** `ShuffleBarSym.deg n s` is the span of the basis vectors of trees with `s`
  vertices; the degrees exhaust `B(T, Ī)(Fin n)` (`ShuffleBarSym.iSup_deg`), and over a field of
  characteristic zero `deg n s = FreeGrL.vx s` (`ShuffleBarSym.deg_eq_vx`), so the bar
  differential maps `deg n (s + 1)` to `deg n s` (`ShuffleBarSym.d_mem_deg`). For `n ≥ 2` and `K` a
  field **`ΦL` maps `deg n s` onto `ShuffleBar.C K n s`** (`ShuffleBarSym.map_ΦL_deg`), so on
  `deg n (s + 1)` both `ΦL ∘ Bar.d` and `ShuffleBar.d ∘ ΦL` land in `C K n s`
  (`ShuffleBarSym.ΦL_d_mem_C`).
* **The bar differential is the differential of a merge structure** (`Bar.mergeSp`,
  `Bar.mergeSp_fn`, `Bar.d_eq_mergeSp_d`), for any graded operad and ideal, so it satisfies the
  Leibniz rule `d (x ∘ᵢ y) = d x ∘ᵢ y + (-1)^|x| x ∘ᵢ d y + x ⊛ᵢ y` (`Bar.d_comp`) and the laws of
  merge-composition in `MergeSp.lean`.

Not proved here: `ΦL ∘ Bar.d = ShuffleBar.d K ∘ ΦL`. The expected proof expands `Bar.d` on a basis
vector by `Bar.d_comp` and `FreeGrL.comp_shEv`. Merging a cut edge gives the basis vector of the
merged tree with its children in the planar order of the merged vertex; sorting them into the
shuffle order costs the Koszul sign of the odd vertices moved, which is the change of `sign` for
the reordered preorder. The sign `(-1)^(position of the edge in preorder)` of `FreeGrL` then
becomes `ShuffleBar.sgn`, the position of the edge in key order, because `sign` counts exactly the
pairs of vertices whose two orders differ. Also open: the hypotheses `hcompl` and `hone` of
`Koszul.isKoszul_iff`, which concern the presented operad of step 2c.
-/
import Operad.ShuffleKoszul
import Operad.ShuffleContext
import Operad.ShuffleFreeGrL
import Operad.ShuffleFreeL
import Operad.MergeSp
import Operad.BarWeights

universe u v w

namespace Operad

open Sym GerBV

/-! ## The ideal of the operations with at least two inputs -/

namespace GrOperadIdeal

variable (R : Type u) [CommRing R] (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]

include R in
/-- An operad without operations in arity zero has none on any empty set of inputs. -/
lemma eq_zero_of_card_eq_zero (h0 : ∀ y : P (Fin 0), y = 0) {B : Type} [Fintype B]
    [DecidableEq B] (hB : Fintype.card B = 0) (y : P B) : y = 0 := by
  let e : B ≃ Fin 0 := Fintype.equivFinOfCardEq hB
  have : y = GrOperad.map (R := R) e.symm (GrOperad.map (R := R) e y) := by
    rw [← GrOperad.map_trans, Equiv.self_trans_symm, GrOperad.map_refl]
  rw [this, h0 (GrOperad.map (R := R) e y), map_zero]

/-- **The ideal of the operations with at least two inputs**, for a graded operad without
operations in arity zero: all of `P A` when `A` has at least two elements, and zero otherwise. -/
noncomputable def atLeastTwo (h0 : ∀ y : P (Fin 0), y = 0) : GrOperadIdeal R P where
  sub A := if 2 ≤ Fintype.card A then ⊤ else ⊥
  par_mem b {A} _ _ {x} hx := by
    split_ifs at hx ⊢
    · trivial
    · rw [Submodule.mem_bot] at hx ⊢
      rw [hx, map_zero]
  map_mem {A B} _ _ _ _ e {x} hx := by
    rw [Fintype.card_congr e.symm] at *
    split_ifs at hx ⊢
    · trivial
    · rw [Submodule.mem_bot] at hx ⊢
      rw [hx, map_zero]
  comp_mem_left {A B} _ _ _ _ i {x} y hx := by
    split_ifs with h
    · trivial
    rw [Submodule.mem_bot]
    split_ifs at hx with hA
    · have hB : Fintype.card B = 0 := by
        rw [Fintype.card_sum, Reg.card_without] at h
        omega
      rw [eq_zero_of_card_eq_zero R P h0 hB y, map_zero]
    · rw [Submodule.mem_bot] at hx
      rw [hx, LinearMap.map_zero₂]
  comp_mem_right {A B} _ _ _ _ i x {y} hy := by
    split_ifs with h
    · trivial
    rw [Submodule.mem_bot]
    split_ifs at hy with hB
    · have hA : 0 < Fintype.card A := Fintype.card_pos_iff.2 ⟨i⟩
      rw [Fintype.card_sum, Reg.card_without] at h
      omega
    · rw [Submodule.mem_bot] at hy
      rw [hy, map_zero]

variable {R P}

lemma atLeastTwo_sub_of_le {h0 : ∀ y : P (Fin 0), y = 0} {A : Type} [Fintype A] [DecidableEq A]
    (h : 2 ≤ Fintype.card A) : (atLeastTwo R P h0).sub A = ⊤ :=
  if_pos h

lemma atLeastTwo_sub_of_lt {h0 : ∀ y : P (Fin 0), y = 0} {A : Type} [Fintype A] [DecidableEq A]
    (h : Fintype.card A < 2) : (atLeastTwo R P h0).sub A = ⊥ :=
  if_neg (by omega)

/-- **The ideal has no operations with at most one input**, the hypothesis `hI1` of
`Koszul.isKoszul_iff`. -/
theorem atLeastTwo_hI1 (h0 : ∀ y : P (Fin 0), y = 0) (B : Type) [Fintype B] [DecidableEq B]
    (hB : Fintype.card B ≤ 1) (y : P B) (hy : y ∈ (atLeastTwo R P h0).sub B) : y = 0 := by
  rw [atLeastTwo_sub_of_lt (by omega), Submodule.mem_bot] at hy
  exact hy

end GrOperadIdeal

/-! ## The bar differential as the differential of a merge structure -/

namespace Bar

open FreeGr

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  (I : GrOperadIdeal R P)

/-- The value of merging two elements of the suspension of the ideal, `x` of parity `b`:
`s a ⊛_q s c = (-1)^{|a|} s (a ∘_q c)`, in the positions of the merged vertex. -/
noncomputable def msVal {k l : ℕ} (b : Bool) (x : BarGen I (Fin k)) (q : Fin k)
    (y : BarGen I (Fin l)) (m : ℕ) (h : m + 1 = k + l) : BarGen I (Fin m) :=
  IdealSp.mk I (σ R (!b) • GrOperad.map (R := R) (posEquivF q l m h)
      (GrOperad.comp (R := R) q (IdealSp.val I x) (IdealSp.val I y)))
    (Submodule.smul_mem _ _ (I.map_mem _ (I.comp_mem_left _ _ (IdealSp.mem I x))))

lemma val_msVal {k l : ℕ} (b : Bool) (x : BarGen I (Fin k)) (q : Fin k)
    (y : BarGen I (Fin l)) (m : ℕ) (h : m + 1 = k + l) :
    IdealSp.val I (msVal I b x q y m h) = σ R (!b) • GrOperad.map (R := R) (posEquivF q l m h)
      (GrOperad.comp (R := R) q (IdealSp.val I x) (IdealSp.val I y)) := rfl

/-- **The merge structure of the bar construction** on the suspension of the ideal. -/
noncomputable def mergeSp : MergeSp R (BarGen I) where
  val b x q y m h := msVal I b x q y m h
  add_left b x x' q y m h := IdealSp.ext I (by
    change σ R (!b) • GrOperad.map (R := R) _ (GrOperad.comp (R := R) q
        (IdealSp.val I x + IdealSp.val I x') (IdealSp.val I y)) =
      σ R (!b) • GrOperad.map (R := R) _ (GrOperad.comp (R := R) q (IdealSp.val I x)
        (IdealSp.val I y)) + σ R (!b) • GrOperad.map (R := R) _ (GrOperad.comp (R := R) q
        (IdealSp.val I x') (IdealSp.val I y))
    rw [map_add, LinearMap.add_apply, map_add, smul_add])
  smul_left b c x q y m h := IdealSp.ext I (by
    change σ R (!b) • GrOperad.map (R := R) _ (GrOperad.comp (R := R) q
        (c • IdealSp.val I x) (IdealSp.val I y)) =
      c • (σ R (!b) • GrOperad.map (R := R) _ (GrOperad.comp (R := R) q (IdealSp.val I x)
        (IdealSp.val I y)))
    rw [LinearMap.map_smul₂, map_smul, smul_comm])
  add_right b x q y y' m h := IdealSp.ext I (by
    change σ R (!b) • GrOperad.map (R := R) _ (GrOperad.comp (R := R) q
        (IdealSp.val I x) (IdealSp.val I y + IdealSp.val I y')) =
      σ R (!b) • GrOperad.map (R := R) _ (GrOperad.comp (R := R) q (IdealSp.val I x)
        (IdealSp.val I y)) + σ R (!b) • GrOperad.map (R := R) _ (GrOperad.comp (R := R) q
        (IdealSp.val I x) (IdealSp.val I y'))
    rw [map_add, map_add, smul_add])
  smul_right b c x q y m h := IdealSp.ext I (by
    change σ R (!b) • GrOperad.map (R := R) _ (GrOperad.comp (R := R) q
        (IdealSp.val I x) (c • IdealSp.val I y)) =
      c • (σ R (!b) • GrOperad.map (R := R) _ (GrOperad.comp (R := R) q (IdealSp.val I x)
        (IdealSp.val I y)))
    rw [map_smul, map_smul, smul_comm])
  map_right := fun {k l} b x q τ y m h => IdealSp.ext I (by
    show σ R (!b) • GrOperad.map (R := R) (posEquivF q l m h) (GrOperad.comp (R := R) q
        (IdealSp.val I x) (GrOperad.map (R := R) τ (IdealSp.val I y))) =
      GrOperad.map (R := R) _ (σ R (!b) • GrOperad.map (R := R) (posEquivF q l m h)
        (GrOperad.comp (R := R) q (IdealSp.val I x) (IdealSp.val I y)))
    rw [map_smul]
    congr 1
    have e := GrOperad.map_comp (R := R) (P := P) (Equiv.refl (Fin k)) τ q (IdealSp.val I x)
      (IdealSp.val I y)
    rw [GrOperad.map_refl] at e
    have e' : GrOperad.comp (R := R) q (IdealSp.val I x) (GrOperad.map (R := R) τ (IdealSp.val I y))
        = GrOperad.map (R := R) (compEquiv (Equiv.refl (Fin k)) τ q)
            (GrOperad.comp (R := R) q (IdealSp.val I x) (IdealSp.val I y)) := e.symm
    rw [e', ← GrOperad.map_trans]
    erw [← GrOperad.map_trans]
    congr 2
    ext t
    simp)
  map_left := fun {k l} b τ x q y m h => IdealSp.ext I (by
    show σ R (!b) • GrOperad.map (R := R) (posEquivF (τ q) l m h) (GrOperad.comp (R := R) (τ q)
        (GrOperad.map (R := R) τ (IdealSp.val I x)) (IdealSp.val I y)) =
      GrOperad.map (R := R) _ (σ R (!b) • GrOperad.map (R := R) (posEquivF q l m h)
        (GrOperad.comp (R := R) q (IdealSp.val I x) (IdealSp.val I y)))
    rw [map_smul]
    congr 1
    have e := GrOperad.map_comp (R := R) (P := P) τ (Equiv.refl (Fin l)) q (IdealSp.val I x)
      (IdealSp.val I y)
    rw [GrOperad.map_refl] at e
    rw [← e, ← GrOperad.map_trans, ← GrOperad.map_trans]
    congr 2
    ext t
    simp)
  par b b' x q y m h hx hy := IdealSp.ext I (by
    have hx' : GrOperad.par (R := R) (!b) (IdealSp.val I x) = IdealSp.val I x :=
      congrArg (IdealSp.val I) hx
    have hy' : GrOperad.par (R := R) (!b') (IdealSp.val I y) = IdealSp.val I y :=
      congrArg (IdealSp.val I) hy
    change GrOperad.par (R := R) (!!(xor b b')) (IdealSp.val I (msVal I b x q y m h)) =
      IdealSp.val I (msVal I b x q y m h)
    rw [Bool.not_not, val_msVal, map_smul, ← GrOperad.map_par, ← hx', ← hy']
    have := GrOperad.comp_par (R := R) q (!b) (!b') (IdealSp.val I x) (IdealSp.val I y)
    rw [show xor (!b) (!b') = xor b b' by cases b <;> cases b' <;> rfl] at this
    rw [this])

/-- **The merge function of the merge structure is that of the bar construction.** -/
theorem mergeSp_fn : (mergeSp I).fn = barMerge I := by
  funext k l x j y m
  unfold MergeSp.fn barMerge
  split_ifs
  · rfl
  · rfl

/-- **The bar differential is the differential of the merge structure**, so it satisfies the
Leibniz rule up to merge-composition, `MergeSp.d_comp`. -/
theorem d_eq_mergeSp_d (A : Type) [Fintype A] [DecidableEq A] : d I A = (mergeSp I).d A := by
  unfold d MergeSp.d
  congr 1

/-- **The Leibniz rule of the bar differential**:
`d (x ∘ᵢ y) = d x ∘ᵢ y + (-1)^|x| x ∘ᵢ d y + x ⊛ᵢ y`. -/
theorem d_comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (X : FreeGrL R (BarGen I) A) (Y : FreeGrL R (BarGen I) B) :
    d I _ (GrOperad.comp (R := R) (P := FreeGrL R (BarGen I)) i X Y)
      = GrOperad.comp (R := R) i (d I A X) Y
        + GrOperad.comp (R := R) i (GrOperad.tw (R := R) true X) (d I B Y)
        + (mergeSp I).mc i X Y := by
  rw [d_eq_mergeSp_d, d_eq_mergeSp_d, d_eq_mergeSp_d]
  exact (mergeSp I).d_comp i X Y

end Bar

/-! ## The vertex count of the shuffle basis -/

section Vx

open Function STree

namespace FreeGrL

variable {R : Type u} [CommRing R]
  {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)] [GrSpecies R W]
  {B : ℕ → Type w} (b : ∀ k, Module.Basis (B k) R (W (Fin k)))

/-- The inputs of a composite at a leaf `m`, named by their values. -/
def labSplit {Y Y₁ Y₂ : Finset ℕ} {m : ℕ} (hm : m ∈ Y₁)
    (hY : ∀ x, x ∈ Y ↔ (x ∈ Y₁ ∧ x ≠ m) ∨ x ∈ Y₂) (hd : ∀ x ∈ Y₁, x ≠ m → x ∉ Y₂) :
    Lab Y ≃ Without (Lab Y₁) ⟨m, hm⟩ ⊕ Lab Y₂ where
  toFun x := if hx : x.1 ∈ Y₂ then Sum.inr ⟨x.1, hx⟩ else
    Sum.inl ⟨⟨x.1, (((hY x.1).1 x.2).resolve_right hx).1⟩,
      fun h => (((hY x.1).1 x.2).resolve_right hx).2 (congrArg Subtype.val h)⟩
  invFun u := match u with
    | Sum.inl a => ⟨a.1.1, (hY _).2 (Or.inl ⟨a.1.2, fun h => a.2 (Subtype.ext h)⟩)⟩
    | Sum.inr c => ⟨c.1, (hY _).2 (Or.inr c.2)⟩
  left_inv x := by
    by_cases hx : x.1 ∈ Y₂
    · simp [hx]
    · simp [hx]
  right_inv u := by
    rcases u with a | c
    · have : a.1.1 ∉ Y₂ := hd _ a.1.2 fun h => a.2 (Subtype.ext h)
      simp [this]
    · simp [c.2]

lemma sval_labSplit {Y Y₁ Y₂ : Finset ℕ} {m : ℕ} (hm : m ∈ Y₁)
    (hY : ∀ x, x ∈ Y ↔ (x ∈ Y₁ ∧ x ≠ m) ∨ x ∈ Y₂) (hd : ∀ x ∈ Y₁, x ≠ m → x ∉ Y₂) (x : Lab Y) :
    sval (labSplit hm hY hd x) = x.1 := by
  by_cases hx : x.1 ∈ Y₂
  · simp [labSplit, hx]
  · simp [labSplit, hx]

lemma labels_eq_toFinset {t : STree B} (h : t.labels.Nodup) :
    t.labels = t.labels.toFinset.val := by
  rw [Multiset.toFinset_val, Multiset.dedup_eq_self.2 h]

variable {p : ∀ k, B k → Bool}
  (hb : ∀ k (β : B k), GrSpecies.par (R := R) (p k β) (b k β) = b k β)
include hb

/-- **The evaluation of a shuffle tree with `s` vertices has `s` vertices**: it lies in the
eigenspace `vx s` of the vertex count. -/
theorem shEv_mem_vx : ∀ (n : ℕ) (t : STree B), t.weight ≤ n → t.IsShuffle →
    ∀ (Y : Finset ℕ) (h : t.labels = Y.val), shEv b t Y h ∈ vx R W t.weight (Lab Y)
  | _, .leaf a, _, _, Y, h => by
    rw [shEv_leaf, weight]
    have hY : Y = {a} := Finset.val_inj.1 (by rw [← h]; rfl)
    subst hY
    rw [unitL_eq (Equiv.ofUnique Unit (Lab {a}))]
    exact unit_mem_eig _
  | 0, .node β c, hw, _, _, _ => by simp [weight] at hw
  | n + 1, .node (k := k) β c, hw, ht, Y, h => by
    have hnd : (STree.node β c).labels.Nodup := h ▸ Y.nodup
    by_cases hall : ∀ j, ∃ a, c j = .leaf a
    · choose a ha using hall
      have hmem : ∀ j, a j ∈ Y := fun j => by
        rw [← Finset.mem_val, ← h]
        exact mem_labels_node.2 ⟨j, by rw [ha j]; simp⟩
      have hinj : Injective a := fun i j hij => by
        by_contra hne
        have := disjoint_of_node hnd hne
        rw [ha i, ha j, hij] at this
        simp at this
      have hsurj : ∀ y : Lab Y, ∃ j, a j = y.1 := fun y => by
        have hy : y.1 ∈ (STree.node β c).labels := by rw [h]; exact y.2
        obtain ⟨j, hj⟩ := mem_labels_node.1 hy
        rw [ha j] at hj
        exact ⟨j, (Multiset.mem_singleton.1 hj).symm⟩
      let θ : Fin k ≃ Lab Y := Equiv.ofBijective (fun j => ⟨a j, hmem j⟩)
        ⟨fun i j hij => hinj (congrArg Subtype.val hij), fun y => by
          obtain ⟨j, hj⟩ := hsurj y
          exact ⟨j, Subtype.ext hj⟩⟩
      have hc : c = fun j => STree.leaf (θ j).1 := funext fun j => ha j
      have hw1 : (STree.node β c).weight = 1 := by
        simp [weight, ha]
      subst hc
      rw [hw1, shEv_corolla]
      exact map_mem_eig θ (ι_mem_vx _)
    · push Not at hall
      obtain ⟨j, hj⟩ := hall
      set t₂ := c j with ht₂
      set m := t₂.first with hm_def
      have hjs : t₂.IsShuffle := ht.child j
      have hmj : m ∈ t₂.labels := first_mem hjs
      let c₁ : Fin k → STree B := update c j (.leaf m)
      let t₁ : STree B := .node β c₁
      have hle : t₁.labels ≤ (STree.node β c).labels := by
        simp only [t₁, labels_node]
        refine Finset.sum_le_sum fun i _ => ?_
        by_cases hij : i = j
        · subst hij
          simp only [c₁, update_self, labels_leaf]
          exact Multiset.singleton_le.2 hmj
        · simp only [c₁, update_of_ne hij]
          exact le_rfl
      have hnd₁ : t₁.labels.Nodup := Multiset.nodup_of_le hle hnd
      have hnd₂ : t₂.labels.Nodup := nodup_of_node hnd j
      set Y₁ := t₁.labels.toFinset
      set Y₂ := t₂.labels.toFinset
      have h₁ : t₁.labels = Y₁.val := labels_eq_toFinset hnd₁
      have h₂ : t₂.labels = Y₂.val := labels_eq_toFinset hnd₂
      have hm₁ : m ∈ Y₁ := Multiset.mem_toFinset.2
        (mem_labels_node.2 ⟨j, by simp [c₁]⟩)
      have hother : ∀ i, i ≠ j → ∀ x ∈ (c i).labels, x ∉ t₂.labels := fun i hij x hx hx' =>
        Multiset.disjoint_left.1 (disjoint_of_node hnd hij) hx hx'
      have hsub : t₁.subst (update STree.leaf m t₂) = STree.node β c := by
        simp only [t₁, subst_node]
        congr 1
        funext i
        by_cases hij : i = j
        · subst hij
          simp [c₁, ht₂]
        · simp only [c₁, update_of_ne hij]
          rw [subst_congr (ys := STree.leaf) (c i) fun x hx => update_of_ne
            (fun hxm => hother i hij x hx (by rw [hxm]; exact hmj)) _ _, subst_leaf]
      have hY : ∀ x, x ∈ Y ↔ (x ∈ Y₁ ∧ x ≠ m) ∨ x ∈ Y₂ := fun x => by
        rw [← Finset.mem_val, ← h, ← hsub, labels_subst, h₁]
        simp only [Multiset.mem_bind, Finset.mem_val]
        constructor
        · rintro ⟨y, hy, hxy⟩
          by_cases hym : y = m
          · subst hym
            rw [update_self] at hxy
            exact Or.inr (Multiset.mem_toFinset.2 hxy)
          · rw [update_of_ne hym, labels_leaf, Multiset.mem_singleton] at hxy
            subst hxy
            exact Or.inl ⟨hy, hym⟩
        · rintro (⟨hx, hxm⟩ | hx)
          · exact ⟨x, hx, by rw [update_of_ne hxm]; simp⟩
          · exact ⟨m, hm₁, by rw [update_self]; exact Multiset.mem_toFinset.1 hx⟩
      have hd : ∀ x ∈ Y₁, x ≠ m → x ∉ Y₂ := fun x hx hxm hx₂ => by
        obtain ⟨i, hi⟩ := mem_labels_node.1 (Multiset.mem_toFinset.1 hx)
        by_cases hij : i = j
        · subst hij
          simp [c₁] at hi
          exact hxm hi
        · simp only [c₁, update_of_ne hij] at hi
          exact hother i hij x hi (Multiset.mem_toFinset.1 hx₂)
      have hh : (t₁.subst (update STree.leaf m t₂)).labels = Y.val := by rw [hsub, h]
      let E := labSplit hm₁ hY hd
      have hcomp := comp_shEv b hb t₂ Y₂ h₂ t₁ Y₁ h₁ m hm₁ Y hh E (sval_labSplit hm₁ hY hd)
      have hev := map_shEv b hsub rfl hh h (Equiv.refl _) fun _ => rfl
      rw [GrOperad.map_refl] at hev
      rw [hev] at hcomp
      have hwsum : t₁.weight + t₂.weight = (STree.node β c).weight := by
        have hupd : ∀ i, (c₁ i).weight = update (fun i => (c i).weight) j 0 i := fun i => by
          by_cases hij : i = j
          · subst hij
            simp [c₁]
          · simp [c₁, update_of_ne hij]
        simp only [t₁, weight, hupd]
        rw [Finset.sum_update_of_mem (Finset.mem_univ j),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ j), Finset.sdiff_singleton_eq_erase, ht₂]
        omega
      have ht₂w : 1 ≤ t₂.weight := by
        rcases hj' : t₂ with a | ⟨β', c'⟩
        · exact absurd hj' (hj a)
        · simp [weight]
      have ht₁s : t₁.IsShuffle := by
        refine ⟨ht.pos, fun i => ?_, ?_⟩
        · by_cases hij : i = j
          · subst hij
            simp [c₁]
          · simp only [c₁, update_of_ne hij]
            exact ht.child i
        · have : (fun i => (c₁ i).first) = fun i => (c i).first := funext fun i => by
            by_cases hij : i = j
            · subst hij
              simp [c₁, hm_def, ht₂]
            · simp [c₁, update_of_ne hij]
          rw [this]
          exact ht.mono
      have ih₁ := shEv_mem_vx n t₁ (by omega) ht₁s Y₁ h₁
      have ht₁w : 1 ≤ t₁.weight := by
        simp only [t₁, weight]
        omega
      have ih₂ := shEv_mem_vx n t₂ (by omega) hjs Y₂ h₂
      have hc' := comp_mem_eig (a := GrSpEnd.id R W) (⟨m, hm₁⟩ : Lab Y₁) ih₁ ih₂
      rw [hcomp, hwsum] at hc'
      have := map_mem_eig E.symm (Submodule.smul_mem _ (σ R (vpar p t₂ && vaft p t₁ m)) hc')
      rwa [smul_smul, σ_mul_self, one_smul, ← GrOperad.map_trans, Equiv.self_trans_symm,
        GrOperad.map_refl] at this

end FreeGrL

end Vx

end Operad

namespace Operad

namespace ShuffleBarSym

open Sym GerBV LTree

/-! ## The bases -/

section Bases

variable {K : Type u} [CommRing K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {G : Type} [Fintype G] [DecidableEq G]
  (c : ∀ k, Module.Basis (BinGen G k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen G k), GrSpecies.par (R := K) false (c k β) = c k β)

lemma vpar_false {B : ℕ → Type*} : ∀ t : STree B, STree.vpar (fun _ _ => false) t = false
  | .leaf _ => rfl
  | .node _ ch => by
    rw [STree.vpar_node]
    simp only [vpar_false (ch _)]
    simp [GrEnd.tot]

/-- **The binary-tree basis of the free graded operad on even binary generators**: the evaluations
of the binary shuffle trees, through `LTree.binMonoEquiv`. -/
noncomputable def tBasis (A : Type) [Fintype A] [LinearOrder A] :
    Module.Basis {t // t ∈ LTree.monomials (E := G) (Fintype.card A)} K (FreeGrL K E A) :=
  (FreeGrL.shuffleBasis c (p := fun _ _ => false) hc A).reindex (LTree.binMonoEquiv _).symm

lemma tBasis_apply (A : Type) [Fintype A] [LinearOrder A]
    (t : {t // t ∈ LTree.monomials (E := G) (Fintype.card A)}) :
    tBasis c hc A t = FreeGrL.shuffleBasis c (p := fun _ _ => false) hc A
      (LTree.binMonoEquiv _ t) := by
  rw [tBasis, Module.Basis.reindex_apply, Equiv.symm_symm]

/-- **The basis vectors are even.** -/
lemma par_tBasis (A : Type) [Fintype A] [LinearOrder A]
    (t : {t // t ∈ LTree.monomials (E := G) (Fintype.card A)}) :
    GrOperad.par (R := K) false (tBasis c hc A t) = tBasis c hc A t := by
  rw [tBasis_apply]
  have := FreeGrL.par_shuffleBasis c (p := fun _ _ => false) hc A (LTree.binMonoEquiv _ t)
  rwa [vpar_false] at this

include hc in
/-- **The free graded operad on binary generators vanishes in arity zero.** -/
lemma free_zero (y : FreeGrL K E (Fin 0)) : y = 0 := by
  haveI : IsEmpty {t // t ∈ LTree.monomials (E := G) (Fintype.card (Fin 0))} :=
    ⟨fun ⟨t, ht⟩ => by
      rw [Fintype.card_fin] at ht
      simp [LTree.monomials] at ht⟩
  exact (tBasis c hc (Fin 0)).repr.injective (Subsingleton.elim _ _)

variable (K E) in
/-- **The ideal `Ī` of the free graded operad** of the operations with at least two inputs. -/
noncomputable abbrev Ibar : GrOperadIdeal K (FreeGrL K E) :=
  GrOperadIdeal.atLeastTwo K (FreeGrL K E) (free_zero c hc)

variable (G) in
/-- **The decorations of the vertices of the bar construction**: the binary shuffle trees on
`0, …, k - 1` with at least two leaves. -/
abbrev VMono (k : ℕ) : Type := {t : LTree G // t ∈ LTree.monomials k ∧ 2 ≤ k}

instance : IsEmpty (VMono G 0) := ⟨fun t => by omega⟩

/-- The binary shuffle trees with at least two leaves, as indices of `tBasis`. -/
def vmonoEquiv {k : ℕ} (h : 2 ≤ k) :
    {t // t ∈ LTree.monomials (E := G) (Fintype.card (Fin k))} ≃ VMono G k where
  toFun t := ⟨t.1, by simpa using t.2, h⟩
  invFun t := ⟨t.1, by simpa using t.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The basis of `Ī (Fin k)`**: the binary shuffle trees with `k ≥ 2` leaves. -/
noncomputable def idealBasis (k : ℕ) : Module.Basis (VMono G k) K ((Ibar K E c hc).sub (Fin k)) :=
  if h : 2 ≤ k then
    ((tBasis c hc (Fin k)).map (LinearEquiv.ofTop _
      (GrOperadIdeal.atLeastTwo_sub_of_le (by simpa using h))).symm).reindex (vmonoEquiv h)
  else
    haveI : IsEmpty (VMono G k) := ⟨fun t => h t.2.2⟩
    haveI : Subsingleton ((Ibar K E c hc).sub (Fin k)) := by
      rw [GrOperadIdeal.atLeastTwo_sub_of_lt (by simp; omega)]
      infer_instance
    Module.Basis.empty _

lemma idealBasis_apply {k : ℕ} (t : VMono G k) :
    (idealBasis c hc k t : FreeGrL K E (Fin k)) =
      tBasis c hc (Fin k) ⟨t.1, by simpa using t.2.1⟩ := by
  rw [idealBasis, dif_pos t.2.2, Module.Basis.reindex_apply, Module.Basis.map_apply,
    LinearEquiv.coe_ofTop_symm_apply]
  rfl

/-- **The basis of the generators `sĪ (Fin k)` of the bar construction.** -/
noncomputable def genBasis (k : ℕ) : Module.Basis (VMono G k) K (BarGen (Ibar K E c hc) (Fin k)) :=
  idealBasis c hc k

/-- **The generators of the bar construction are odd.** -/
lemma par_genBasis (k : ℕ) (t : VMono G k) :
    GrSpecies.par (R := K) ((fun _ _ => true) k t) (genBasis c hc k t) = genBasis c hc k t := by
  refine IdealSp.ext _ ?_
  show GrOperad.par (R := K) false (idealBasis c hc k t : FreeGrL K E (Fin k)) = _
  rw [idealBasis_apply, par_tBasis]
  exact (idealBasis_apply c hc t).symm

/-- **The shuffle basis of the bar construction `B(T, Ī)`**: on a finite linear order `A`, the
shuffle trees on the positions of `A` whose vertices are binary shuffle trees with at least two
leaves (`FreeGrL.shuffleBasis` on the basis `genBasis` of `sĪ`). -/
noncomputable def barBasis (A : Type) [Fintype A] [LinearOrder A] :
    Module.Basis (STree.SMono (VMono G) (Finset.range (Fintype.card A))) K
      (BarCoop (Ibar K E c hc) A) :=
  FreeGrL.shuffleBasis (genBasis c hc) (par_genBasis c hc) A

end Bases

/-! ## Bar trees from shuffle trees of monomials -/

section Trees

open ShuffleBar STree

variable {G : Type}

/-- **Cut the edge above the root** of a bar tree. -/
def cutRoot : BarTree G → BarTree G
  | LTree.leaf a => LTree.leaf a
  | LTree.node d l r => LTree.node (d.1, true) l r

/-- **Uncut the edge above the root** of a bar tree. -/
def uncutRoot : BarTree G → BarTree G
  | LTree.leaf a => LTree.leaf a
  | LTree.node d l r => LTree.node (d.1, false) l r

@[simp] lemma labels_cutRoot (y : BarTree G) : (cutRoot y).labels = y.labels := by
  cases y <;> rfl

@[simp] lemma minLabel_cutRoot (y : BarTree G) : (cutRoot y).minLabel = y.minLabel := by
  cases y <;> rfl

@[simp] lemma isShuffle_cutRoot (y : BarTree G) : (cutRoot y).IsShuffle ↔ y.IsShuffle := by
  cases y <;> rfl

@[simp] lemma labels_uncutRoot (y : BarTree G) : (uncutRoot y).labels = y.labels := by
  cases y <;> rfl

@[simp] lemma minLabel_uncutRoot (y : BarTree G) : (uncutRoot y).minLabel = y.minLabel := by
  cases y <;> rfl

@[simp] lemma isShuffle_uncutRoot (y : BarTree G) : (uncutRoot y).IsShuffle ↔ y.IsShuffle := by
  cases y <;> rfl

@[simp] lemma size_uncutRoot (y : BarTree G) : (uncutRoot y).size = y.size := by
  cases y <;> rfl

lemma rootFlag_uncutRoot (y : BarTree G) : rootFlag (uncutRoot y) = false := by
  cases y <;> rfl

lemma uncutRoot_cutRoot {y : BarTree G} (hy : rootFlag y = false) : uncutRoot (cutRoot y) = y := by
  cases y with
  | leaf => rfl
  | node d l r =>
    obtain ⟨e, b⟩ := d
    simp only [rootFlag] at hy
    subst hy
    rfl

lemma cutRoot_injective {y y' : BarTree G} (hy : rootFlag y = false) (hy' : rootFlag y' = false)
    (h : cutRoot y = cutRoot y') : y = y' := by
  rw [← uncutRoot_cutRoot hy, ← uncutRoot_cutRoot hy', h]

lemma card_cutKeys_cutRoot_node {d : G × Bool} {l r : BarTree G} (hd : d.2 = false) :
    (cutKeys (cutRoot (LTree.node d l r))).card = (cutKeys (LTree.node d l r)).card + 1 := by
  have e1 : cutKeys (cutRoot (LTree.node d l r)) =
      insert (key (LTree.node d l r)) (cutKeys l ∪ cutKeys r) := by
    simp only [cutRoot, ShuffleBar.cutKeys]
    rfl
  have e2 : cutKeys (LTree.node d l r) = cutKeys l ∪ cutKeys r := by
    simp [ShuffleBar.cutKeys, hd]
  rw [e1, e2, Finset.card_insert_of_notMem]
  intro h
  rcases Finset.mem_union.1 h with h | h
  · exact key_not_mem_left d l r (cutKeys_subset l h)
  · exact key_not_mem_right d l r (cutKeys_subset r h)

variable [Fintype G] [DecidableEq G]

/-- **The bar tree of a shuffle tree of monomials**: each vertex, a binary shuffle tree on
`0, …, k - 1`, with the bar trees of its children grafted on its leaves along cut edges. -/
def toBar : STree (VMono G) → BarTree G
  | STree.leaf a => LTree.leaf a
  | STree.node (k := k) m ch => (liftW false m.1).plug fun a =>
      if h : a < k then cutRoot (toBar (ch ⟨a, h⟩)) else LTree.leaf a

/-- The inputs grafted on the top vertex. -/
def kids {k : ℕ} (ch : Fin k → STree (VMono G)) (a : ℕ) : BarTree G :=
  if h : a < k then cutRoot (toBar (ch ⟨a, h⟩)) else LTree.leaf a

lemma toBar_node {k : ℕ} (m : VMono G k) (ch : Fin k → STree (VMono G)) :
    toBar (STree.node m ch) = (liftW false m.1).plug (kids ch) := rfl

lemma kids_fin {k : ℕ} (ch : Fin k → STree (VMono G)) (j : Fin k) :
    kids ch j = cutRoot (toBar (ch j)) := by
  rw [kids, dif_pos j.2]

lemma kids_of_lt {k : ℕ} (ch : Fin k → STree (VMono G)) {a : ℕ} (h : a < k) :
    kids ch a = cutRoot (toBar (ch ⟨a, h⟩)) := by
  rw [kids, dif_pos h]

lemma VMono.perm {k : ℕ} (m : VMono G k) : m.1.labels.Perm (List.range k) :=
  ((LTree.mem_monomials k m.1).1 m.2.1).2

lemma VMono.isShuffle {k : ℕ} (m : VMono G k) : m.1.IsShuffle :=
  ((LTree.mem_monomials k m.1).1 m.2.1).1

lemma VMono.lt {k : ℕ} (m : VMono G k) {a : ℕ} (ha : a ∈ m.1.labels) : a < k :=
  List.mem_range.1 (m.perm.subset ha)

lemma VMono.mem {k : ℕ} (m : VMono G k) {a : ℕ} (ha : a < k) : a ∈ m.1.labels :=
  m.perm.symm.subset (List.mem_range.2 ha)

lemma VMono.exists_node {k : ℕ} (m : VMono G k) : ∃ e l r, m.1 = LTree.node e l r := by
  rcases h : m.1 with a | ⟨e, l, r⟩
  · have h1 := m.perm.length_eq
    rw [h, List.length_range] at h1
    have h2 := m.2.2
    simp only [LTree.labels_leaf, List.length_singleton] at h1
    omega
  · exact ⟨e, l, r, rfl⟩

lemma VMono.minLabel {k : ℕ} (m : VMono G k) : m.1.minLabel = 0 := by
  have h0 : 0 ∈ m.1.labels := m.mem (by have := m.2.2; omega)
  exact Nat.le_zero.1 (LTree.minLabel_le_of_mem _ h0)

lemma bind_kids {k : ℕ} (m : VMono G k) (f : ℕ → Multiset ℕ) :
    Multiset.bind (m.1.labels : Multiset ℕ) f = ∑ j : Fin k, f j := by
  rw [Multiset.coe_eq_coe.2 m.perm, Multiset.coe_range,
    Fin.sum_univ_eq_sum_range f, Finset.sum_eq_multiset_sum, Multiset.bind]
  rfl

/-- **The leaves of the bar tree are those of the shuffle tree.** -/
theorem labels_toBar : ∀ t : STree (VMono G), ((toBar t).labels : Multiset ℕ) = t.labels
  | STree.leaf _ => rfl
  | STree.node m ch => by
    rw [toBar_node, labels_plug, labels_liftW, ← Multiset.coe_bind, bind_kids m, STree.labels]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [kids_fin, labels_cutRoot, labels_toBar (ch j)]

lemma rootFlag_toBar : ∀ t : STree (VMono G), rootFlag (toBar t) = false
  | STree.leaf _ => rfl
  | STree.node m ch => by
    obtain ⟨e, l, r, h⟩ := m.exists_node
    rw [toBar_node, h]
    rfl

lemma strictOn_kids {k : ℕ} (m : VMono G k) {ch : Fin k → STree (VMono G)}
    (hmin : ∀ j, (toBar (ch j)).minLabel = (ch j).first)
    (hmono : StrictMono fun j => (ch j).first) :
    StrictOn (fun a => (kids ch a).minLabel) (liftW false m.1) := by
  intro a ha b hb hab
  rw [labels_liftW] at ha hb
  have ha' := m.lt ha
  have hb' := m.lt hb
  show (kids ch a).minLabel < (kids ch b).minLabel
  rw [kids_of_lt ch ha', kids_of_lt ch hb', minLabel_cutRoot, minLabel_cutRoot, hmin, hmin]
  exact hmono (show (⟨a, ha'⟩ : Fin k) < ⟨b, hb'⟩ from hab)

/-- **The least leaf of the bar tree** is that of the shuffle tree. -/
theorem minLabel_toBar : ∀ t : STree (VMono G), t.IsShuffle → (toBar t).minLabel = t.first
  | STree.leaf _, _ => rfl
  | STree.node (k := k) m ch, ht => by
    have hmin : ∀ j, (toBar (ch j)).minLabel = (ch j).first := fun j =>
      minLabel_toBar (ch j) (ht.child j)
    rw [toBar_node, minLabel_plug_of_strictOn _ (strictOn_kids m hmin ht.mono),
      show (liftW false m.1).minLabel = m.1.minLabel by
        rw [← minLabel_mapDec Prod.fst, liftW_mapDec],
      m.minLabel, first_node _ _ ht.pos, ← hmin, kids_of_lt ch ht.pos, minLabel_cutRoot]

/-- **The bar tree of a shuffle tree is a shuffle tree.** -/
theorem isShuffle_toBar : ∀ t : STree (VMono G), t.IsShuffle → (toBar t).IsShuffle
  | STree.leaf _, _ => trivial
  | STree.node (k := k) m ch, ht => by
    rw [toBar_node]
    refine isShuffle_plug_of_strictOn _ ((isShuffle_liftW _ _).2 m.isShuffle)
      (strictOn_kids m (fun j => minLabel_toBar (ch j) (ht.child j)) ht.mono) fun a ha => ?_
    rw [labels_liftW] at ha
    rw [kids_of_lt ch (m.lt ha), isShuffle_cutRoot]
    exact isShuffle_toBar _ (ht.child _)

lemma mem_labels_toBar {t : STree (VMono G)} {a : ℕ} : a ∈ (toBar t).labels ↔ a ∈ t.labels := by
  rw [← labels_toBar t, Multiset.mem_coe]

lemma nodup_toBar {t : STree (VMono G)} (h : t.labels.Nodup) : (toBar t).labels.Nodup := by
  rw [← Multiset.coe_nodup, labels_toBar]
  exact h

lemma toFinset_labels {k : ℕ} (m : VMono G k) : m.1.labels.toFinset = Finset.range k := by
  ext a
  rw [List.mem_toFinset, Finset.mem_range]
  exact ⟨m.lt, m.mem⟩

lemma cutKeys_toBar_node {k : ℕ} (m : VMono G k) (ch : Fin k → STree (VMono G)) :
    ShuffleBar.cutKeys (toBar (STree.node m ch)) =
      (Finset.range k).biUnion fun a => ShuffleBar.cutKeys (kids ch a) := by
  obtain ⟨e, l, r, h⟩ := m.exists_node
  rw [toBar_node, h, cutKeys_plug_liftW, if_neg Bool.false_ne_true, Finset.empty_union, ← h,
    toFinset_labels]

lemma disjoint_cutKeys_kids {k : ℕ} {m : VMono G k} {ch : Fin k → STree (VMono G)}
    (hnd : (STree.node m ch).labels.Nodup) :
    (↑(Finset.range k) : Set ℕ).PairwiseDisjoint fun a => ShuffleBar.cutKeys (kids ch a) := by
  intro a ha b hb hab
  have ha' : a < k := Finset.mem_range.1 ha
  have hb' : b < k := Finset.mem_range.1 hb
  have hd := disjoint_of_node hnd (show (⟨a, ha'⟩ : Fin k) ≠ ⟨b, hb'⟩ from
    fun h => hab (congrArg Fin.val h))
  refine Finset.disjoint_left.2 fun κ h1 h2 => ?_
  simp only [kids_of_lt ch ha', kids_of_lt ch hb'] at h1 h2
  have m1 := (mem_nodeKeys_labels _ (cutKeys_subset _ h1)).1
  have m2 := (mem_nodeKeys_labels _ (cutKeys_subset _ h2)).1
  rw [labels_cutRoot, mem_labels_toBar] at m1 m2
  exact Multiset.disjoint_left.1 hd m1 m2

lemma toBar_node_eq {k : ℕ} (m : VMono G k) (ch : Fin k → STree (VMono G)) :
    ∃ e l r, toBar (STree.node m ch) = LTree.node (e, false) l r := by
  obtain ⟨e, l, r, h⟩ := m.exists_node
  refine ⟨e, (unflag l).plug (kids ch), (unflag r).plug (kids ch), ?_⟩
  rw [toBar_node, h]
  rfl

/-- **The number of cut edges** of the bar tree of a shuffle tree, the edge above its root cut, is
its number of vertices. -/
theorem card_cutKeys_cutRoot_toBar : ∀ t : STree (VMono G), t.labels.Nodup →
    (ShuffleBar.cutKeys (cutRoot (toBar t))).card = t.weight
  | STree.leaf _, _ => rfl
  | STree.node (k := k) m ch, hnd => by
    obtain ⟨e, l, r, hT⟩ := toBar_node_eq m ch
    rw [hT, card_cutKeys_cutRoot_node rfl, ← hT, cutKeys_toBar_node,
      Finset.card_biUnion (disjoint_cutKeys_kids hnd), STree.weight, add_comm,
      ← Fin.sum_univ_eq_sum_range (fun a => (ShuffleBar.cutKeys (kids ch a)).card)]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [kids_fin, card_cutKeys_cutRoot_toBar (ch j) (nodup_of_node hnd j)]

/-- **The number of components** of the bar tree of a shuffle tree with a vertex is its number of
vertices. -/
theorem card_cutKeys_toBar {k : ℕ} (m : VMono G k) (ch : Fin k → STree (VMono G))
    (hnd : (STree.node m ch).labels.Nodup) :
    (ShuffleBar.cutKeys (toBar (STree.node m ch))).card + 1 = (STree.node m ch).weight := by
  rw [← card_cutKeys_cutRoot_toBar _ hnd]
  obtain ⟨e, l, r, hT⟩ := toBar_node_eq m ch
  rw [hT, card_cutKeys_cutRoot_node rfl]

/-! ### Injectivity -/

omit [Fintype G] [DecidableEq G] in
lemma topAux_cutRoot (y : BarTree G) : topAux (cutRoot y) = LTree.leaf y.minLabel := by
  cases y with
  | leaf => rfl
  | node d l r => simp [cutRoot, topAux]

omit [Fintype G] [DecidableEq G] in
lemma hangAux_cutRoot (y : BarTree G) : hangAux (cutRoot y) y.minLabel = cutRoot y := by
  cases y with
  | leaf => rfl
  | node d l r => simp [cutRoot, hangAux]

omit [Fintype G] [DecidableEq G] in
lemma pick_eq {ins : ℕ → BarTree G} {a j : ℕ} :
    ∀ {ks : List ℕ}, j ∈ ks → a ∈ (topAux (ins j)).labels →
      (∀ i ∈ ks, i ≠ j → a ∉ (topAux (ins i)).labels) → pick ins a ks = hangAux (ins j) a
  | [], hj, _, _ => absurd hj List.not_mem_nil
  | i :: ks, hj, ha, hother => by
    rw [pick]
    by_cases hij : i = j
    · subst hij
      rw [if_pos ha]
    · rw [if_neg (hother i (by simp) hij)]
      exact pick_eq (List.mem_of_ne_of_mem (Ne.symm hij) hj) ha
        fun i' hi' => hother i' (List.mem_cons_of_mem _ hi')

/-- The least leaves of the children, as a function of the leaves of the top vertex. -/
def firstOf {k : ℕ} (ch : Fin k → STree (VMono G)) (a : ℕ) : ℕ := (kids ch a).minLabel

lemma top_toBar {k : ℕ} (m : VMono G k) (ch : Fin k → STree (VMono G)) :
    top (toBar (STree.node m ch)) = m.1.plug fun a => LTree.leaf (firstOf ch a) := by
  obtain ⟨e, l, r, h⟩ := m.exists_node
  rw [toBar_node, h, top_plug_liftW, ← h]
  refine plug_congr fun a ha => ?_
  rw [kids_of_lt ch (m.lt ha), topAux_cutRoot, firstOf, kids_of_lt ch (m.lt ha), minLabel_cutRoot]

lemma firstOf_lt {k : ℕ} (ch : Fin k → STree (VMono G)) (hch : ∀ j, (ch j).IsShuffle)
    (j : Fin k) : firstOf ch j = (ch j).first := by
  rw [firstOf, kids_fin, minLabel_cutRoot, minLabel_toBar _ (hch j)]

lemma hang_toBar {k : ℕ} (m : VMono G k) {ch : Fin k → STree (VMono G)}
    (ht : (STree.node m ch).IsShuffle) (j : Fin k) :
    hang (toBar (STree.node m ch)) (ch j).first = kids ch j := by
  obtain ⟨e, l, r, h⟩ := m.exists_node
  rw [toBar_node, h, hang_plug_liftW, ← h]
  have hfj : (ch j).first = (kids ch j).minLabel := by
    rw [kids_fin, minLabel_cutRoot, minLabel_toBar _ (ht.child j)]
  rw [pick_eq (j := j) (m.mem j.2), hfj, kids_fin, minLabel_cutRoot, hangAux_cutRoot]
  · rw [kids_fin, topAux_cutRoot, minLabel_toBar _ (ht.child j)]
    simp
  · intro i hi hij
    rw [kids_of_lt ch (m.lt hi), topAux_cutRoot, minLabel_toBar _ (ht.child _),
      LTree.labels_leaf, List.mem_singleton]
    intro heq
    refine hij ?_
    have := ht.mono.injective heq
    exact (congrArg Fin.val this).symm

lemma plug_leaf_injective {X : Type*} {F : ℕ → ℕ} :
    ∀ {m m' : LTree X}, (∀ a ∈ m.labels, ∀ b ∈ m'.labels, F a = F b → a = b) →
      m.plug (fun a => LTree.leaf (F a)) = m'.plug (fun a => LTree.leaf (F a)) → m = m'
  | LTree.leaf a, LTree.leaf b, hF, h => by
    simp only [plug, LTree.leaf.injEq] at h
    rw [hF a (by simp) b (by simp) h]
  | LTree.leaf _, LTree.node _ _ _, _, h => by simp [plug] at h
  | LTree.node _ _ _, LTree.leaf _, _, h => by simp [plug] at h
  | LTree.node e l r, LTree.node e' l' r', hF, h => by
    simp only [plug, LTree.node.injEq] at h
    obtain ⟨he, hl, hr⟩ := h
    rw [he, plug_leaf_injective (fun a ha b hb => hF a (by simp [ha]) b (by simp [hb])) hl,
      plug_leaf_injective (fun a ha b hb => hF a (by simp [ha]) b (by simp [hb])) hr]

lemma labels_plug_leaf {X : Type*} (F : ℕ → ℕ) (m : LTree X) :
    (m.plug fun a => LTree.leaf (F a)).labels = m.labels.map F := by
  induction m with
  | leaf a => rfl
  | node e l r hl hr => simp only [plug, LTree.labels_node, hl, hr, List.map_append]

lemma node_ne_leaf {k : ℕ} (m : VMono G k) (ch : Fin k → STree (VMono G)) (a : ℕ) :
    toBar (STree.node m ch) ≠ LTree.leaf a := by
  obtain ⟨e, l, r, h⟩ := toBar_node_eq m ch
  rw [h]
  exact fun h' => by cases h'

/-- **Shuffle trees of monomials are determined by their bar trees.** -/
theorem toBar_injective : ∀ {t t' : STree (VMono G)}, t.IsShuffle → t'.IsShuffle →
    toBar t = toBar t' → t = t'
  | STree.leaf a, STree.leaf b, _, _, h => by
    simp only [toBar, LTree.leaf.injEq] at h
    rw [h]
  | STree.leaf _, STree.node _ _, _, _, h => absurd h.symm (node_ne_leaf _ _ _)
  | STree.node _ _, STree.leaf _, _, _, h => absurd h (node_ne_leaf _ _ _)
  | STree.node (k := k) m ch, STree.node (k := k') m' ch', ht, ht', h => by
    have htop := congrArg top h
    rw [top_toBar, top_toBar] at htop
    have hlab := congrArg LTree.labels htop
    rw [labels_plug_leaf, labels_plug_leaf] at hlab
    have hk : k = k' := by
      have := congrArg List.length hlab
      rw [List.length_map, List.length_map, m.perm.length_eq, m'.perm.length_eq,
        List.length_range, List.length_range] at this
      exact this
    subst hk
    have key : ∀ (c : Fin k → STree (VMono G)) (mm : VMono G k), (∀ j, (c j).IsShuffle) →
        ∀ x, (x ∈ Set.range fun j => (c j).first) ↔ x ∈ mm.1.labels.map (firstOf c) := by
      intro c mm hc x
      simp only [Set.mem_range, List.mem_map]
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨j, mm.mem j.2, firstOf_lt c hc j⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, mm.lt ha⟩, (firstOf_lt c hc ⟨a, mm.lt ha⟩).symm⟩
    have hf : (fun j => (ch j).first) = fun j => (ch' j).first :=
      (StrictMono.range_inj ht.mono ht'.mono).1 (Set.ext fun x => by
        rw [key ch m ht.child, key ch' m' ht'.child, hlab])
    have hF : ∀ a < k, firstOf ch a = firstOf ch' a := fun a ha => by
      have h1 := firstOf_lt ch ht.child ⟨a, ha⟩
      have h2 := firstOf_lt ch' ht'.child ⟨a, ha⟩
      exact h1.trans ((congrFun hf _).trans h2.symm)
    rw [plug_congr (m := m'.1) (ins' := fun a => LTree.leaf (firstOf ch a))
      fun a ha => by show _ = LTree.leaf (firstOf ch a); rw [hF a (m'.lt ha)]] at htop
    have hm : m = m' := Subtype.ext (plug_leaf_injective (fun a ha b hb hab => by
      have ha' := m.lt ha
      have hb' := m'.lt hb
      have h1 := firstOf_lt ch ht.child ⟨a, ha'⟩
      have h2 := firstOf_lt ch ht.child ⟨b, hb'⟩
      have h3 : (ch ⟨a, ha'⟩).first = (ch ⟨b, hb'⟩).first := h1.symm.trans (hab.trans h2)
      exact congrArg Fin.val (ht.mono.injective h3)) htop)
    subst hm
    have hch : ch = ch' := funext fun j => by
      have h1 := hang_toBar m ht j
      have h2 := hang_toBar m ht' j
      rw [h, show (ch j).first = (ch' j).first from congrFun hf j, h2, kids_fin,
        kids_fin] at h1
      exact toBar_injective (ht.child j) (ht'.child j)
        (cutRoot_injective (rootFlag_toBar _) (rootFlag_toBar _) h1).symm
    rw [hch]

/-! ### Surjectivity -/

omit [Fintype G] [DecidableEq G] in
/-- **The hanging subtrees** below the top part of a subtree: of the least label they hang at,
cut at the root unless they are leaves, and shuffle trees in a shuffle tree. -/
lemma hangAux_spec : ∀ (y : BarTree G) (a : ℕ), a ∈ (topAux y).labels →
    (hangAux y a).minLabel = a ∧ cutRoot (uncutRoot (hangAux y a)) = hangAux y a ∧
      (y.IsShuffle → (hangAux y a).IsShuffle)
  | LTree.leaf b, a, ha => by
    simp only [topAux, LTree.labels_leaf, List.mem_singleton] at ha
    subst ha
    exact ⟨rfl, rfl, fun h => h⟩
  | LTree.node d l r, a, ha => by
    by_cases hd : d.2 = true
    · simp only [topAux, hd, if_true, LTree.labels_leaf, List.mem_singleton] at ha
      subst ha
      simp only [hangAux, hd, if_true]
      refine ⟨rfl, ?_, fun h => h⟩
      obtain ⟨e, b⟩ := d
      simp only at hd
      subst hd
      rfl
    · simp only [topAux, hd, Bool.false_eq_true, if_false, LTree.labels_node,
        List.mem_append] at ha
      simp only [hangAux, hd, Bool.false_eq_true, if_false]
      split_ifs with hl
      · obtain ⟨h1, h2, h3⟩ := hangAux_spec l a hl
        exact ⟨h1, h2, fun h => h3 h.2.1⟩
      · obtain ⟨h1, h2, h3⟩ := hangAux_spec r a (ha.resolve_left hl)
        exact ⟨h1, h2, fun h => h3 h.2.2⟩

lemma unflag_plug_leaf {X : Type*} (F : ℕ → ℕ) (K : ℕ → LTree (X × Bool)) :
    ∀ l : LTree X, (unflag (l.plug fun a => LTree.leaf (F a))).plug K =
      (unflag l).plug fun a => K (F a)
  | LTree.leaf _ => rfl
  | LTree.node e l r => by
    simp only [plug, mapDec_node]
    rw [unflag_plug_leaf F K l, unflag_plug_leaf F K r]

lemma liftW_plug_leaf {X : Type*} (c : Bool) (F : ℕ → ℕ) (K : ℕ → LTree (X × Bool)) :
    ∀ T : LTree X, (liftW c (T.plug fun a => LTree.leaf (F a))).plug K =
      (liftW c T).plug fun a => K (F a)
  | LTree.leaf _ => rfl
  | LTree.node e l r => by
    simp only [plug, liftW]
    exact congrArg₂ _ (unflag_plug_leaf F K l) (unflag_plug_leaf F K r)

/-- **Every bar tree of the bar construction is the bar tree of a shuffle tree of monomials**, by
induction on its size through its top component and the subtrees hanging from it. -/
theorem exists_toBar : ∀ (N : ℕ) (y : BarTree G), y.size ≤ N → Valid y →
    ∃ t : STree (VMono G), t.IsShuffle ∧ t.labels = (y.labels : Multiset ℕ) ∧ toBar t = y
  | _, LTree.leaf a, _, _ => ⟨STree.leaf a, trivial, rfl, rfl⟩
  | 0, LTree.node _ _ _, hN, _ => by simp at hN
  | N + 1, LTree.node d l r, hN, hy => by
    set y := LTree.node d l r with hy_def
    have hnd := hy.nodup
    have hroot : rootFlag y = false := hy.root
    set T := top y with hT
    set S := T.labels.toFinset with hS
    set k := S.card with hk
    have hTnd : T.labels.Nodup := nodup_top hnd
    have hk2 : 2 ≤ k := by
      rw [hk, hS, List.toFinset_card_of_nodup hTnd, length_labels, hT, hy_def]
      simp only [top, arity]
      have := arity_pos (topAux l)
      have := arity_pos (topAux r)
      omega
    let iso := S.orderIsoOfFin hk.symm
    let g : Fin k → ℕ := fun j => (iso j : ℕ)
    let rank : ℕ → ℕ := fun a => if h : a ∈ S then (iso.symm ⟨a, h⟩ : ℕ) else 0
    have hgS : ∀ j, g j ∈ S := fun j => (iso j).2
    have hrank_lt : ∀ a, rank a < k ∨ a ∉ S := fun a => by
      by_cases h : a ∈ S
      · left
        simp only [rank, dif_pos h]
        exact (iso.symm ⟨a, h⟩).2
      · exact Or.inr h
    have hrank_g : ∀ j, rank (g j) = j := fun j => by
      simp only [rank, dif_pos (hgS j)]
      rw [show (⟨g j, hgS j⟩ : S) = iso j from rfl, OrderIso.symm_apply_apply]
    have hg_rank : ∀ a (h : a ∈ S), g ⟨rank a, by simp only [rank, dif_pos h]; exact
        (iso.symm ⟨a, h⟩).2⟩ = a := fun a h => by
      simp only [g, rank, dif_pos h]
      rw [Fin.eta, OrderIso.apply_symm_apply]
    have hgmono : StrictMono g := fun i j hij => iso.strictMono hij
    have hrank_on : StrictOn rank T := fun a ha b hb hab => by
      have ha' : a ∈ S := List.mem_toFinset.2 ha
      have hb' : b ∈ S := List.mem_toFinset.2 hb
      simp only [rank, dif_pos ha', dif_pos hb']
      exact iso.symm.strictMono (show (⟨a, ha'⟩ : S) < ⟨b, hb'⟩ from hab)
    -- the top vertex, relabelled by ranks
    set m : LTree G := T.plug fun a => LTree.leaf (rank a) with hm_def
    have hm_mem : m ∈ LTree.monomials k := by
      refine (LTree.mem_monomials k m).2 ⟨isShuffle_plug_of_strictOn _ (isShuffle_top hy.shuffle)
        hrank_on fun _ _ => trivial, ?_⟩
      rw [hm_def, labels_plug_leaf]
      refine List.perm_of_nodup_nodup_toFinset_eq
        (hTnd.map_on fun a ha b hb hab => ?_) List.nodup_range ?_
      · rcases lt_trichotomy a b with h | h | h
        · exact absurd hab (hrank_on a ha b hb h).ne
        · exact h
        · exact absurd hab.symm (hrank_on b hb a ha h).ne
      · rw [List.toFinset_range]
        ext x
        simp only [List.mem_toFinset, List.mem_map, Finset.mem_range]
        constructor
        · rintro ⟨a, ha, rfl⟩
          exact (hrank_lt a).resolve_right (by simpa [hS] using ha)
        · intro hx
          exact ⟨g ⟨x, hx⟩, List.mem_toFinset.1 (hgS _), hrank_g ⟨x, hx⟩⟩
    let mm : VMono G k := ⟨m, hm_mem, hk2⟩
    -- the hanging subtrees
    have hhang : hang y = hangAux y := (hangAux_eq_hang hroot).symm
    have htop : T = topAux y := (topAux_eq_top hroot).symm
    have hspec : ∀ a ∈ S, (hang y a).minLabel = a ∧ cutRoot (uncutRoot (hang y a)) = hang y a ∧
        (hang y a).IsShuffle := fun a ha => by
      rw [hhang]
      obtain ⟨h1, h2, h3⟩ := hangAux_spec y a (by rw [← htop]; exact List.mem_toFinset.1 ha)
      exact ⟨h1, h2, h3 hy.shuffle⟩
    have hplug := plug_top y hnd
    rw [hroot] at hplug
    have hlabels : y.labels = T.labels.flatMap fun a => (hang y a).labels := by
      conv_lhs => rw [← hplug]
      rw [labels_plug, labels_liftW]
    have hnd_hang : ∀ a ∈ T.labels, (hang y a).labels.Nodup := fun a ha => by
      rw [hlabels] at hnd
      exact (List.nodup_flatMap.1 hnd).1 a ha
    let z : Fin k → BarTree G := fun j => uncutRoot (hang y (g j))
    have hz : ∀ j, Valid (z j) := fun j =>
      ⟨(isShuffle_uncutRoot _).2 (hspec _ (hgS j)).2.2,
        by rw [labels_uncutRoot]; exact hnd_hang _ (List.mem_toFinset.1 (hgS j)),
        rootFlag_uncutRoot _⟩
    have hzsize : ∀ j, (z j).size ≤ N := fun j => by
      have := size_hang_lt d l r (g j)
      simp only [z, size_uncutRoot]
      rw [← hy_def] at this
      omega
    choose s hs using fun j => exists_toBar N (z j) (hzsize j) (hz j)
    refine ⟨STree.node mm s, ⟨by omega, fun j => (hs j).1, fun i j hij => ?_⟩, ?_, ?_⟩
    · show (s i).first < (s j).first
      rw [← minLabel_toBar _ (hs i).1, ← minLabel_toBar _ (hs j).1, (hs i).2.2, (hs j).2.2]
      simp only [z, minLabel_uncutRoot]
      rw [(hspec _ (hgS i)).1, (hspec _ (hgS j)).1]
      exact hgmono hij
    · rw [STree.labels, hlabels, ← Multiset.coe_bind]
      have hval : ((T.labels : List ℕ) : Multiset ℕ) = S.val := by
        rw [hS, List.toFinset_val, List.dedup_eq_self.2 hTnd]
      rw [hval]
      have : ∀ j, (s j).labels = (((hang y (g j)).labels : List ℕ) : Multiset ℕ) := fun j => by
        rw [(hs j).2.1]
        simp [z]
      simp only [this]
      rw [← S.map_orderEmbOfFin_univ hk.symm, Finset.map_val, Multiset.bind_map]
      show _ = (Multiset.map (fun a => (((hang y ((S.orderEmbOfFin hk.symm).toEmbedding a)).labels
        : List ℕ) : Multiset ℕ)) Finset.univ.val).sum
      rw [← Finset.sum_eq_multiset_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [g, iso, RelEmbedding.coe_toEmbedding, Finset.coe_orderIsoOfFin_apply]
    · rw [toBar_node]
      show (liftW false (T.plug fun a => LTree.leaf (rank a))).plug (kids s) = y
      rw [liftW_plug_leaf]
      conv_rhs => rw [← hplug]
      refine plug_congr fun a ha => ?_
      rw [labels_liftW] at ha
      have haS : a ∈ S := List.mem_toFinset.2 ha
      have hra : rank a < k := (hrank_lt a).resolve_right (not_not.2 haS)
      rw [kids_of_lt s hra, (hs _).2.2]
      simp only [z]
      rw [hg_rank a haS]
      exact (hspec a haS).2.1

end Trees

/-! ## The bijection with the bar trees -/

section Equiv

open ShuffleBar STree

variable {G : Type} [Fintype G] [DecidableEq G]

variable (G) in
/-- **The bar trees of the bar construction in arity `n`**: valid bar trees on `0, …, n - 1`. -/
def barSet (n : ℕ) : Set (BarTree G) := {x | Valid x ∧ x.labels.Perm (List.range n)}

lemma valid_toBar {Y : Finset ℕ} (t : SMono (VMono G) Y) : Valid (toBar t.1) :=
  ⟨isShuffle_toBar _ t.2.1, nodup_toBar (by rw [t.2.2]; exact Y.nodup), rootFlag_toBar _⟩

lemma labels_toBar_range {n : ℕ} (t : SMono (VMono G) (Finset.range n)) :
    (toBar t.1).labels.Perm (List.range n) := by
  rw [← Multiset.coe_eq_coe, labels_toBar, t.2.2, Finset.range_val, Multiset.coe_range]

/-- **The shuffle trees of monomials on `0, …, n - 1` are the bar trees of the bar construction**
in arity `n`, by `toBar`. -/
noncomputable def treeEquiv (n : ℕ) : SMono (VMono G) (Finset.range n) ≃ barSet G n :=
  Equiv.ofBijective (fun t => ⟨toBar t.1, valid_toBar t, labels_toBar_range t⟩)
    ⟨fun t t' h => Subtype.ext (toBar_injective t.2.1 t'.2.1 (congrArg Subtype.val h)),
      fun x => by
        obtain ⟨t, ht, hl, hb⟩ := exists_toBar x.1.size x.1 le_rfl x.2.1
        refine ⟨⟨t, ht, ?_⟩, Subtype.ext hb⟩
        rw [hl, Finset.range_val, ← Multiset.coe_range, Multiset.coe_eq_coe]
        exact x.2.2⟩

@[simp] lemma treeEquiv_apply {n : ℕ} (t : SMono (VMono G) (Finset.range n)) :
    (treeEquiv n t : BarTree G) = toBar t.1 := rfl

lemma exists_node_of_two_le {n : ℕ} (hn : 2 ≤ n) (t : SMono (VMono G) (Finset.range n)) :
    ∃ (k : ℕ) (m : VMono G k) (ch : Fin k → STree (VMono G)), t.1 = STree.node m ch := by
  rcases h : t.1 with a | ⟨m, ch⟩
  · have h1 := congrArg Multiset.card t.2.2
    rw [h, STree.labels_leaf, Multiset.card_singleton, Finset.range_val, Multiset.card_range] at h1
    omega
  · exact ⟨_, m, ch, rfl⟩

/-- **Degrees.** In arity `n ≥ 2`, the bar tree of a shuffle tree with `s` vertices has `s`
components: it is a basis vector of `ShuffleBar.C K n s`. -/
theorem adm_treeEquiv {n : ℕ} (hn : 2 ≤ n) (t : SMono (VMono G) (Finset.range n)) :
    Adm n t.1.weight (treeEquiv n t : BarTree G) := by
  refine ⟨valid_toBar t, labels_toBar_range t, ?_⟩
  obtain ⟨k, m, ch, h⟩ := exists_node_of_two_le hn t
  rw [treeEquiv_apply, h, card_cutKeys_toBar m ch (by rw [← h, t.2.2]; exact Finset.nodup _)]

omit [Fintype G] [DecidableEq G] in
lemma mem_barSet_of_adm {n s : ℕ} {x : BarTree G} (h : Adm n s x) : x ∈ barSet G n :=
  ⟨h.1, h.2.1⟩

/-- **The number of components of a bar tree in arity `n ≥ 2`** is the number of vertices of its
shuffle tree. -/
theorem adm_iff {n s : ℕ} (hn : 2 ≤ n) (t : SMono (VMono G) (Finset.range n)) :
    Adm n s (treeEquiv n t : BarTree G) ↔ t.1.weight = s := by
  constructor
  · intro h
    have h' := adm_treeEquiv hn t
    exact h'.2.2.symm.trans h.2.2
  · rintro rfl
    exact adm_treeEquiv hn t

/-! ## The sign of a shuffle tree -/

/-- The key of the vertex at the root of a subtree: its least leaf and its number of leaves, as
`ShuffleBar`'s key of the vertex below a cut edge. -/
def vkey {B : ℕ → Type*} (t : STree B) : ℕ ×ₗ ℕ := toLex (t.first, Multiset.card t.labels)

/-- **The keys of the vertices in preorder**: the root, then the children from left to right. -/
def preKeys {B : ℕ → Type*} : STree B → List (ℕ ×ₗ ℕ)
  | STree.leaf _ => []
  | t@(STree.node _ ch) => vkey t :: (List.ofFn fun j => preKeys (ch j)).flatten

/-- **The number of inversions** of a list. -/
def inv {α : Type*} [LinearOrder α] : List α → ℕ
  | [] => 0
  | a :: l => (l.filter (· < a)).length + inv l

/-- Equal sets of leaves, for shuffle monomials. -/
def smonoCast {B : ℕ → Type*} {Y Y' : Finset ℕ} (h : Y = Y') : SMono B Y ≃ SMono B Y' where
  toFun t := t.cast h
  invFun t := t.cast h.symm
  left_inv _ := rfl
  right_inv _ := rfl

variable (K : Type u) [CommRing K]

/-- **The sign of a shuffle tree of monomials**: the sign of the permutation from the preorder of
its vertices other than the root, the order of composition in `FreeGrL`, to the order of their keys,
the order of `ShuffleBar.sgn`. -/
def sign {B : ℕ → Type*} (t : STree B) : K := (-1) ^ inv (preKeys t).tail

lemma isUnit_sign {B : ℕ → Type*} (t : STree B) : IsUnit (sign K t) :=
  (isUnit_neg_one (α := K)).pow _

lemma sign_mul_self {B : ℕ → Type*} (t : STree B) : sign K t * sign K t = 1 := by
  rw [sign, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

end Equiv

/-! ## The comparison `Φ` -/

section Phi

open ShuffleBar STree

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {G : Type} [Fintype G] [DecidableEq G]
  (c : ∀ k, Module.Basis (BinGen G k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen G k), GrSpecies.par (R := K) false (c k β) = c k β)

/-- The shuffle basis of the bar construction in arity `n`, on the leaves `0, …, n - 1`. -/
noncomputable def barBasisN (n : ℕ) :
    Module.Basis (SMono (VMono G) (Finset.range n)) K (BarCoop (Ibar K E c hc) (Fin n)) :=
  (barBasis c hc (Fin n)).reindex (smonoCast (by rw [Fintype.card_fin]))

lemma barBasisN_apply (n : ℕ) (t : SMono (VMono G) (Finset.range n)) :
    barBasisN c hc n t = barBasis c hc (Fin n) (t.cast (by rw [Fintype.card_fin])) := by
  rw [barBasisN, Module.Basis.reindex_apply]
  rfl

/-- The shuffle basis twisted by the signs. -/
noncomputable def signedBasis (n : ℕ) :
    Module.Basis (SMono (VMono G) (Finset.range n)) K (BarCoop (Ibar K E c hc) (Fin n)) :=
  (barBasisN c hc n).isUnitSMul fun t => isUnit_sign K t.1

/-- **The comparison of the bar constructions**: `B(T, Ī)(Fin n)`, `T` the free graded operad on
the even binary generators `c`, is the span of the bar trees of arity `n` in the bar construction
of the free shuffle operad on `G`, a shuffle basis vector `t` going to `sign t` times its bar tree
(`Φ_barBasisN`). -/
noncomputable def Φ (n : ℕ) :
    BarCoop (Ibar K E c hc) (Fin n) ≃ₗ[K] Finsupp.supported K K (barSet G n) :=
  (signedBasis c hc n).repr ≪≫ₗ Finsupp.domLCongr (treeEquiv n) ≪≫ₗ
    (Finsupp.supportedEquivFinsupp (barSet G n)).symm

/-- `Φ` as a linear map into the combinations of bar trees. -/
noncomputable def ΦL (n : ℕ) : BarCoop (Ibar K E c hc) (Fin n) →ₗ[K] (BarTree G →₀ K) :=
  (Finsupp.supported K K (barSet G n)).subtype ∘ₗ (Φ c hc n).toLinearMap

lemma ΦL_injective (n : ℕ) : Function.Injective (ΦL c hc n) :=
  (Submodule.subtype_injective _).comp (Φ c hc n).injective

lemma ΦL_range (n : ℕ) : LinearMap.range (ΦL c hc n) = Finsupp.supported K K (barSet G n) := by
  rw [ΦL, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]

lemma ΦL_signedBasis (n : ℕ) (t : SMono (VMono G) (Finset.range n)) :
    ΦL c hc n (signedBasis c hc n t) = Finsupp.single (toBar t.1) 1 := by
  classical
  simp only [ΦL, Φ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply, Module.Basis.repr_self, Finsupp.domLCongr_single,
    Submodule.coe_subtype]
  rw [Finsupp.supportedEquivFinsupp_symm_apply_coe, Finsupp.extendDomain_single]
  rfl

/-- **`Φ` on the shuffle basis**: a basis vector goes to its bar tree, with the sign of the tree. -/
theorem Φ_barBasisN (n : ℕ) (t : SMono (VMono G) (Finset.range n)) :
    ΦL c hc n (barBasisN c hc n t) = sign K t.1 • Finsupp.single (toBar t.1) 1 := by
  have : barBasisN c hc n t = sign K t.1 • signedBasis c hc n t := by
    rw [signedBasis, Module.Basis.isUnitSMul_apply, smul_smul, sign_mul_self, one_smul]
  rw [this, map_smul, ΦL_signedBasis]

/-- **The vertex grading of the bar construction**: in arity `n`, the span of the shuffle basis
vectors whose trees have `s` vertices. -/
noncomputable def deg (n s : ℕ) : Submodule K (BarCoop (Ibar K E c hc) (Fin n)) :=
  Submodule.span K (barBasisN c hc n '' {t | t.1.weight = s})

/-- **`Φ` respects the degrees**: in arity `n ≥ 2` it sends the trees with `s` vertices onto the
bar trees with `s` components, `ShuffleBar.C K n s`. -/
theorem map_ΦL_deg {n : ℕ} (hn : 2 ≤ n) (s : ℕ) :
    Submodule.map (ΦL c hc n) (deg c hc n s) = ShuffleBar.C (E := G) K n s := by
  rw [deg, Submodule.map_span, ShuffleBar.C, Finsupp.supported_eq_span_single]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Φ_barBasisN c hc n t]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨toBar t.1, ?_, rfl⟩)
    exact (adm_iff hn t).2 ht
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht⟩ := (treeEquiv n).surjective ⟨x, mem_barSet_of_adm hx⟩
    have hx' : toBar t.1 = x := congrArg Subtype.val ht
    have hw : t.1.weight = s := (adm_iff hn t).1 (by rw [treeEquiv_apply, hx']; exact hx)
    have hmem : ΦL c hc n (barBasisN c hc n t) ∈
        Submodule.span K (ΦL c hc n '' (barBasisN c hc n ''
          {t : SMono (VMono G) (Finset.range n) | t.1.weight = s})) :=
      Submodule.subset_span ⟨_, ⟨t, hw, rfl⟩, rfl⟩
    rw [Φ_barBasisN c hc n t, hx'] at hmem
    have := Submodule.smul_mem _ (sign K t.1) hmem
    rwa [smul_smul, sign_mul_self, one_smul] at this

/-- **The degrees exhaust the bar construction.** -/
theorem iSup_deg (n : ℕ) : ⨆ s, deg c hc n s = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← (barBasisN c hc n).span_eq, Submodule.span_le]
  rintro _ ⟨t, rfl⟩
  exact Submodule.mem_iSup_of_mem t.1.weight (Submodule.subset_span ⟨t, rfl, rfl⟩)

/-- **A basis vector of a tree with `s` vertices has `s` vertices**: it lies in the eigenspace
`FreeGrL.vx s` of the vertex count. -/
theorem barBasisN_mem_vx (n : ℕ) (t : SMono (VMono G) (Finset.range n)) :
    barBasisN c hc n t ∈ FreeGrL.vx K (BarGen (Ibar K E c hc)) t.1.weight (Fin n) := by
  rw [barBasisN_apply, barBasis]
  erw [FreeGrL.shuffleBasis_apply (genBasis c hc) (par_genBasis c hc)]
  exact FreeGrL.map_mem_eig _ (FreeGrL.shEv_mem_vx (genBasis c hc) (par_genBasis c hc) _ t.1
    le_rfl t.2.1 _ _)

lemma deg_le_vx (n s : ℕ) : deg c hc n s ≤ FreeGrL.vx K (BarGen (Ibar K E c hc)) s (Fin n) := by
  rw [deg, Submodule.span_le]
  rintro _ ⟨t, ht, rfl⟩
  have := barBasisN_mem_vx c hc n t
  rw [ht] at this
  exact this

variable [CharZero K]

/-- **The vertex grading is the vertex count**: `deg n s` is the eigenspace `FreeGrL.vx s`, over
a field of characteristic zero. -/
theorem deg_eq_vx (n s : ℕ) : deg c hc n s = FreeGrL.vx K (BarGen (Ibar K E c hc)) s (Fin n) := by
  refine le_antisymm (deg_le_vx c hc n s) fun x hx => ?_
  have hx' : x ∈ deg c hc n s ⊔ ⨆ i, ⨆ (_ : i ≠ s), deg c hc n i := by
    rw [← iSup_split_single (fun i => deg c hc n i) s, iSup_deg]
    exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
  have hzv : z ∈ FreeGrL.vx K (BarGen (Ibar K E c hc)) s (Fin n) := by
    have := Submodule.sub_mem _ hx (deg_le_vx c hc n s hy)
    rwa [add_sub_cancel_left] at this
  have hzo : z ∈ ⨆ i, ⨆ (_ : i ≠ s), FreeGrL.vx K (BarGen (Ibar K E c hc)) i (Fin n) :=
    (iSup₂_mono fun i _ => deg_le_vx c hc n i) hz
  have hind := iSupIndep_def.1 (iSupIndep_eigenspace_nat
    ((FreeGrL.derSp (GrSpEnd.id K (BarGen (Ibar K E c hc)))).app (Fin n))) s
  have hz0 : z = 0 := Submodule.disjoint_def.1 hind z hzv hzo
  rw [hz0, add_zero]
  exact hy

/-- **The bar differential lowers the degree by one.** -/
theorem d_mem_deg {n s : ℕ} {x : BarCoop (Ibar K E c hc) (Fin n)} (hx : x ∈ deg c hc n (s + 1)) :
    Bar.d (Ibar K E c hc) (Fin n) x ∈ deg c hc n s := by
  rw [deg_eq_vx] at hx ⊢
  exact Bar.d_vx_succ hx

/-- **Both differentials lower the degree by one through `Φ`**: in arity `n ≥ 2`, on the trees
with `s + 1` vertices, `ΦL ∘ Bar.d` and `ShuffleBar.d ∘ ΦL` both take values in
`ShuffleBar.C K n s`. -/
theorem ΦL_d_mem_C {n s : ℕ} (hn : 2 ≤ n) {x : BarCoop (Ibar K E c hc) (Fin n)}
    (hx : x ∈ deg c hc n (s + 1)) :
    ΦL c hc n (Bar.d (Ibar K E c hc) (Fin n) x) ∈ ShuffleBar.C (E := G) K n s ∧
      ShuffleBar.d K (ΦL c hc n x) ∈ ShuffleBar.C (E := G) K n s := by
  refine ⟨?_, ShuffleBar.d_mem_C K ?_⟩
  · rw [← map_ΦL_deg c hc hn s]
    exact Submodule.mem_map_of_mem (d_mem_deg c hc hx)
  · rw [← map_ΦL_deg c hc hn (s + 1)]
    exact Submodule.mem_map_of_mem hx

end Phi

end ShuffleBarSym

end Operad
