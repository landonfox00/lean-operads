/-
# The expansion of the bar differential over the edges

Step (2b) of the bridge between symmetric and shuffle operads (Dotsenko–Khoroshkin), completed:
`T = FreeGrL K E` for `E` even with the basis `c` indexed by `BinGen G`, and `Ī` its ideal of
operations with at least two inputs. **The bar differential of the basis vector of every shuffle
tree of monomials expands over its edges** with the signs of `ShuffleBarSymSign.lean`
(`ShuffleBarSym.dExpansion`), so **`ΦL ∘ Bar.d = ShuffleBar.d ∘ ΦL` on all of
`B(T, Ī)(Fin n)`** (`ShuffleBarSym.ΦL_d`).

* **Composing and merge-composing at a leaf, the inputs named by their values** (`compL`, `mcL`),
  for a split `LabSplit Y Y₁ Y₂ m` of the leaves (`LabSplit.of_val`,
  `FreeGrL.labSplit_of_equiv`): composing evaluations of trees substitutes one tree for a leaf of
  the other with the Koszul sign `σ(|t'| · aft_t(m))` (`compL_shEv`); the Leibniz rule
  (`d_compL`); merging at a leaf other than the one composed at (`mcL_compL_par`); composing into
  the inner factor of a merge-composite (`mcL_compL_outer`).
* **Merging two basis generators** (`ShuffleBarSym.msVal_genBasis`): `s m₁ ⊛_q s m₂` is the basis
  generator of the merged monomial `mergedMono m₁ q m₂ π`, its inputs relabelled by `π`, without
  sign since `T` is even.
* **Koszul signs** (`ShuffleBarSym.kz_mul_after`, `ShuffleBarSym.kz_mul_σ_vaft`): with one child
  of a vertex cut off at its least leaf, the Koszul sign of sorting the children times the parity
  of the children sorted after that leaf is the Koszul sign without that child times the signs of
  that child with the children after it in planar order.
* **Merging the root of a child into the vertex** (`ShuffleBarSym.rmProp`): when the children after
  the child `j` are leaves, merge-composing the evaluation of the tree cut at `j` with that of the
  child is the evaluation of `rootMerge` with the sign `ShuffleBarSym.rmCoeff`, `(-1)` to the number
  of the other vertices below the vertex times `kzRoot`. By induction on the vertices: the last
  other child of the vertex that is not a leaf moves out by `mcL_compL_par`
  (`ShuffleBarSym.rm_stepA`), then the last child of the child that is not a leaf by
  `mcL_compL_outer` (`ShuffleBarSym.rm_stepB`), down to two relabelled generators
  (`ShuffleBarSym.rm_base`); each child goes back into the merged vertex by `compL_shEv`, whose sign
  `kz_mul_σ_vaft` turns into the Koszul sign of sorting.
* **The expansion** (`ShuffleBarSym.dProp_all`, by `ShuffleBarSym.dProp_step`): the evaluation of a
  tree is the composite of the tree cut at its last child that is not a leaf with that child, so
  its bar differential is the sum over the edges of the cut tree (`ShuffleBarSym.mergeT_cut_subst`,
  `ShuffleBarSym.kzAt_cut`), the edge above the child (`rmProp`) and the edges of the child, in the
  preorder of the keys (`ShuffleBarSym.tail_preKeys_cut`).

The Koszul sign of sorting the children of a merged vertex comes out of the composition signs; the
reordering relation of the graded composite (`GrComposite.mk_reorder`) is not used.
-/
import Operad.ShuffleBarSymSign

universe u v w

namespace Operad

open Function Sym GerBV GrComposite STree

/-! ## Composing operations whose inputs are named by natural numbers -/

/-- **The leaves of a composite at the leaf `m`**: `Y` is `Y₁` without `m`, together with `Y₂`,
the two sets meeting at most in `m`. -/
structure LabSplit (Y Y₁ Y₂ : Finset ℕ) (m : ℕ) : Prop where
  /-- The leaf composed at is a leaf of the outer operation. -/
  mem : m ∈ Y₁
  /-- The leaves of the composite. -/
  iff : ∀ x, x ∈ Y ↔ (x ∈ Y₁ ∧ x ≠ m) ∨ x ∈ Y₂
  /-- The other leaves of the outer operation are not leaves of the inner one. -/
  disj : ∀ x ∈ Y₁, x ≠ m → x ∉ Y₂

namespace LabSplit

variable {Y Y₁ Y₂ : Finset ℕ} {m : ℕ}

/-- A split from the multisets of leaves. -/
lemma of_val (hm : m ∈ Y₁) (h : Y.val + {m} = Y₁.val + Y₂.val) : LabSplit Y Y₁ Y₂ m := by
  have hc : ∀ x, Multiset.count x Y.val + (if x = m then 1 else 0)
      = Multiset.count x Y₁.val + Multiset.count x Y₂.val := fun x => by
    have := congrArg (Multiset.count x) h
    rw [Multiset.count_add, Multiset.count_add, Multiset.count_singleton] at this
    exact this
  have hle : ∀ (Z : Finset ℕ) x, Multiset.count x Z.val ≤ 1 := fun Z x =>
    Multiset.nodup_iff_count_le_one.1 Z.nodup x
  have hcnt : ∀ (Z : Finset ℕ) x, x ∈ Z ↔ 0 < Multiset.count x Z.val := fun Z x => by
    rw [Multiset.count_pos, Finset.mem_val]
  have hm' := (hcnt Y₁ m).1 hm
  refine ⟨hm, fun x => ?_, fun x hx hxm hx₂ => ?_⟩
  · have h1 := hc x
    have := hle Y x
    have := hle Y₁ x
    have := hle Y₂ x
    rw [hcnt, hcnt, hcnt]
    by_cases hxm : x = m
    · subst hxm
      rw [if_pos rfl] at h1
      omega
    · rw [if_neg hxm] at h1
      omega
  · have h1 := hc x
    rw [if_neg hxm] at h1
    have := hle Y x
    have := (hcnt _ _).1 hx
    have := (hcnt _ _).1 hx₂
    omega

end LabSplit

namespace FreeGrL

/-- The inverse of `labSplit` names an input of a composite by its value. -/
@[simp] lemma labSplit_symm_val {Y Y₁ Y₂ : Finset ℕ} {m : ℕ} (hm : m ∈ Y₁)
    (hY : ∀ x, x ∈ Y ↔ (x ∈ Y₁ ∧ x ≠ m) ∨ x ∈ Y₂) (hd : ∀ x ∈ Y₁, x ≠ m → x ∉ Y₂)
    (u : Without (Lab Y₁) ⟨m, hm⟩ ⊕ Lab Y₂) : ((labSplit hm hY hd).symm u).1 = sval u := by
  rcases u with a | c <;> rfl

/-- **The inputs of a composite named by their values** are named by `labSplit`. -/
lemma eq_labSplit {Y Y₁ Y₂ : Finset ℕ} {m : ℕ} (hm : m ∈ Y₁)
    (hY : ∀ x, x ∈ Y ↔ (x ∈ Y₁ ∧ x ≠ m) ∨ x ∈ Y₂) (hd : ∀ x ∈ Y₁, x ≠ m → x ∉ Y₂)
    (E : Lab Y ≃ Without (Lab Y₁) ⟨m, hm⟩ ⊕ Lab Y₂) (hE : ∀ x, sval (E x) = x.1) :
    E = labSplit hm hY hd :=
  Equiv.ext fun x => sval_injective E hE (by rw [hE, sval_labSplit])

/-- **A bijection naming the inputs of a composite by their values** splits the leaves. -/
lemma labSplit_of_equiv {Y Y₁ Y₂ : Finset ℕ} {m : ℕ} (hm : m ∈ Y₁)
    (E : Lab Y ≃ Without (Lab Y₁) ⟨m, hm⟩ ⊕ Lab Y₂) (hE : ∀ x, sval (E x) = x.1) :
    LabSplit Y Y₁ Y₂ m := by
  have hinj := sval_injective E hE
  refine ⟨hm, fun x => ⟨fun hx => ?_, fun hx => ?_⟩, fun x hx hxm hx₂ => ?_⟩
  · have := hE ⟨x, hx⟩
    rcases h : E ⟨x, hx⟩ with a | c
    · rw [h, sval_inl] at this
      have hax : a.1.1 = x := this
      exact Or.inl ⟨hax ▸ a.1.2, fun e => a.2 (Subtype.ext (hax.trans e))⟩
    · rw [h, sval_inr] at this
      have hcx : c.1 = x := this
      exact Or.inr (hcx ▸ c.2)
  · rcases hx with ⟨hx, hxm⟩ | hx
    · have := hE (E.symm (Sum.inl ⟨⟨x, hx⟩, fun e => hxm (congrArg Subtype.val e)⟩))
      rw [Equiv.apply_symm_apply, sval_inl] at this
      have hx' : x = (E.symm (Sum.inl ⟨⟨x, hx⟩, fun e => hxm (congrArg Subtype.val e)⟩)).1 := this
      exact hx' ▸ (E.symm _).2
    · have := hE (E.symm (Sum.inr ⟨x, hx⟩))
      rw [Equiv.apply_symm_apply, sval_inr] at this
      have hx' : x = (E.symm (Sum.inr ⟨x, hx⟩)).1 := this
      exact hx' ▸ (E.symm _).2
  · have e := hinj (a₁ := Sum.inl ⟨⟨x, hx⟩, fun e => hxm (congrArg Subtype.val e)⟩)
      (a₂ := Sum.inr ⟨x, hx₂⟩) rfl
    exact Sum.inl_ne_inr e

end FreeGrL

section LabComp

variable (R : Type u) [CommRing R] {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
  {Y Y₁ Y₂ : Finset ℕ} {m : ℕ}

/-- **Composing at the leaf `m`**, the inputs of the composite named by their values. -/
noncomputable def compL (s : LabSplit Y Y₁ Y₂ m) : Q (Lab Y₁) →ₗ[R] Q (Lab Y₂) →ₗ[R] Q (Lab Y) :=
  (GrOperad.comp (R := R) (⟨m, s.mem⟩ : Lab Y₁)).compr₂
    (GrOperad.map (R := R) (FreeGrL.labSplit s.mem s.iff s.disj).symm)

lemma compL_apply (s : LabSplit Y Y₁ Y₂ m) (X : Q (Lab Y₁)) (Z : Q (Lab Y₂)) :
    compL R s X Z = GrOperad.map (R := R) (FreeGrL.labSplit s.mem s.iff s.disj).symm
      (GrOperad.comp (R := R) (⟨m, s.mem⟩ : Lab Y₁) X Z) := rfl

/-- **A composite named by values** through any bijection naming the inputs by their values. -/
lemma comp_eq_map_compL (s : LabSplit Y Y₁ Y₂ m)
    (E : Lab Y ≃ Without (Lab Y₁) ⟨m, s.mem⟩ ⊕ Lab Y₂) (hE : ∀ x, FreeGrL.sval (E x) = x.1)
    (X : Q (Lab Y₁)) (Z : Q (Lab Y₂)) :
    GrOperad.comp (R := R) (⟨m, s.mem⟩ : Lab Y₁) X Z = GrOperad.map (R := R) E (compL R s X Z) := by
  rw [compL_apply, FreeGrL.eq_labSplit s.mem s.iff s.disj E hE, ← GrOperad.map_trans,
    Equiv.symm_trans_self, GrOperad.map_refl]

end LabComp

section LabShEv

variable {R : Type u} [CommRing R]
  {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)] [GrSpecies R W]
  {B : ℕ → Type w} (b : ∀ k, Module.Basis (B k) R (W (Fin k))) {p : ∀ k, B k → Bool}
  (hb : ∀ k (β : B k), GrSpecies.par (R := R) (p k β) (b k β) = b k β)
include hb

/-- **Composing evaluations of trees at a leaf**, the inputs named by their values: substituting
`t'` for the leaf `m` of `t`, with the Koszul sign `σ(|t'| · aft_t(m))`. -/
theorem compL_shEv {Y Y₁ Y₂ : Finset ℕ} {m : ℕ} (s : LabSplit Y Y₁ Y₂ m) (t t' : STree B)
    (h₁ : t.labels = Y₁.val) (h₂ : t'.labels = Y₂.val)
    (h : (t.subst (update STree.leaf m t')).labels = Y.val) :
    compL R s (FreeGrL.shEv b t Y₁ h₁) (FreeGrL.shEv b t' Y₂ h₂)
      = σ R (vpar p t' && vaft p t m) • FreeGrL.shEv b (t.subst (update STree.leaf m t')) Y h := by
  rw [compL_apply, FreeGrL.comp_shEv b hb t' Y₂ h₂ t Y₁ h₁ m s.mem Y h _
    (FreeGrL.sval_labSplit s.mem s.iff s.disj), map_smul, ← GrOperad.map_trans,
    Equiv.self_trans_symm, GrOperad.map_refl]

end LabShEv

/-! ## Merge-composing operations whose inputs are named by natural numbers -/

namespace MergeSp

variable {R : Type u} [CommRing R] {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)] [GrSpecies R W]
  (M : MergeSp R W) {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **Merge-composition commutes with relabelling the outer operation**, at a slot given up to
equality. -/
lemma mc_map_left_of {A' : Type} [Fintype A'] [DecidableEq A'] (e : A ≃ A') (i : A) (j : A')
    (h : e i = j) (X : FreeGrL R W A) (Y : FreeGrL R W B) :
    M.mc j (GrOperad.map (R := R) e X) Y
      = GrOperad.map (R := R) ((compEquiv e (Equiv.refl B) i).trans (slotEquiv h))
          (M.mc i X Y) := by
  subst h
  rw [M.mc_map_left]
  refine gmap_congr (fun x => ?_) _
  rcases x with a | c <;> rfl

end MergeSp

section LabMerge

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {I : GrOperadIdeal R P}

local notation "𝒞" => FreeGrL R (BarGen I)

/-- **Merge-composing at the leaf `m`** in the bar construction, the inputs of the result named by
their values. -/
noncomputable def mcL {Y Y₁ Y₂ : Finset ℕ} {m : ℕ} (s : LabSplit Y Y₁ Y₂ m) :
    𝒞 (Lab Y₁) →ₗ[R] 𝒞 (Lab Y₂) →ₗ[R] 𝒞 (Lab Y) :=
  ((Bar.mergeSp I).mc (⟨m, s.mem⟩ : Lab Y₁)).compr₂
    (GrOperad.map (R := R) (FreeGrL.labSplit s.mem s.iff s.disj).symm)

lemma mcL_apply {Y Y₁ Y₂ : Finset ℕ} {m : ℕ} (s : LabSplit Y Y₁ Y₂ m) (X : 𝒞 (Lab Y₁))
    (Z : 𝒞 (Lab Y₂)) :
    mcL s X Z = GrOperad.map (R := R) (FreeGrL.labSplit s.mem s.iff s.disj).symm
      ((Bar.mergeSp I).mc (⟨m, s.mem⟩ : Lab Y₁) X Z) := rfl

/-- **The Leibniz rule of the bar differential**, the inputs named by their values:
`d (x ∘ₘ y) = d x ∘ₘ y + (-1)^|x| x ∘ₘ d y + x ⊛ₘ y`. -/
theorem d_compL {Y Y₁ Y₂ : Finset ℕ} {m : ℕ} (s : LabSplit Y Y₁ Y₂ m) (X : 𝒞 (Lab Y₁))
    (Z : 𝒞 (Lab Y₂)) :
    Bar.d I (Lab Y) (compL R s X Z) = compL R s (Bar.d I _ X) Z
      + compL R s (GrOperad.tw (R := R) true X) (Bar.d I _ Z) + mcL s X Z := by
  rw [compL_apply, Bar.d_map, Bar.d_comp, map_add, map_add]
  rfl

/-- **Merging at a leaf other than the one composed at**, the inputs named by their values:
`(x ∘ₘ' w) ⊛ₘ z = (-1)^{|w||z|} (x ⊛ₘ z) ∘ₘ' w`. -/
theorem mcL_compL_par {Y Y₁ Y₂ Y₃ Y₁₂ Y₁₃ : Finset ℕ} {m m' : ℕ} (hmm : m ≠ m')
    (s₁ : LabSplit Y₁₃ Y₁ Y₃ m') (s₂ : LabSplit Y Y₁₃ Y₂ m) (s₃ : LabSplit Y₁₂ Y₁ Y₂ m)
    (s₄ : LabSplit Y Y₁₂ Y₃ m') (X : 𝒞 (Lab Y₁)) {q r : Bool} {W : 𝒞 (Lab Y₃)} {Z : 𝒞 (Lab Y₂)}
    (hW : GrOperad.par (R := R) q W = W) (hZ : GrOperad.par (R := R) r Z = Z) :
    mcL s₂ (compL R s₁ X W) Z = σ R (q && r) • compL R s₄ (mcL s₃ X Z) W := by
  have hik : (⟨m', s₁.mem⟩ : Lab Y₁) ≠ ⟨m, s₃.mem⟩ := fun e => hmm (congrArg Subtype.val e).symm
  have e1 : (FreeGrL.labSplit s₁.mem s₁.iff s₁.disj).symm (Sum.inl ⟨⟨m, s₃.mem⟩, Ne.symm hik⟩)
      = (⟨m, s₂.mem⟩ : Lab Y₁₃) := Subtype.ext (by simp)
  have e2 : (FreeGrL.labSplit s₃.mem s₃.iff s₃.disj).symm (Sum.inl ⟨⟨m', s₁.mem⟩, hik⟩)
      = (⟨m', s₄.mem⟩ : Lab Y₁₂) := Subtype.ext (by simp)
  have hp := (Bar.mergeSp I).mc_comp_par hik X hW hZ
  have hp' := congrArg (GrOperad.map (R := R) (parEquiv hik (Lab Y₃) (Lab Y₂)).symm) hp
  rw [← GrOperad.map_trans, Equiv.self_trans_symm, GrOperad.map_refl] at hp'
  rw [mcL_apply, compL_apply, MergeSp.mc_map_left_of _ _ _ _ e1, hp', compL_apply, mcL_apply,
    GrOperad.comp_map_left _ _ _ e2, map_smul, map_smul, map_smul]
  congr 1
  simp only [← GrOperad.map_trans]
  refine gmap_congr (fun x => ?_) _
  apply Subtype.ext
  rcases x with ⟨a | z, hx⟩ | w
  · simp
  · simp
  · simp

/-- **Composing into the inner factor of a merge-composite**, the inputs named by their values:
`x ⊛ₘ (w ∘ₘ' v) = (x ⊛ₘ w) ∘ₘ' v`, for `w` without unit component. -/
theorem mcL_compL_outer {Y Y₁ Y₂ Y₃ Y₁₂ Y₂₃ : Finset ℕ} {m m' : ℕ}
    (s₁ : LabSplit Y₂₃ Y₂ Y₃ m') (s₂ : LabSplit Y Y₁ Y₂₃ m) (s₃ : LabSplit Y₁₂ Y₁ Y₂ m)
    (s₄ : LabSplit Y Y₁₂ Y₃ m') (X : 𝒞 (Lab Y₁)) {W : 𝒞 (Lab Y₂)}
    (hW : FreeGrL.unitCoeffL R (BarGen I) _ W = 0) (V : 𝒞 (Lab Y₃)) :
    mcL s₂ X (compL R s₁ W V) = compL R s₄ (mcL s₃ X W) V := by
  have e2 : (FreeGrL.labSplit s₃.mem s₃.iff s₃.disj).symm (Sum.inr ⟨m', s₁.mem⟩)
      = (⟨m', s₄.mem⟩ : Lab Y₁₂) := Subtype.ext (by simp)
  have ho := (Bar.mergeSp I).comp_mc_outer (⟨m, s₂.mem⟩ : Lab Y₁) (⟨m', s₁.mem⟩ : Lab Y₂) X hW V
  rw [mcL_apply, compL_apply, MergeSp.mc_map_right, ← ho, compL_apply, mcL_apply,
    GrOperad.comp_map_left _ _ _ e2]
  simp only [← GrOperad.map_trans]
  erw [← GrOperad.map_trans]
  apply gmap_congr
  intro x
  apply Subtype.ext
  rcases x with ⟨a | z, hx⟩ | w <;> rfl

end LabMerge

namespace ShuffleBarSym

open LTree

/-! ## Parities and Koszul signs -/

section Signs

lemma bodd_toNat_bodd (n : ℕ) : Nat.bodd (Nat.bodd n).toNat = Nat.bodd n := by
  cases Nat.bodd n <;> rfl

lemma bodd_sum_toNat {X : Type*} (s : Finset X) (f : X → ℕ) :
    Nat.bodd (∑ x ∈ s, (Nat.bodd (f x)).toNat) = Nat.bodd (∑ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Nat.bodd_add, Nat.bodd_add, ih,
      bodd_toNat_bodd]

/-- **The parity of a tree of odd vertices** is the parity of its number of vertices. -/
lemma vpar_true {B : ℕ → Type*} : ∀ t : STree B, vpar (fun _ _ => true) t = Nat.bodd t.weight
  | .leaf _ => by simp
  | .node _ ch => by
    rw [vpar_node, GrEnd.tot, weight_node]
    simp only [vpar_true (ch _)]
    rw [bodd_sum_toNat, Nat.bodd_add]
    rfl

variable (K : Type u) [CommRing K]

lemma σ_bodd (n : ℕ) : σ K (Nat.bodd n) = (-1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.bodd_succ, pow_succ, ← ih]
    cases Nat.bodd n <;> simp

lemma σ_bodd_and (a b : ℕ) : σ K (Nat.bodd a && Nat.bodd b) = (-1) ^ (a * b) := by
  rw [← Nat.bodd_mul, σ_bodd]

/-- A factor of the Koszul sign `kz`. -/
noncomputable def kzF {α : Type*} {N : ℕ} (π : Equiv.Perm (Fin N)) (B : Fin N → List α)
    (a b : Fin N) : K :=
  if a < b ∧ π.symm b < π.symm a then (-1 : K) ^ ((B a).length * (B b).length) else 1

lemma kz_eq_prod_kzF {α : Type*} {N : ℕ} (B : Fin N → List α) (π : Equiv.Perm (Fin N)) :
    kz K B π = ∏ a, ∏ b, kzF K π B a b := rfl

lemma kzF_update {α : Type*} {N : ℕ} (B : Fin N → List α) (π : Equiv.Perm (Fin N))
    (r₀ a b : Fin N) :
    kzF K π B a b = kzF K π (update B r₀ []) a b * (if a = r₀ then kzF K π B r₀ b else 1)
      * (if b = r₀ then kzF K π B a r₀ else 1) := by
  by_cases ha : a = r₀ <;> by_cases hb : b = r₀
  · subst ha hb
    simp [kzF]
  · subst ha
    rw [if_pos rfl, if_neg hb, mul_one]
    unfold kzF
    rw [update_self, List.length_nil, Nat.zero_mul, pow_zero, ite_self, one_mul]
  · subst hb
    rw [if_neg ha, if_pos rfl, mul_one]
    unfold kzF
    rw [update_self, List.length_nil, Nat.mul_zero, pow_zero, ite_self, one_mul]
  · rw [if_neg ha, if_neg hb, mul_one, mul_one]
    unfold kzF
    rw [update_of_ne ha, update_of_ne hb]

/-- **Koszul signs of a block moved to the leaf of its least entry**: the Koszul sign of sorting
blocks, times the signs of the block `r₀` with the blocks sorted after it, is the Koszul sign with
the block `r₀` emptied, times the signs of the block `r₀` with the blocks after it in the original
order. -/
theorem kz_mul_after {α : Type*} {N : ℕ} (B : Fin N → List α) (π : Equiv.Perm (Fin N))
    (r₀ : Fin N) :
    kz K B π * ∏ r, (if π.symm r₀ < π.symm r then (-1 : K) ^ ((B r₀).length * (B r).length)
      else 1)
      = kz K (update B r₀ []) π
        * ∏ r, (if r₀ < r then (-1 : K) ^ ((B r₀).length * (B r).length) else 1) := by
  have hrow : ∀ (g : Fin N → K) (a : Fin N),
      (∏ b, if a = r₀ then g b else 1) = if a = r₀ then ∏ b, g b else 1 := fun g a => by
    split_ifs <;> simp
  have hcol : ∀ (g : Fin N → K) (a : Fin N),
      (∏ b : Fin N, if b = r₀ then g a else 1) = g a := fun g a => by
    rw [Finset.prod_ite_eq' Finset.univ r₀ (fun _ => g a), if_pos (Finset.mem_univ _)]
  have hsplit : ∏ a, ∏ b, kzF K π B a b = (∏ a, ∏ b, kzF K π (update B r₀ []) a b)
      * (∏ b, kzF K π B r₀ b) * ∏ a, kzF K π B a r₀ := by
    rw [Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => kzF_update K B π r₀ a b]
    simp only [Finset.prod_mul_distrib, hrow, hcol]
    rw [Finset.prod_ite_eq' Finset.univ r₀ (fun _ => ∏ b, kzF K π B r₀ b),
      if_pos (Finset.mem_univ _)]
  rw [kz_eq_prod_kzF, kz_eq_prod_kzF, hsplit]
  rw [mul_assoc, mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun r _ => ?_
  by_cases hr : r = r₀
  · subst hr
    simp [kzF]
  · have hne : π.symm r₀ ≠ π.symm r := fun e => hr (π.symm.injective e).symm
    have hsq : (-1 : K) ^ ((B r).length * (B r₀).length)
        * (-1) ^ ((B r₀).length * (B r).length) = 1 := by
      rw [Nat.mul_comm, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    unfold kzF
    rcases lt_or_gt_of_ne hr with h | h <;> rcases lt_or_gt_of_ne hne with h' | h'
    · simp [h, h', lt_asymm h, lt_asymm h', hsq]
    · simp [h, h', lt_asymm h, lt_asymm h']
    · simp [h, h', lt_asymm h, lt_asymm h']
    · simp [h, h', lt_asymm h, lt_asymm h']

end Signs

/-! ## Trees -/

section TreeLemmas

variable {B : ℕ → Type*}

/-- **The parity after a leaf child**: the parity of the children after it. -/
lemma vaft_node_of_leaf (p : ∀ k, B k → Bool) {k : ℕ} (β : B k) (C : Fin k → STree B)
    (s₀ : Fin k) (m : ℕ) (hC : C s₀ = .leaf m) (hm : ∀ s, s ≠ s₀ → m ∉ (C s).labels) :
    vaft p (.node β C) m = GrEnd.tot fun s => if s₀ < s then vpar p (C s) else false := by
  rw [vaft_node]
  congr 1
  funext s
  by_cases hs : s = s₀
  · subst hs
    rw [if_pos (by rw [hC]; exact Multiset.mem_singleton_self m), hC, vaft_leaf,
      if_neg (lt_irrefl _)]
  · rw [if_neg (hm s hs)]
    have hiff : (∃ j', j' < s ∧ m ∈ (C j').labels) ↔ s₀ < s := by
      constructor
      · rintro ⟨j', hj', hmj⟩
        by_cases e : j' = s₀
        · exact e ▸ hj'
        · exact absurd hmj (hm j' e)
      · intro h
        exact ⟨s₀, h, by rw [hC]; exact Multiset.mem_singleton_self m⟩
    by_cases h : s₀ < s
    · rw [if_pos (hiff.2 h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]

lemma σ_and_vaft_node_of_leaf (K : Type u) [CommRing K] (p : ∀ k, B k → Bool) {k : ℕ} (β : B k)
    (C : Fin k → STree B) (s₀ : Fin k) (m : ℕ) (hC : C s₀ = .leaf m)
    (hm : ∀ s, s ≠ s₀ → m ∉ (C s).labels) (x : Bool) :
    σ K (x && vaft p (.node β C) m) = ∏ s, if s₀ < s then σ K (x && vpar p (C s)) else 1 := by
  rw [vaft_node_of_leaf p β C s₀ m hC hm, ← GrEnd.prod_σ_tot]
  refine Finset.prod_congr rfl fun s _ => ?_
  split_ifs <;> simp

/-- **Substituting back a child cut off at a leaf.** -/
lemma subst_update_comp {k : ℕ} (β : B k) (Q : Fin k → STree B) (r₀ : Fin k) (m : ℕ)
    (hm : ∀ r, r ≠ r₀ → m ∉ (Q r).labels) (π : Equiv.Perm (Fin k)) :
    (STree.node β (update Q r₀ (.leaf m) ∘ π)).subst (update STree.leaf m (Q r₀))
      = STree.node β (Q ∘ π) := by
  rw [subst_node]
  congr 1
  funext s
  simp only [comp_apply]
  by_cases hs : π s = r₀
  · rw [hs, update_self, subst_leaf', update_self]
  · rw [update_of_ne hs]
    exact (subst_congr _ fun a ha => update_of_ne (fun e : a = m => hm _ hs (e ▸ ha)) _ _).trans
      (subst_leaf _)

lemma subst_update_child {k : ℕ} (β : B k) (ch : Fin k → STree B) (j : Fin k) (m : ℕ)
    (x : STree B) (hm : ∀ a, a ≠ j → m ∉ (ch a).labels) :
    (STree.node β (update ch j (.leaf m))).subst (update STree.leaf m x)
      = STree.node β (update ch j x) := by
  have := subst_update_comp β (update ch j x) j m (fun r hr => by
    rw [update_of_ne hr]; exact hm r hr) (Equiv.refl _)
  simpa using this

/-- The leaves of a tree with a tree substituted for one of its leaves. -/
lemma labels_subst_update_add (t x : STree B) {m : ℕ} (hm : m ∈ t.labels)
    (hnd : t.labels.Nodup) :
    (t.subst (update STree.leaf m x)).labels + {m} = t.labels + x.labels := by
  have ht : t.labels = m ::ₘ t.labels.erase m := (Multiset.cons_erase hm).symm
  have hnm : m ∉ t.labels.erase m := by
    rw [ht] at hnd
    exact (Multiset.nodup_cons.1 hnd).1
  rw [labels_subst, ht, Multiset.cons_bind, update_self]
  rw [Multiset.bind_congr (g := fun a => {a}) fun a ha => by
    rw [update_of_ne (fun e : a = m => hnm (e ▸ ha)), STree.labels_leaf], Multiset.bind_singleton,
    Multiset.map_id']
  rw [← Multiset.singleton_add]
  abel

lemma weight_update_child {k : ℕ} (β : B k) (ch : Fin k → STree B) (j : Fin k) (x : STree B) :
    (STree.node β (update ch j x)).weight + (ch j).weight
      = (STree.node β ch).weight + x.weight := by
  simp only [weight_node]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
    ← Finset.add_sum_erase _ (fun i => (ch i).weight) (Finset.mem_univ j), update_self]
  have : ∑ i ∈ Finset.univ.erase j, (update ch j x i).weight
      = ∑ i ∈ Finset.univ.erase j, (ch i).weight :=
    Finset.sum_congr rfl fun i hi => by rw [update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [this]
  ring

end TreeLemmas

section PlanarUpdate

variable {B : ℕ → Type*} {k l N : ℕ} (ch : Fin k → STree B) (j : Fin k) (c₂ : Fin l → STree B)
  (hN : N + 1 = k + l)

lemma planar_update_left (i : Fin k) (hi : i ≠ j) (x : STree B) :
    planar (update ch i x) j c₂ hN
      = update (planar ch j c₂ hN) (posEquivF j l N hN (Sum.inl ⟨i, hi⟩)) x := by
  funext r
  obtain ⟨y, rfl⟩ := (posEquivF j l N hN).surjective r
  rcases y with a | a
  · rw [planar_inl]
    by_cases ha : a = ⟨i, hi⟩
    · subst ha
      rw [update_self, update_self]
    · rw [update_of_ne (fun e => ha (Subtype.ext e)),
        update_of_ne (fun e => ha (Sum.inl_injective ((posEquivF j l N hN).injective e))),
        planar_inl]
  · rw [planar_inr,
      update_of_ne (fun e => Sum.inl_ne_inr ((posEquivF j l N hN).injective e).symm), planar_inr]

lemma planar_update_right (i : Fin l) (x : STree B) :
    planar ch j (update c₂ i x) hN
      = update (planar ch j c₂ hN) (posEquivF j l N hN (Sum.inr i)) x := by
  funext r
  obtain ⟨y, rfl⟩ := (posEquivF j l N hN).surjective r
  rcases y with a | a
  · rw [planar_inl, update_of_ne (fun e => Sum.inl_ne_inr ((posEquivF j l N hN).injective e)),
      planar_inl]
  · rw [planar_inr]
    by_cases ha : a = i
    · subst ha
      rw [update_self, update_self]
    · rw [update_of_ne ha,
        update_of_ne (fun e => ha (Sum.inr_injective ((posEquivF j l N hN).injective e))),
        planar_inr]

end PlanarUpdate

lemma sortP_congr {B : ℕ → Type*} {N : ℕ} {Q Q' : Fin N → STree B}
    (h : ∀ r, (Q r).first = (Q' r).first) : sortP Q = sortP Q' := by
  unfold sortP
  congr 1
  funext r
  exact h r

/-! ## Merging two basis generators -/

section MsVal

variable {K : Type u} [CommRing K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {G : Type} [Fintype G] [DecidableEq G]
  (c : ∀ k, Module.Basis (BinGen G k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen G k), GrSpecies.par (R := K) false (c k β) = c k β)

/-- An injective function on `Fin k`, as a bijection with its image. -/
noncomputable def labOfInj {k : ℕ} (f : Fin k → ℕ) (hf : Function.Injective f) :
    Fin k ≃ Lab (Finset.univ.image f) :=
  Equiv.ofBijective (fun a => ⟨f a, Finset.mem_image_of_mem _ (Finset.mem_univ a)⟩)
    ⟨fun a b h => hf (congrArg Subtype.val h), fun ⟨x, hx⟩ => by
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨a, rfl⟩⟩

omit [Fintype G] [DecidableEq G] in
@[simp] lemma labOfInj_val {k : ℕ} (f : Fin k → ℕ) (hf : Function.Injective f) (a : Fin k) :
    (labOfInj f hf a).1 = f a := rfl

/-- The rank function of the leaves of the vertex, with the leaf `q` sent out of range. -/
noncomputable def rk₁' {k l N : ℕ} (q : Fin k) (hN : N + 1 = k + l) (π : Equiv.Perm (Fin N))
    (a : ℕ) : ℕ :=
  if a = q then N else rk₁ q hN π a

omit [Fintype G] [DecidableEq G] in
lemma rk₁'_injective {k l N : ℕ} (q : Fin k) (hN : N + 1 = k + l) (π : Equiv.Perm (Fin N)) :
    Function.Injective fun a : Fin k => rk₁' q hN π a := by
  have hval : ∀ (a : Fin k) (ha : a ≠ q),
      rk₁' q hN π a = π.symm (posEquivF q l N hN (Sum.inl ⟨a, ha⟩)) := fun a ha => by
    rw [rk₁', if_neg (fun h => ha (Fin.ext h))]
    exact rk₁_of q hN π ⟨a, ha⟩
  have hq : rk₁' q hN π q = N := if_pos rfl
  intro a b hab
  change rk₁' q hN π a = rk₁' q hN π b at hab
  by_cases ha : a = q <;> by_cases hb : b = q
  · rw [ha, hb]
  · rw [ha, hq, hval b hb] at hab
    exact absurd hab.symm (by omega)
  · rw [hb, hq, hval a ha] at hab
    exact absurd hab (by omega)
  · rw [hval a ha, hval b hb] at hab
    have := (posEquivF q l N hN).injective (π.symm.injective (Fin.ext hab))
    simpa using this

omit [Fintype G] [DecidableEq G] in
lemma rk₂_injective {k l N : ℕ} (q : Fin k) (hN : N + 1 = k + l) (π : Equiv.Perm (Fin N)) :
    Function.Injective fun i : Fin l => rk₂ q hN π i := by
  intro a b hab
  simp only [rk₂_of] at hab
  have := (posEquivF q l N hN).injective (π.symm.injective (Fin.ext hab))
  simpa using this

omit [Fintype G] [DecidableEq G] in
lemma mergeMono_rk₁' {k l N : ℕ} (m₁ : LTree G) (q : Fin k) (m₂ : LTree G) (hN : N + 1 = k + l)
    (π : Equiv.Perm (Fin N)) :
    mergeMono m₁ q m₂ (rk₁' q hN π) (rk₂ q hN π) = mergedMono m₁ q m₂ hN π := by
  unfold mergedMono mergeMono
  congr 1
  funext a
  split_ifs with h
  · rfl
  · rw [rk₁', if_neg h]

/-- **Merging two basis generators of the bar construction** gives the basis generator of the
merged monomial, its inputs relabelled by the permutation `π` naming the leaves of the merged
monomial: `s m₁ ⊛_q s m₂ = π · s (mergedMono m₁ q m₂ π)`, without sign since `T` is even. -/
theorem msVal_genBasis {k l N : ℕ} (m₁ : VMono G k) (q : Fin k) (m₂ : VMono G l)
    (hN : N + 1 = k + l) (π : Equiv.Perm (Fin N))
    (hM : mergedMono m₁.1 q m₂.1 hN π ∈ LTree.monomials N ∧ 2 ≤ N) :
    Bar.msVal (Ibar K E c hc) true (genBasis c hc k m₁) q (genBasis c hc l m₂) N hN
      = SymSpecies.map (R := K) π (genBasis c hc N ⟨_, hM⟩) := by
  set θ₁ := labOfInj _ (rk₁'_injective q hN π) with hθ₁
  set θ₂ := labOfInj _ (rk₂_injective q hN π) with hθ₂
  have hM' : mergedMono m₁.1 q m₂.1 hN π ∈ LTree.monomials (Fintype.card (Fin N)) := by
    rw [Fintype.card_fin]
    exact hM.1
  have hY : (toBinSTree (mergeMono m₁.1 q m₂.1 (rk₁' q hN π) (rk₂ q hN π))).labels
      = (Finset.range (Fintype.card (Fin N))).val := by
    rw [mergeMono_rk₁']
    exact labels_toBinSTree_mono _ hM'
  let E' : Lab (Finset.range (Fintype.card (Fin N))) ≃ Without (Lab _) (θ₁ q) ⊕ Lab _ :=
    (FreeGrL.posEquiv (Fin N)).symm.trans
      (π.trans ((posEquivF q l N hN).symm.trans (compEquiv θ₁ θ₂ q)))
  have hE : ∀ x, FreeGrL.sval (E' x) = x.1 := by
    intro x
    have hx : (π.symm (π ((FreeGrL.posEquiv (Fin N)).symm x)) : ℕ) = x.1 := by
      rw [Equiv.symm_apply_apply, val_symm_posEquiv]
    obtain ⟨y, hy⟩ : ∃ y, (posEquivF q l N hN).symm (π ((FreeGrL.posEquiv (Fin N)).symm x)) = y :=
      ⟨_, rfl⟩
    have hp : π ((FreeGrL.posEquiv (Fin N)).symm x) = posEquivF q l N hN y := by
      rw [← hy, Equiv.apply_symm_apply]
    rw [hp] at hx
    show FreeGrL.sval (compEquiv θ₁ θ₂ q ((posEquivF q l N hN).symm
      (π ((FreeGrL.posEquiv (Fin N)).symm x)))) = x.1
    rw [hy]
    rcases y with a | i
    · rw [compEquiv_inl, FreeGrL.sval_inl, hθ₁, labOfInj_val, rk₁',
        if_neg (fun h => a.2 (Fin.ext h)), rk₁_of, ← hx]
    · rw [compEquiv_inr, FreeGrL.sval_inr, hθ₂, labOfInj_val, rk₂_of, ← hx]
  have hB := comp_tBasis c hc m₁.1 (by simpa using m₁.2.1) m₂.1 (by simpa using m₂.2.1) θ₁ θ₂
    (rk₁' q hN π) (rk₂ q hN π) (fun _ => rfl) (fun _ => rfl) q hY E' hE
  have hc' := GrOperad.map_comp (R := K) (P := FreeGrL K E) θ₁ θ₂ q
    (tBasis c hc (Fin k) ⟨m₁.1, by simpa using m₁.2.1⟩)
    (tBasis c hc (Fin l) ⟨m₂.1, by simpa using m₂.2.1⟩)
  rw [hB] at hc'
  have hc'' := congrArg (GrOperad.map (R := K) (compEquiv θ₁ θ₂ q).symm) hc'
  rw [← GrOperad.map_trans, Equiv.self_trans_symm, GrOperad.map_refl] at hc''
  refine IdealSp.ext _ ?_
  rw [Bar.val_msVal]
  show _ = GrOperad.map (R := K) π (idealBasis c hc N ⟨_, hM⟩ : FreeGrL K E (Fin N))
  rw [Bool.not_true, σ_false, one_smul]
  show GrOperad.map (R := K) _ (GrOperad.comp (R := K) q
    (idealBasis c hc k m₁ : FreeGrL K E (Fin k)) (idealBasis c hc l m₂ : FreeGrL K E (Fin l)))
    = _
  rw [idealBasis_apply, idealBasis_apply, idealBasis_apply, tBasis_apply c hc (Fin N),
    FreeGrL.shuffleBasis_apply, hc'']
  have hT : FreeGrL.shEv c (toBinSTree (mergeMono m₁.1 q m₂.1 (rk₁' q hN π) (rk₂ q hN π))) _ hY
      = FreeGrL.shEv c (toBinSTree (mergedMono m₁.1 q m₂.1 hN π)) _
          (labels_toBinSTree_mono _ hM') := by
    have := FreeGrL.map_shEv c (congrArg toBinSTree (mergeMono_rk₁' m₁.1 q m₂.1 hN π)) rfl hY
      (labels_toBinSTree_mono _ hM') (Equiv.refl _) fun _ => rfl
    rwa [GrOperad.map_refl] at this
  rw [hT]
  simp only [← GrOperad.map_trans]
  refine Eq.trans (gmap_congr (e' := (FreeGrL.posEquiv (Fin N)).symm.trans π) (fun x => ?_) _) rfl
  simp [E']

end MsVal

end ShuffleBarSym

namespace ShuffleBarSym

/-! ## Children cut off and substituted back -/

section Cut

variable {B : ℕ → Type*}

lemma first_update_child {k : ℕ} (ch : Fin k → STree B) (i : Fin k) (x : STree B)
    (hx : x.first = (ch i).first) (a : Fin k) : (update ch i x a).first = (ch a).first := by
  by_cases ha : a = i
  · subst ha
    rw [update_self, hx]
  · rw [update_of_ne ha]

lemma isShuffle_update_child {k : ℕ} {β : B k} {ch : Fin k → STree B}
    (ht : (STree.node β ch).IsShuffle) (i : Fin k) {x : STree B} (hx : x.IsShuffle)
    (hfx : x.first = (ch i).first) : (STree.node β (update ch i x)).IsShuffle := by
  refine ⟨ht.pos, fun a => ?_, ?_⟩
  · by_cases ha : a = i
    · subst ha
      rw [update_self]
      exact hx
    · rw [update_of_ne ha]
      exact ht.child a
  · simp only [first_update_child ch i x hfx]
    exact ht.mono

lemma first_node_update_child {k : ℕ} (β : B k) (ch : Fin k → STree B) (i : Fin k) (x : STree B)
    (hfx : x.first = (ch i).first) :
    (STree.node β (update ch i x)).first = (STree.node β ch).first := by
  have hk : 0 < k := Fin.pos i
  rw [first_node _ _ hk, first_node _ _ hk, first_update_child ch i x hfx]

lemma labels_update_child {k : ℕ} (β : B k) (ch : Fin k → STree B) (i : Fin k) (x : STree B) :
    (STree.node β (update ch i x)).labels + (ch i).labels
      = (STree.node β ch).labels + x.labels := by
  simp only [labels_node]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ (fun a => (ch a).labels) (Finset.mem_univ i), update_self]
  have : ∑ a ∈ Finset.univ.erase i, (update ch i x a).labels
      = ∑ a ∈ Finset.univ.erase i, (ch a).labels :=
    Finset.sum_congr rfl fun a ha => by rw [update_of_ne (Finset.ne_of_mem_erase ha)]
  rw [this]
  abel

lemma labels_update_leaf_le {k : ℕ} (β : B k) (ch : Fin k → STree B) (i : Fin k) {x : ℕ}
    (hx : x ∈ (ch i).labels) :
    (STree.node β (update ch i (.leaf x))).labels ≤ (STree.node β ch).labels := by
  simp only [labels_node]
  refine Finset.sum_le_sum fun a _ => ?_
  by_cases ha : a = i
  · subst ha
    rw [update_self, labels_leaf]
    exact Multiset.singleton_le.2 hx
  · rw [update_of_ne ha]

lemma vpar_true_of_weight_eq_zero {t : STree B} (h : t.weight = 0) :
    vpar (fun _ _ => true) t = false := by
  rw [vpar_true, h]
  rfl

lemma preKeys_of_weight_eq_zero {t : STree B} (h : t.weight = 0) : preKeys t = [] := by
  obtain ⟨a, rfl⟩ := exists_leaf_of_weight_eq_zero h
  rfl

end Cut

/-! ## The positions of the children of a merged vertex -/

lemma posEquivF_inl_val {k l N : ℕ} (j : Fin k) (hN : N + 1 = k + l) (a : Without (Fin k) j) :
    (posEquivF j l N hN (Sum.inl a) : ℕ) = if (a.1 : ℕ) < j then (a.1 : ℕ) else (a.1 : ℕ) + l - 1
    := by
  split_ifs with h
  · exact posEquivF_inl_of_lt j hN a h
  · have hne : (a.1 : ℕ) ≠ j := fun e => a.2 (Fin.ext e)
    have := posEquivF_inl_of_gt j hN a (show j < a.1 by
      show (j : ℕ) < a.1
      omega)
    omega

lemma planar_update_self {B : ℕ → Type*} {k l N : ℕ} (ch : Fin k → STree B) (j : Fin k)
    (c₂ : Fin l → STree B) (hN : N + 1 = k + l) (x : STree B) :
    planar (update ch j x) j c₂ hN = planar ch j c₂ hN := by
  funext r
  obtain ⟨y, rfl⟩ := (posEquivF j l N hN).surjective r
  rcases y with a | a
  · rw [planar_inl, planar_inl, update_of_ne a.2]
  · rw [planar_inr, planar_inr]

/-! ## Koszul signs and the parity after a leaf -/

section KzVaft

variable (K : Type u) [CommRing K] {G : Type} [Fintype G] [DecidableEq G]

/-- **The Koszul sign of sorting the children of a vertex, with one child cut off**: times the
parity after the leaf left by that child, it is the Koszul sign without that child times the signs
of that child with the children after it in the original order. -/
theorem kz_mul_σ_vaft {N : ℕ} (M : VMono G N) (Q : Fin N → STree (VMono G)) (r₀ : Fin N) (m' : ℕ)
    (hd : ∀ r, r ≠ r₀ → m' ∉ (Q r).labels) (π : Equiv.Perm (Fin N)) :
    kz K (fun r => preKeys (Q r)) π
        * σ K (vpar (fun _ _ => true) (Q r₀)
          && vaft (fun _ _ => true) (STree.node M (update Q r₀ (.leaf m') ∘ π)) m')
      = kz K (fun r => preKeys (update Q r₀ (.leaf m') r)) π
        * ∏ r, (if r₀ < r then (-1 : K) ^ ((Q r₀).weight * (Q r).weight) else 1) := by
  have hC : (update Q r₀ (.leaf m') ∘ π) (π.symm r₀) = .leaf m' := by
    rw [comp_apply, Equiv.apply_symm_apply, update_self]
  have hm : ∀ s, s ≠ π.symm r₀ → m' ∉ ((update Q r₀ (.leaf m') ∘ π) s).labels := by
    intro s hs
    have hs' : π s ≠ r₀ := fun e => hs (by rw [← e, Equiv.symm_apply_apply])
    simp only [comp_apply, update_of_ne hs']
    exact hd _ hs'
  rw [σ_and_vaft_node_of_leaf K _ M _ (π.symm r₀) m' hC hm]
  rw [← Equiv.prod_comp π.symm]
  have hB : (fun r => preKeys (update Q r₀ (.leaf m') r))
      = update (fun r => preKeys (Q r)) r₀ [] := by
    funext r
    by_cases hr : r = r₀
    · subst hr
      rw [update_self, update_self]
      rfl
    · rw [update_of_ne hr, update_of_ne hr]
  have hprod : (∏ r, if π.symm r₀ < π.symm r then σ K (vpar (fun _ _ => true) (Q r₀)
        && vpar (fun _ _ => true) ((update Q r₀ (.leaf m') ∘ π) (π.symm r))) else 1)
      = ∏ r, (if π.symm r₀ < π.symm r then (-1 : K) ^ ((preKeys (Q r₀)).length
          * (preKeys (Q r)).length) else 1) := by
    refine Finset.prod_congr rfl fun r _ => ?_
    split_ifs with h
    · have hr : r ≠ r₀ := fun e => lt_irrefl _ (e ▸ h)
      rw [comp_apply, Equiv.apply_symm_apply, update_of_ne hr, vpar_true, vpar_true, σ_bodd_and,
        length_preKeys, length_preKeys]
    · rfl
  rw [hprod, kz_mul_after K (fun r => preKeys (Q r)) π r₀, hB]
  simp only [length_preKeys]

end KzVaft

end ShuffleBarSym

namespace ShuffleBarSym

/-! ## The planar signs after a child of a merged vertex -/

section After

variable (K : Type u) [CommRing K] {B : ℕ → Type*}

/-- The children after a child `i₀` of the vertex, all of whose later siblings other than `j` are
leaves, are those of the child `j`. -/
lemma prod_after_left {k l N : ℕ} (ch : Fin k → STree B) (j : Fin k) (c₂ : Fin l → STree B)
    (hN : N + 1 = k + l) (i₀ : Fin k) (hi₀ : i₀ ≠ j) (hlt : i₀ < j)
    (hafter : ∀ a, i₀ < a → a ≠ j → (ch a).weight = 0) :
    ∏ r, (if posEquivF j l N hN (Sum.inl ⟨i₀, hi₀⟩) < r then (-1 : K) ^
        ((planar ch j c₂ hN (posEquivF j l N hN (Sum.inl ⟨i₀, hi₀⟩))).weight
          * (planar ch j c₂ hN r).weight) else 1)
      = (-1) ^ ((ch i₀).weight * ∑ i, (c₂ i).weight) := by
  rw [planar_inl, ← (posEquivF j l N hN).prod_comp, Fintype.prod_sum_type]
  have hlt' : (i₀ : ℕ) < j := hlt
  have hv0 : (posEquivF j l N hN (Sum.inl ⟨i₀, hi₀⟩) : ℕ) = i₀ := by
    rw [posEquivF_inl_val]
    exact if_pos hlt'
  have h1 : (∏ a : Without (Fin k) j, if posEquivF j l N hN (Sum.inl ⟨i₀, hi₀⟩)
      < posEquivF j l N hN (Sum.inl a) then (-1 : K) ^ ((ch i₀).weight
        * (planar ch j c₂ hN (posEquivF j l N hN (Sum.inl a))).weight) else 1) = 1 := by
    refine Finset.prod_eq_one fun a _ => ?_
    split_ifs with h
    · have hv := posEquivF_inl_val j hN a
      have hne : (a.1 : ℕ) ≠ j := fun e => a.2 (Fin.ext e)
      rw [Fin.lt_def, hv0] at h
      have hia : i₀ < a.1 := by
        show (i₀ : ℕ) < a.1
        split_ifs at hv <;> omega
      rw [planar_inl, hafter a.1 hia a.2, Nat.mul_zero, pow_zero]
    · rfl
  have h2 : ∀ i : Fin l, posEquivF j l N hN (Sum.inl ⟨i₀, hi₀⟩) < posEquivF j l N hN (Sum.inr i) :=
    fun i => by
      rw [Fin.lt_def, hv0, posEquivF_inr]
      omega
  rw [h1, one_mul]
  simp only [if_pos (h2 _), planar_inr]
  rw [Finset.prod_pow_eq_pow_sum, Finset.mul_sum]

/-- The children after a child `i₀` of the child `j`, all of whose later siblings are leaves, the
other children of the vertex being leaves, are leaves. -/
lemma prod_after_right {k l N : ℕ} (ch : Fin k → STree B) (j : Fin k) (c₂ : Fin l → STree B)
    (hN : N + 1 = k + l) (i₀ : Fin l) (hl₁ : ∀ a, a ≠ j → (ch a).weight = 0)
    (hafter : ∀ i, i₀ < i → (c₂ i).weight = 0) :
    ∏ r, (if posEquivF j l N hN (Sum.inr i₀) < r then (-1 : K) ^
        ((planar ch j c₂ hN (posEquivF j l N hN (Sum.inr i₀))).weight
          * (planar ch j c₂ hN r).weight) else 1) = 1 := by
  refine Finset.prod_eq_one fun r _ => ?_
  obtain ⟨y, rfl⟩ := (posEquivF j l N hN).surjective r
  split_ifs with h
  · rcases y with a | i
    · rw [planar_inl, hl₁ a.1 a.2, Nat.mul_zero, pow_zero]
    · rw [Fin.lt_def, posEquivF_inr, posEquivF_inr] at h
      have hi : i₀ < i := by
        show (i₀ : ℕ) < i
        omega
      rw [planar_inr, planar_inr, hafter i hi, Nat.mul_zero, pow_zero]
  · rfl

/-- The children after a later child `j` of the vertex merged with its child `j'`, all children
after `j` being leaves, are leaves. -/
lemma prod_after_merged {k l N : ℕ} (ch : Fin k → STree B) (j' : Fin k) (c₂ : Fin l → STree B)
    (hN : N + 1 = k + l) (j : Fin k) (hjj : j ≠ j') (hlt : j' < j)
    (hafter : ∀ a, j < a → (ch a).weight = 0) :
    ∏ r, (if posEquivF j' l N hN (Sum.inl ⟨j, hjj⟩) < r then (-1 : K) ^
        ((planar ch j' c₂ hN (posEquivF j' l N hN (Sum.inl ⟨j, hjj⟩))).weight
          * (planar ch j' c₂ hN r).weight) else 1) = 1 := by
  refine Finset.prod_eq_one fun r _ => ?_
  obtain ⟨y, rfl⟩ := (posEquivF j' l N hN).surjective r
  have hlt' : ¬ (j : ℕ) < j' := fun h => absurd hlt (not_lt.2 (le_of_lt h))
  have hv0 : (posEquivF j' l N hN (Sum.inl ⟨j, hjj⟩) : ℕ) = j + l - 1 := by
    rw [posEquivF_inl_val]
    exact if_neg hlt'
  split_ifs with h
  · rcases y with a | i
    · have hv := posEquivF_inl_val j' hN a
      have hne : (a.1 : ℕ) ≠ j' := fun e => a.2 (Fin.ext e)
      rw [Fin.lt_def, hv0] at h
      have hja : j < a.1 := by
        show (j : ℕ) < a.1
        have : (j' : ℕ) < j := hlt
        split_ifs at hv <;> omega
      rw [planar_inl, planar_inl, hafter a.1 hja, Nat.mul_zero, pow_zero]
    · rw [Fin.lt_def, hv0, posEquivF_inr] at h
      have : (j' : ℕ) < j := hlt
      have := i.2
      omega
  · rfl

end After

/-! ## Merging the root of a tree into a vertex -/

section RootMergeL

variable {K : Type u} [CommRing K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {G : Type} [Fintype G] [DecidableEq G]
  (c : ∀ k, Module.Basis (BinGen G k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen G k), GrSpecies.par (R := K) false (c k β) = c k β)

lemma shEv_congr {t t' : STree (VMono G)} (ht : t = t') (Y : Finset ℕ) (h : t.labels = Y.val)
    (h' : t'.labels = Y.val) :
    FreeGrL.shEv (genBasis c hc) t Y h = FreeGrL.shEv (genBasis c hc) t' Y h' := by
  subst ht
  rfl

lemma unitCoeffL_shEv_node {k : ℕ} (β : VMono G k) (ch : Fin k → STree (VMono G)) (Y : Finset ℕ)
    (h : (STree.node β ch).labels = Y.val) :
    FreeGrL.unitCoeffL K (BarGen (Ibar K E c hc)) _
      (FreeGrL.shEv (genBasis c hc) (.node β ch) Y h) = 0 := by
  rw [FreeGrL.shEv_node, FreeGrL.unitCoeffL_graft]

variable (K) in
/-- **The sign of merging the root of the child `j` into the vertex**: `(-1)` to the number of the
other vertices below the vertex, times the Koszul sign of sorting the children of the merged vertex.
-/
noncomputable def rmCoeff {k l : ℕ} (m₁ : VMono G k) (ch : Fin k → STree (VMono G)) (j : Fin k)
    (c₂ : Fin l → STree (VMono G)) : K :=
  (-1) ^ ((STree.node m₁ (update ch j (.leaf 0))).weight - 1)
    * kz K (fun r => preKeys (planar ch j c₂ (mergeN_eq m₁ l) r))
      (sortP (planar ch j c₂ (mergeN_eq m₁ l)))

/-- **Merge-composing the evaluations of a tree cut at its child `j` and of that child**: the
evaluation of the tree with the edge above `j` merged, with the sign `rmCoeff`. -/
def RMProp {k l : ℕ} (m₁ : VMono G k) (ch : Fin k → STree (VMono G)) (j : Fin k)
    (m₂ : VMono G l) (c₂ : Fin l → STree (VMono G)) : Prop :=
  ∀ (Y Y₁ Y₂ : Finset ℕ) (m : ℕ) (s : LabSplit Y Y₁ Y₂ m) (T₁ T₂ R : STree (VMono G)),
    m = (STree.node m₂ c₂).first → T₁ = STree.node m₁ (update ch j (.leaf m)) →
    T₂ = STree.node m₂ c₂ → R = rootMerge m₁ ch j m₂ c₂ →
    ∀ (h₁ : T₁.labels = Y₁.val) (h₂ : T₂.labels = Y₂.val) (h : R.labels = Y.val),
      mcL (I := Ibar K E c hc) s (FreeGrL.shEv (genBasis c hc) T₁ Y₁ h₁)
        (FreeGrL.shEv (genBasis c hc) T₂ Y₂ h₂)
        = rmCoeff K m₁ ch j c₂ • FreeGrL.shEv (genBasis c hc) R Y h

/-- **Substituting a child back into the merged vertex.** -/
lemma rootMerge_subst {k l : ℕ} {m₁ : VMono G k} {ch ch' : Fin k → STree (VMono G)} {j : Fin k}
    {m₂ : VMono G l} {c₂ c₂' : Fin l → STree (VMono G)} (hj : ch j = .node m₂ c₂)
    (hj' : ch' j = .node m₂ c₂') (ht : (STree.node m₁ ch).IsShuffle)
    (ht' : (STree.node m₁ ch').IsShuffle) (r₀ : Fin (k + l - 1)) {m' : ℕ} {y : STree (VMono G)}
    (hQ : planar ch' j c₂' (mergeN_eq m₁ l)
      = update (planar ch j c₂ (mergeN_eq m₁ l)) r₀ (.leaf m'))
    (hy : planar ch j c₂ (mergeN_eq m₁ l) r₀ = y) (hf : y.first = m')
    (hd : ∀ r, r ≠ r₀ → m' ∉ (planar ch j c₂ (mergeN_eq m₁ l) r).labels) :
    (rootMerge m₁ ch' j m₂ c₂').subst (update STree.leaf m' y) = rootMerge m₁ ch j m₂ c₂ := by
  have hπ : sortP (planar ch' j c₂' (mergeN_eq m₁ l))
      = sortP (planar ch j c₂ (mergeN_eq m₁ l)) := by
    rw [hQ]
    refine sortP_congr fun r => ?_
    by_cases hr : r = r₀
    · subst hr
      rw [update_self, first_leaf, hy, hf]
    · rw [update_of_ne hr]
  rw [rootMerge_eq hj' ht', rootMerge_eq hj ht, subst_node]
  congr 1
  · exact Subtype.ext (by simp only [hπ])
  · funext s
    simp only [comp_apply]
    rw [hπ, hQ]
    by_cases hs : sortP (planar ch j c₂ (mergeN_eq m₁ l)) s = r₀
    · rw [hs, update_self, subst_leaf', update_self, hy]
    · rw [update_of_ne hs]
      exact (subst_congr _ fun a ha => update_of_ne (fun e : a = m' => hd _ hs (e ▸ ha)) _ _).trans
        (subst_leaf _)

end RootMergeL

end ShuffleBarSym

namespace ShuffleBarSym

lemma labels_update_le {B : ℕ → Type*} {k : ℕ} (β : B k) (ch : Fin k → STree B) (i : Fin k)
    {x : STree B} (hx : x.labels ≤ (ch i).labels) :
    (STree.node β (update ch i x)).labels ≤ (STree.node β ch).labels := by
  simp only [labels_node]
  refine Finset.sum_le_sum fun a _ => ?_
  by_cases ha : a = i
  · subst ha
    rw [update_self]
    exact hx
  · rw [update_of_ne ha]

section RootMergeProof

variable {K : Type u} [CommRing K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {G : Type} [Fintype G] [DecidableEq G]
  (c : ∀ k, Module.Basis (BinGen G k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen G k), GrSpecies.par (R := K) false (c k β) = c k β)

/-- **Merge-composing two relabelled basis generators**, the inputs named by their values. -/
lemma mc_corolla_aux {k l N : ℕ} (m₁ : VMono G k) (m₂ : VMono G l) {Y Y₁ Y₂ : Finset ℕ}
    (θ₁ : Fin k ≃ Lab Y₁) (θ₂ : Fin l ≃ Lab Y₂) (j : Fin k) (i : Lab Y₁) (hi : θ₁ j = i)
    (hN : N + 1 = k + l) (π : Equiv.Perm (Fin N)) (β : VMono G N)
    (hβ : β.1 = mergedMono m₁.1 j m₂.1 hN π) (θ : Fin N ≃ Lab Y)
    (E' : Lab Y ≃ Without (Lab Y₁) i ⊕ Lab Y₂) (hE : ∀ x, FreeGrL.sval (E' x) = x.1)
    (hval : ∀ x : Fin N,
      (θ x).1 = FreeGrL.sval (compEquiv θ₁ θ₂ j ((posEquivF j l N hN).symm (π x)))) :
    GrOperad.map (R := K) E'.symm ((Bar.mergeSp (Ibar K E c hc)).mc i
        (GrOperad.map (R := K) θ₁
          ((FreeGrL.ι K (BarGen (Ibar K E c hc))).app (Fin k) (genBasis c hc k m₁)))
        (GrOperad.map (R := K) θ₂
          ((FreeGrL.ι K (BarGen (Ibar K E c hc))).app (Fin l) (genBasis c hc l m₂))))
      = GrOperad.map (R := K) θ
          ((FreeGrL.ι K (BarGen (Ibar K E c hc))).app (Fin N) (genBasis c hc N β)) := by
  subst hi
  obtain ⟨βv, hM⟩ := β
  simp only at hβ
  subst hβ
  have h1 := Bar.mc_map_ι (Ibar K E c hc) θ₁ θ₂ j _ _ (par_genBasis c hc k m₁)
    (par_genBasis c hc l m₂) N hN
  have h2 := msVal_genBasis c hc m₁ j m₂ hN π hM
  have happ := (FreeGrL.ι K (BarGen (Ibar K E c hc))).app_map π (genBasis c hc N ⟨_, hM⟩)
  simp only [h2, happ] at h1
  rw [h1, GrOperad.toGrSpecies_map]
  simp only [← GrOperad.map_trans]
  refine gmap_congr (fun x => ?_) _
  apply Subtype.ext
  have hs : ∀ u, (E'.symm u).1 = FreeGrL.sval u := fun u => by
    rw [← hE (E'.symm u), Equiv.apply_symm_apply]
  simp only [Equiv.trans_apply, hs]
  exact (hval x).symm

lemma exists_rootMerge_eq {k l : ℕ} {m₁ : VMono G k} {ch : Fin k → STree (VMono G)} {j : Fin k}
    {m₂ : VMono G l} {c₂ : Fin l → STree (VMono G)} (hj : ch j = .node m₂ c₂)
    (ht : (STree.node m₁ ch).IsShuffle) :
    ∃ M : VMono G (k + l - 1),
      M.1 = mergedMono m₁.1 j m₂.1 (mergeN_eq m₁ l) (sortP (planar ch j c₂ (mergeN_eq m₁ l)))
      ∧ rootMerge m₁ ch j m₂ c₂ = STree.node M
          (planar ch j c₂ (mergeN_eq m₁ l) ∘ sortP (planar ch j c₂ (mergeN_eq m₁ l))) :=
  ⟨_, rfl, rootMerge_eq hj ht⟩

lemma val_corolla {k l N : ℕ} {Y Y₁ Y₂ : Finset ℕ} (ch : Fin k → STree (VMono G)) (j : Fin k)
    (c₂ : Fin l → STree (VMono G)) (hN : N + 1 = k + l) (θ₁ : Fin k ≃ Lab Y₁)
    (θ₂ : Fin l ≃ Lab Y₂) (θ : Fin N ≃ Lab Y) (hθ₁ : ∀ a, a ≠ j → ch a = .leaf (θ₁ a).1)
    (hθ₂ : ∀ i, c₂ i = .leaf (θ₂ i).1) (π : Equiv.Perm (Fin N))
    (hθ : ∀ x, planar ch j c₂ hN (π x) = .leaf (θ x).1) (x : Fin N) :
    (θ x).1 = FreeGrL.sval (compEquiv θ₁ θ₂ j ((posEquivF j l N hN).symm (π x))) := by
  have h1 := hθ x
  rw [← Equiv.apply_symm_apply (posEquivF j l N hN) (π x)] at h1
  generalize (posEquivF j l N hN).symm (π x) = y at h1 ⊢
  rcases y with a | i
  · rw [planar_inl, hθ₁ a.1 a.2] at h1
    exact (STree.leaf.inj h1).symm
  · rw [planar_inr, hθ₂ i] at h1
    exact (STree.leaf.inj h1).symm

/-- **The root merge of two corollas.** -/
theorem rm_base {k l : ℕ} (m₁ : VMono G k) (ch : Fin k → STree (VMono G)) (j : Fin k)
    (m₂ : VMono G l) (c₂ : Fin l → STree (VMono G)) (hj : ch j = .node m₂ c₂)
    (ht : (STree.node m₁ ch).IsShuffle) (hl₁ : ∀ a, a ≠ j → (ch a).weight = 0)
    (hl₂ : ∀ i, (c₂ i).weight = 0) : RMProp c hc m₁ ch j m₂ c₂ := by
  intro Y Y₁ Y₂ m s T₁ T₂ R _ hT₁ hT₂ hR h₁ h₂ h
  subst hT₁ hT₂ hR
  have hall₁ : ∀ a, ∃ x, update ch j (.leaf m) a = .leaf x := fun a => by
    by_cases ha : a = j
    · subst ha
      exact ⟨m, update_self _ _ _⟩
    · rw [update_of_ne ha]
      exact exists_leaf_of_weight_eq_zero (hl₁ a ha)
  have hcor₁ := FreeGrL.exists_shEv_corolla (genBasis c hc) m₁ (update ch j (.leaf m)) Y₁ h₁ hall₁
  obtain ⟨θ₁, hθ₁, hev₁⟩ := hcor₁
  have hall₂ : ∀ i, ∃ a, c₂ i = .leaf a := fun i => exists_leaf_of_weight_eq_zero (hl₂ i)
  have hcor₂ := FreeGrL.exists_shEv_corolla (genBasis c hc) m₂ c₂ Y₂ h₂ hall₂
  obtain ⟨θ₂, hθ₂, hev₂⟩ := hcor₂
  have hQw : ∀ r, (planar ch j c₂ (mergeN_eq m₁ l) r).weight = 0 := fun r => by
    obtain ⟨y, rfl⟩ := (posEquivF j l _ (mergeN_eq m₁ l)).surjective r
    rcases y with a | i
    · rw [planar_inl]
      exact hl₁ a.1 a.2
    · rw [planar_inr]
      exact hl₂ i
  have hRM := exists_rootMerge_eq hj ht
  obtain ⟨M, hM, hRMC⟩ := hRM
  have hCex : ∃ C, C = planar ch j c₂ (mergeN_eq m₁ l)
      ∘ sortP (planar ch j c₂ (mergeN_eq m₁ l)) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ := hCex
  rw [← hC] at hRMC
  have hallC : ∀ r, ∃ x, C r = .leaf x := fun r => by
    rw [hC]
    exact exists_leaf_of_weight_eq_zero (hQw _)
  have h' : (STree.node M C).labels = Y.val := hRMC ▸ h
  have hcor := FreeGrL.exists_shEv_corolla (genBasis c hc) M C Y h' hallC
  obtain ⟨θ, hθ, hev⟩ := hcor
  have hco : rmCoeff K m₁ ch j c₂ = 1 := by
    unfold rmCoeff
    have hw : (STree.node m₁ (update ch j (.leaf 0))).weight = 1 := by
      rw [weight_node]
      have : ∑ a, (update ch j (STree.leaf 0) a).weight = 0 := Finset.sum_eq_zero fun a _ => by
        by_cases ha : a = j
        · subst ha
          rw [update_self]
          rfl
        · rw [update_of_ne ha]
          exact hl₁ a ha
      rw [this]
    have hkz : kz K (fun r => preKeys (planar ch j c₂ (mergeN_eq m₁ l) r))
        (sortP (planar ch j c₂ (mergeN_eq m₁ l))) = 1 :=
      kz_eq_one_of_nil K (fun r => preKeys_of_weight_eq_zero (hQw r)) _
    rw [hw, hkz]
    simp
  have hq : θ₁ j = ⟨m, s.mem⟩ :=
    Subtype.ext (STree.leaf.inj ((update_self j (STree.leaf m) ch).symm.trans (hθ₁ j))).symm
  have hval := val_corolla ch j c₂ (mergeN_eq m₁ l) θ₁ θ₂ θ
    (fun a ha => (update_of_ne ha _ _).symm.trans (hθ₁ a)) hθ₂ _
    (fun x => (congrFun hC x).symm.trans (hθ x))
  have key := mc_corolla_aux c hc m₁ m₂ θ₁ θ₂ j _ hq (mergeN_eq m₁ l) _ M hM θ _
    (FreeGrL.sval_labSplit s.mem s.iff s.disj) hval
  have e1 := (shEv_congr c hc hRMC Y h h').trans hev
  exact (congrArg₂ (fun X Z => mcL (I := Ibar K E c hc) s X Z) hev₁ hev₂).trans
    (key.trans ((one_smul K _).symm.trans (congrArg₂ (· • ·) hco.symm e1.symm)))

/-- **Peeling a child of the vertex off the root merge.** -/
theorem rm_stepA {k l : ℕ} (m₁ : VMono G k) (ch : Fin k → STree (VMono G)) (j : Fin k)
    (m₂ : VMono G l) (c₂ : Fin l → STree (VMono G)) (hj : ch j = .node m₂ c₂)
    (ht : (STree.node m₁ ch).IsShuffle) (hnd : (STree.node m₁ ch).labels.Nodup) (i₀ : Fin k)
    (hi₀ : i₀ ≠ j) (hlt : i₀ < j) (hafter : ∀ a, i₀ < a → a ≠ j → (ch a).weight = 0)
    (y : STree (VMono G)) (hy : ch i₀ = y) (m' : ℕ) (hm' : y.first = m')
    (ih : RMProp c hc m₁ (update ch i₀ (.leaf m')) j m₂ c₂) : RMProp c hc m₁ ch j m₂ c₂ := by
  intro Y Y₁ Y₂ m s T₁ T₂ R hm hT₁ hT₂ hR h₁ h₂ h
  subst hT₁ hT₂ hR
  have hch'j : update ch i₀ (STree.leaf m') j = ch j := update_of_ne hi₀.symm _ _
  have hj' : update ch i₀ (STree.leaf m') j = .node m₂ c₂ := hch'j.trans hj
  have hyS : y.IsShuffle := hy ▸ ht.child i₀
  have hm'y : m' ∈ y.labels := hm' ▸ first_mem hyS
  have hm'i : m' ∈ (ch i₀).labels := hy ▸ hm'y
  have hmj : m ∈ (ch j).labels := by
    rw [hm, hj]
    exact first_mem (hj ▸ ht.child j)
  have hmm' : m ≠ m' := fun e => not_mem_of_node hnd hi₀ hm'i (e ▸ hmj)
  have ht' : (STree.node m₁ (update ch i₀ (.leaf m'))).IsShuffle :=
    isShuffle_update_child ht i₀ (isShuffle_leaf m') (by rw [first_leaf, hy, hm'])
  have hnd' : (STree.node m₁ (update ch i₀ (.leaf m'))).labels.Nodup :=
    Multiset.nodup_of_le (labels_update_leaf_le m₁ ch i₀ hm'i) hnd
  have hdm' : ∀ a, a ≠ i₀ → m' ∉ (ch a).labels := fun a ha => not_mem_of_node hnd (Ne.symm ha) hm'i
  have hdm : ∀ a, a ≠ j → m ∉ (ch a).labels := fun a ha => not_mem_of_node hnd (Ne.symm ha) hmj
  -- the cut trees
  have hC₁ : update (update (update ch i₀ (.leaf m')) j (.leaf m)) i₀ (.leaf m')
      = update (update ch i₀ (.leaf m')) j (.leaf m) := by
    funext a
    by_cases ha : a = i₀
    · subst ha
      rw [update_self, update_of_ne hi₀, update_self]
    · rw [update_of_ne ha]
  have hC₂ : update (update (update ch i₀ (.leaf m')) j (.leaf m)) i₀ y
      = update ch j (.leaf m) := by
    funext a
    by_cases ha : a = i₀
    · subst ha
      rw [update_self, update_of_ne hi₀, hy]
    · rw [update_of_ne ha]
      by_cases haj : a = j
      · subst haj
        rw [update_self, update_self]
      · rw [update_of_ne haj, update_of_ne haj, update_of_ne ha]
  have hd1 : ∀ a, a ≠ i₀ → m' ∉ (update (update ch i₀ (.leaf m')) j (.leaf m) a).labels := by
    intro a ha
    by_cases haj : a = j
    · subst haj
      rw [update_self, labels_leaf, Multiset.mem_singleton]
      exact Ne.symm hmm'
    · rw [update_of_ne haj, update_of_ne ha]
      exact hdm' a ha
  have E1 : (STree.node m₁ (update (update ch i₀ (.leaf m')) j (.leaf m))).subst
      (update STree.leaf m' y) = STree.node m₁ (update ch j (.leaf m)) := by
    have := subst_update_child m₁ (update (update ch i₀ (.leaf m')) j (.leaf m)) i₀ m' y hd1
    rwa [hC₁, hC₂] at this
  have hd3 : ∀ a, a ≠ j → m ∉ (update ch i₀ (.leaf m') a).labels := fun a ha => by
    by_cases hai : a = i₀
    · subst hai
      rw [update_self, labels_leaf, Multiset.mem_singleton]
      exact hmm'
    · rw [update_of_ne hai]
      exact hdm a ha
  have E3 : (STree.node m₁ (update (update ch i₀ (.leaf m')) j (.leaf m))).subst
      (update STree.leaf m (.node m₂ c₂)) = STree.node m₁ (update ch i₀ (.leaf m')) := by
    have := subst_update_child m₁ (update ch i₀ (.leaf m')) j m (.node m₂ c₂) hd3
    have e : update (update ch i₀ (STree.leaf m')) j (STree.node m₂ c₂)
        = update ch i₀ (STree.leaf m') := by
      rw [← hj', update_eq_self]
    rwa [e] at this
  -- substituting back into the merged vertex
  have hQ := planar_update_left ch j c₂ (mergeN_eq m₁ l) i₀ hi₀ (.leaf m')
  have hyQ : planar ch j c₂ (mergeN_eq m₁ l)
      (posEquivF j l _ (mergeN_eq m₁ l) (Sum.inl ⟨i₀, hi₀⟩)) = y :=
    (planar_inl ch j c₂ (mergeN_eq m₁ l) ⟨i₀, hi₀⟩).trans hy
  have hdQ : ∀ r, r ≠ posEquivF j l _ (mergeN_eq m₁ l) (Sum.inl ⟨i₀, hi₀⟩) →
      m' ∉ (planar ch j c₂ (mergeN_eq m₁ l) r).labels := by
    intro r hr
    obtain ⟨x, rfl⟩ := (posEquivF j l _ (mergeN_eq m₁ l)).surjective r
    rcases x with a | i
    · rw [planar_inl]
      exact hdm' a.1 fun e => hr (by rw [show a = ⟨i₀, hi₀⟩ from Subtype.ext e])
    · rw [planar_inr]
      intro hmc
      exact hdm' j hi₀.symm (by rw [hj]; exact mem_labels_node.2 ⟨i, hmc⟩)
  have E2 : (rootMerge m₁ (update ch i₀ (.leaf m')) j m₂ c₂).subst (update STree.leaf m' y)
      = rootMerge m₁ ch j m₂ c₂ := rootMerge_subst hj hj' ht ht' _ hQ hyQ hm' hdQ
  -- the leaves
  have hlR' : (rootMerge m₁ (update ch i₀ (.leaf m')) j m₂ c₂).labels
      = (STree.node m₁ (update ch i₀ (.leaf m'))).labels := labels_rootMerge hj' ht'
  have hnd₁' : (STree.node m₁ (update (update ch i₀ (.leaf m')) j (.leaf m))).labels.Nodup :=
    Multiset.nodup_of_le (labels_update_leaf_le m₁ _ j (hch'j ▸ hmj)) hnd'
  have hndR' : (rootMerge m₁ (update ch i₀ (.leaf m')) j m₂ c₂).labels.Nodup := hlR' ▸ hnd'
  have hndy : y.labels.Nodup := hy ▸ nodup_of_node hnd i₀
  have hm'₁ : m' ∈ (STree.node m₁ (update (update ch i₀ (.leaf m')) j (.leaf m))).labels :=
    mem_labels_node.2 ⟨i₀, by
      rw [update_of_ne hi₀, update_self]
      exact Multiset.mem_singleton_self _⟩
  have hm₁ : m ∈ (STree.node m₁ (update (update ch i₀ (.leaf m')) j (.leaf m))).labels :=
    mem_labels_node.2 ⟨j, by
      rw [update_self]
      exact Multiset.mem_singleton_self _⟩
  have hm'R : m' ∈ (rootMerge m₁ (update ch i₀ (.leaf m')) j m₂ c₂).labels := by
    rw [hlR']
    exact mem_labels_node.2 ⟨i₀, by
      rw [update_self]
      exact Multiset.mem_singleton_self _⟩
  have hY₁' := FreeGrL.labels_eq_toFinset hnd₁'
  have hYy := FreeGrL.labels_eq_toFinset hndy
  have hY₁₂ := FreeGrL.labels_eq_toFinset hndR'
  have s₁ : LabSplit Y₁
      (STree.node m₁ (update (update ch i₀ (.leaf m')) j (.leaf m))).labels.toFinset
      y.labels.toFinset m' := LabSplit.of_val (Multiset.mem_toFinset.2 hm'₁) (by
    rw [← h₁, ← hY₁', ← hYy, ← E1]
    exact labels_subst_update_add _ y hm'₁ hnd₁')
  have s₃ : LabSplit (rootMerge m₁ (update ch i₀ (.leaf m')) j m₂ c₂).labels.toFinset
      (STree.node m₁ (update (update ch i₀ (.leaf m')) j (.leaf m))).labels.toFinset Y₂ m :=
    LabSplit.of_val (Multiset.mem_toFinset.2 hm₁) (by
      rw [← hY₁₂, ← hY₁', ← h₂, hlR', ← E3]
      exact labels_subst_update_add _ _ hm₁ hnd₁')
  have s₄ : LabSplit Y (rootMerge m₁ (update ch i₀ (.leaf m')) j m₂ c₂).labels.toFinset
      y.labels.toFinset m' := LabSplit.of_val (Multiset.mem_toFinset.2 hm'R) (by
    rw [← h, ← hY₁₂, ← hYy, ← E2]
    exact labels_subst_update_add _ y hm'R hndR')
  -- the sign of cutting off `y`
  have hσ1 : σ K (vpar (fun _ _ => true) y && vaft (fun _ _ => true)
      (STree.node m₁ (update (update ch i₀ (.leaf m')) j (.leaf m))) m') = 1 := by
    rw [σ_and_vaft_node_of_leaf K _ m₁ _ i₀ m' (by rw [update_of_ne hi₀, update_self]) hd1]
    refine Finset.prod_eq_one fun a _ => ?_
    split_ifs with ha
    · have hw : (update (update ch i₀ (STree.leaf m')) j (STree.leaf m) a).weight = 0 := by
        by_cases haj : a = j
        · subst haj
          rw [update_self]
          rfl
        · rw [update_of_ne haj, update_of_ne (ne_of_gt ha)]
          exact hafter a ha haj
      rw [vpar_true_of_weight_eq_zero hw, Bool.and_false, σ_false]
    · rfl
  -- the computation
  have hev₁ := ((compL_shEv (genBasis c hc) (par_genBasis c hc) s₁ _ y hY₁' hYy
    (by rw [E1]; exact h₁)).trans ((congrArg (· • _) hσ1).trans ((one_smul K _).trans
      (shEv_congr c hc E1 Y₁ _ h₁)))).symm
  have hpar := mcL_compL_par hmm' s₁ s s₃ s₄
    (FreeGrL.shEv (genBasis c hc) _ _ hY₁')
    (FreeGrL.par_shEv (genBasis c hc) (par_genBasis c hc) y _ hYy)
    (FreeGrL.par_shEv (genBasis c hc) (par_genBasis c hc) _ Y₂ h₂)
  have hih := ih _ _ _ _ s₃ _ (STree.node m₂ c₂) _ hm rfl rfl rfl hY₁' h₂ hY₁₂
  have hcomp := compL_shEv (genBasis c hc) (par_genBasis c hc) s₄ _ y hY₁₂ hYy
    (by rw [E2]; exact h)
  have hRR := shEv_congr c hc E2 Y (by rw [E2]; exact h) h
  have hcoef : σ K (vpar (fun _ _ => true) y && vpar (fun _ _ => true) (STree.node m₂ c₂))
      * (rmCoeff K m₁ (update ch i₀ (.leaf m')) j c₂ * σ K (vpar (fun _ _ => true) y
        && vaft (fun _ _ => true) (rootMerge m₁ (update ch i₀ (.leaf m')) j m₂ c₂) m'))
      = rmCoeff K m₁ ch j c₂ := by
    have hRM' := exists_rootMerge_eq hj' ht'
    obtain ⟨M', -, hR'eq⟩ := hRM'
    have hπ : sortP (planar (update ch i₀ (.leaf m')) j c₂ (mergeN_eq m₁ l))
        = sortP (planar ch j c₂ (mergeN_eq m₁ l)) := by
      rw [hQ]
      refine sortP_congr fun r => ?_
      by_cases hr : r = posEquivF j l _ (mergeN_eq m₁ l) (Sum.inl ⟨i₀, hi₀⟩)
      · rw [hr, update_self, first_leaf, hyQ, hm']
      · rw [update_of_ne hr]
    rw [hπ, hQ] at hR'eq
    rw [hR'eq]
    have hcv := kz_mul_σ_vaft K M' (planar ch j c₂ (mergeN_eq m₁ l))
      (posEquivF j l _ (mergeN_eq m₁ l) (Sum.inl ⟨i₀, hi₀⟩)) m' hdQ
      (sortP (planar ch j c₂ (mergeN_eq m₁ l)))
    rw [prod_after_left K ch j c₂ (mergeN_eq m₁ l) i₀ hi₀ hlt hafter, hyQ, hy] at hcv
    have hKz := kz_mul_self K (fun r => preKeys (planar ch j c₂ (mergeN_eq m₁ l) r))
      (sortP (planar ch j c₂ (mergeN_eq m₁ l)))
    have hKz' := kz_mul_self K (fun r => preKeys (update (planar ch j c₂ (mergeN_eq m₁ l))
      (posEquivF j l _ (mergeN_eq m₁ l) (Sum.inl ⟨i₀, hi₀⟩)) (.leaf m') r))
      (sortP (planar ch j c₂ (mergeN_eq m₁ l)))
    have hu := neg_one_pow_mul_self K (y.weight * ∑ i, (c₂ i).weight)
    have hσy : σ K (vpar (fun _ _ => true) y && vpar (fun _ _ => true) (STree.node m₂ c₂))
        = (-1) ^ y.weight * (-1) ^ (y.weight * ∑ i, (c₂ i).weight) := by
      rw [vpar_true, vpar_true, σ_bodd_and, weight_node, mul_add, mul_one, pow_add]
    have hw₁ := weight_update_child m₁ (update ch j (.leaf 0)) i₀ (.leaf m')
    rw [← update_comm hi₀ (STree.leaf m') (STree.leaf 0) ch, update_of_ne hi₀, hy,
      weight_leaf, add_zero] at hw₁
    have hpos : 1 ≤ (STree.node m₁ (update (update ch i₀ (.leaf m')) j (.leaf 0))).weight := by
      rw [weight_node]
      omega
    unfold rmCoeff
    rw [hπ, hQ, hσy, show (STree.node m₁ (update ch j (.leaf 0))).weight - 1
      = ((STree.node m₁ (update (update ch i₀ (.leaf m')) j (.leaf 0))).weight - 1) + y.weight
      by omega, pow_add]
    linear_combination ((-1 : K) ^ ((STree.node m₁ (update (update ch i₀ (.leaf m')) j
        (.leaf 0))).weight - 1) * kz K (fun r => preKeys (update (planar ch j c₂ (mergeN_eq m₁ l))
        (posEquivF j l _ (mergeN_eq m₁ l) (Sum.inl ⟨i₀, hi₀⟩)) (.leaf m') r))
        (sortP (planar ch j c₂ (mergeN_eq m₁ l))) * (-1) ^ y.weight
        * (-1) ^ (y.weight * ∑ i, (c₂ i).weight))
      * (kz K (fun r => preKeys (planar ch j c₂ (mergeN_eq m₁ l) r))
        (sortP (planar ch j c₂ (mergeN_eq m₁ l))) * hcv
        - σ K (vpar (fun _ _ => true) y && vaft (fun _ _ => true) (STree.node M'
          (update (planar ch j c₂ (mergeN_eq m₁ l))
            (posEquivF j l _ (mergeN_eq m₁ l) (Sum.inl ⟨i₀, hi₀⟩)) (.leaf m')
          ∘ sortP (planar ch j c₂ (mergeN_eq m₁ l)))) m') * hKz)
      + ((-1 : K) ^ ((STree.node m₁ (update (update ch i₀ (.leaf m')) j (.leaf 0))).weight - 1)
        * (-1) ^ y.weight * kz K (fun r => preKeys (planar ch j c₂ (mergeN_eq m₁ l) r))
          (sortP (planar ch j c₂ (mergeN_eq m₁ l)))
        * (-1) ^ (y.weight * ∑ i, (c₂ i).weight) * (-1) ^ (y.weight * ∑ i, (c₂ i).weight)) * hKz'
      + ((-1 : K) ^ ((STree.node m₁ (update (update ch i₀ (.leaf m')) j (.leaf 0))).weight - 1)
        * (-1) ^ y.weight * kz K (fun r => preKeys (planar ch j c₂ (mergeN_eq m₁ l) r))
          (sortP (planar ch j c₂ (mergeN_eq m₁ l)))) * hu
  have hmain := (congrArg (fun X => mcL (I := Ibar K E c hc) s X
    (FreeGrL.shEv (genBasis c hc) (STree.node m₂ c₂) Y₂ h₂)) hev₁).trans hpar
  have h3 := (congrArg (fun X => compL K s₄ X (FreeGrL.shEv (genBasis c hc) y _ hYy)) hih).trans
    ((LinearMap.map_smul₂ _ _ _ _).trans ((congrArg
      (fun X => rmCoeff K m₁ (update ch i₀ (.leaf m')) j c₂ • X) (hcomp.trans (congrArg
        (fun X => σ K (vpar (fun _ _ => true) y && vaft (fun _ _ => true)
          (rootMerge m₁ (update ch i₀ (.leaf m')) j m₂ c₂) m') • X) hRR))).trans
      (smul_smul _ _ _)))
  exact hmain.trans ((congrArg (fun X => σ K (vpar (fun _ _ => true) y
    && vpar (fun _ _ => true) (STree.node m₂ c₂)) • X) h3).trans ((smul_smul _ _ _).trans
      (congrArg (· • FreeGrL.shEv (genBasis c hc) (rootMerge m₁ ch j m₂ c₂) Y h) hcoef)))

/-- **Peeling a child of the merged child off the root merge.** -/
theorem rm_stepB {k l : ℕ} (m₁ : VMono G k) (ch : Fin k → STree (VMono G)) (j : Fin k)
    (m₂ : VMono G l) (c₂ : Fin l → STree (VMono G)) (hj : ch j = .node m₂ c₂)
    (ht : (STree.node m₁ ch).IsShuffle) (hnd : (STree.node m₁ ch).labels.Nodup)
    (hl₁ : ∀ a, a ≠ j → (ch a).weight = 0) (i₀ : Fin l)
    (hafter : ∀ i, i₀ < i → (c₂ i).weight = 0) (y : STree (VMono G)) (hy : c₂ i₀ = y) (m' : ℕ)
    (hm' : y.first = m')
    (ih : RMProp c hc m₁ (update ch j (.node m₂ (update c₂ i₀ (.leaf m')))) j m₂
      (update c₂ i₀ (.leaf m'))) : RMProp c hc m₁ ch j m₂ c₂ := by
  intro Y Y₁ Y₂ m s T₁ T₂ R hm hT₁ hT₂ hR h₁ h₂ h
  subst hT₁ hT₂ hR
  have ht₂ : (STree.node m₂ c₂).IsShuffle := hj ▸ ht.child j
  have hnd₂ : (STree.node m₂ c₂).labels.Nodup := hj ▸ nodup_of_node hnd j
  have hyS : y.IsShuffle := hy ▸ ht₂.child i₀
  have hm'y : m' ∈ y.labels := hm' ▸ first_mem hyS
  have hm'i : m' ∈ (c₂ i₀).labels := hy ▸ hm'y
  have hdm' : ∀ i, i ≠ i₀ → m' ∉ (c₂ i).labels := fun i hi =>
    not_mem_of_node hnd₂ (Ne.symm hi) hm'i
  have hfy : (STree.leaf m' : STree (VMono G)).first = (c₂ i₀).first := by
    rw [first_leaf, hy, hm']
  have hfirst : (STree.node m₂ (update c₂ i₀ (.leaf m'))).first = (STree.node m₂ c₂).first :=
    first_node_update_child m₂ c₂ i₀ _ hfy
  have ht₂' : (STree.node m₂ (update c₂ i₀ (.leaf m'))).IsShuffle :=
    isShuffle_update_child ht₂ i₀ (isShuffle_leaf m') hfy
  have hj' : update ch j (STree.node m₂ (update c₂ i₀ (.leaf m'))) j
      = .node m₂ (update c₂ i₀ (.leaf m')) := update_self _ _ _
  have ht' : (STree.node m₁ (update ch j (.node m₂ (update c₂ i₀ (.leaf m'))))).IsShuffle :=
    isShuffle_update_child ht j ht₂' (by rw [hfirst, hj])
  have hle₂ : (STree.node m₂ (update c₂ i₀ (.leaf m'))).labels ≤ (STree.node m₂ c₂).labels :=
    labels_update_leaf_le m₂ c₂ i₀ hm'i
  have hnd' : (STree.node m₁ (update ch j (.node m₂ (update c₂ i₀ (.leaf m'))))).labels.Nodup :=
    Multiset.nodup_of_le (labels_update_le m₁ ch j (by rw [hj]; exact hle₂)) hnd
  have hm₂ : m ∈ (STree.node m₂ c₂).labels := hm ▸ first_mem ht₂
  have hmj : m ∈ (ch j).labels := by
    rw [hj]
    exact hm₂
  have hdm : ∀ a, a ≠ j → m ∉ (ch a).labels := fun a ha => not_mem_of_node hnd (Ne.symm ha) hmj
  have hdmj : ∀ a, a ≠ j → m' ∉ (ch a).labels := fun a ha => not_mem_of_node hnd (Ne.symm ha)
    (by rw [hj]; exact mem_labels_node.2 ⟨i₀, hm'i⟩)
  have E1 : (STree.node m₂ (update c₂ i₀ (.leaf m'))).subst (update STree.leaf m' y)
      = STree.node m₂ c₂ := by
    have := subst_update_child m₂ c₂ i₀ m' y hdm'
    have e : update c₂ i₀ y = c₂ := by
      rw [← hy, update_eq_self]
    rwa [e] at this
  have E3 : (STree.node m₁ (update ch j (.leaf m))).subst
      (update STree.leaf m (.node m₂ (update c₂ i₀ (.leaf m'))))
      = STree.node m₁ (update ch j (.node m₂ (update c₂ i₀ (.leaf m')))) :=
    subst_update_child m₁ ch j m _ hdm
  have hQ : planar (update ch j (.node m₂ (update c₂ i₀ (.leaf m')))) j (update c₂ i₀ (.leaf m'))
      (mergeN_eq m₁ l) = update (planar ch j c₂ (mergeN_eq m₁ l))
        (posEquivF j l _ (mergeN_eq m₁ l) (Sum.inr i₀)) (.leaf m') := by
    rw [planar_update_self, planar_update_right]
  have hyQ : planar ch j c₂ (mergeN_eq m₁ l) (posEquivF j l _ (mergeN_eq m₁ l) (Sum.inr i₀)) = y :=
    (planar_inr ch j c₂ (mergeN_eq m₁ l) i₀).trans hy
  have hdQ : ∀ r, r ≠ posEquivF j l _ (mergeN_eq m₁ l) (Sum.inr i₀) →
      m' ∉ (planar ch j c₂ (mergeN_eq m₁ l) r).labels := by
    intro r hr
    obtain ⟨x, rfl⟩ := (posEquivF j l _ (mergeN_eq m₁ l)).surjective r
    rcases x with a | i
    · rw [planar_inl]
      exact hdmj a.1 a.2
    · rw [planar_inr]
      exact hdm' i fun e => hr (by rw [e])
  have E2 : (rootMerge m₁ (update ch j (.node m₂ (update c₂ i₀ (.leaf m')))) j m₂
      (update c₂ i₀ (.leaf m'))).subst (update STree.leaf m' y) = rootMerge m₁ ch j m₂ c₂ :=
    rootMerge_subst hj hj' ht ht' _ hQ hyQ hm' hdQ
  have hlR' : (rootMerge m₁ (update ch j (.node m₂ (update c₂ i₀ (.leaf m')))) j m₂
      (update c₂ i₀ (.leaf m'))).labels
      = (STree.node m₁ (update ch j (.node m₂ (update c₂ i₀ (.leaf m'))))).labels :=
    labels_rootMerge hj' ht'
  have hnd₂' : (STree.node m₂ (update c₂ i₀ (.leaf m'))).labels.Nodup :=
    Multiset.nodup_of_le hle₂ hnd₂
  have hndy : y.labels.Nodup := hy ▸ nodup_of_node hnd₂ i₀
  have hndR' : (rootMerge m₁ (update ch j (.node m₂ (update c₂ i₀ (.leaf m')))) j m₂
      (update c₂ i₀ (.leaf m'))).labels.Nodup := hlR' ▸ hnd'
  have hm'₂ : m' ∈ (STree.node m₂ (update c₂ i₀ (.leaf m'))).labels :=
    mem_labels_node.2 ⟨i₀, by
      rw [update_self]
      exact Multiset.mem_singleton_self _⟩
  have hnd₁ : (STree.node m₁ (update ch j (.leaf m))).labels.Nodup := by
    rw [h₁]
    exact Y₁.nodup
  have hm₁ : m ∈ (STree.node m₁ (update ch j (.leaf m))).labels :=
    mem_labels_node.2 ⟨j, by
      rw [update_self]
      exact Multiset.mem_singleton_self _⟩
  have hm'R : m' ∈ (rootMerge m₁ (update ch j (.node m₂ (update c₂ i₀ (.leaf m')))) j m₂
      (update c₂ i₀ (.leaf m'))).labels := by
    rw [hlR']
    exact mem_labels_node.2 ⟨j, by rw [hj']; exact hm'₂⟩
  have hY₂' := FreeGrL.labels_eq_toFinset hnd₂'
  have hYy := FreeGrL.labels_eq_toFinset hndy
  have hY₁₂ := FreeGrL.labels_eq_toFinset hndR'
  have s₁ : LabSplit Y₂ (STree.node m₂ (update c₂ i₀ (.leaf m'))).labels.toFinset
      y.labels.toFinset m' := LabSplit.of_val (Multiset.mem_toFinset.2 hm'₂) (by
    rw [← h₂, ← hY₂', ← hYy, ← E1]
    exact labels_subst_update_add _ y hm'₂ hnd₂')
  have s₃ : LabSplit (rootMerge m₁ (update ch j (.node m₂ (update c₂ i₀ (.leaf m')))) j m₂
      (update c₂ i₀ (.leaf m'))).labels.toFinset Y₁
      (STree.node m₂ (update c₂ i₀ (.leaf m'))).labels.toFinset m :=
    LabSplit.of_val s.mem (by
      rw [← hY₁₂, ← h₁, ← hY₂', hlR', ← E3]
      exact labels_subst_update_add _ _ hm₁ hnd₁)
  have s₄ : LabSplit Y (rootMerge m₁ (update ch j (.node m₂ (update c₂ i₀ (.leaf m')))) j m₂
      (update c₂ i₀ (.leaf m'))).labels.toFinset y.labels.toFinset m' :=
    LabSplit.of_val (Multiset.mem_toFinset.2 hm'R) (by
      rw [← h, ← hY₁₂, ← hYy, ← E2]
      exact labels_subst_update_add _ y hm'R hndR')
  have hσ1 : σ K (vpar (fun _ _ => true) y && vaft (fun _ _ => true)
      (STree.node m₂ (update c₂ i₀ (.leaf m'))) m') = 1 := by
    rw [σ_and_vaft_node_of_leaf K _ m₂ _ i₀ m' (update_self _ _ _) (fun i hi => by
      rw [update_of_ne hi]
      exact hdm' i hi)]
    refine Finset.prod_eq_one fun i _ => ?_
    split_ifs with hi
    · rw [update_of_ne (ne_of_gt hi), vpar_true_of_weight_eq_zero (hafter i hi), Bool.and_false,
        σ_false]
    · rfl
  have hev₂ := ((compL_shEv (genBasis c hc) (par_genBasis c hc) s₁ _ y hY₂' hYy
    (by rw [E1]; exact h₂)).trans ((congrArg (· • _) hσ1).trans ((one_smul K _).trans
      (shEv_congr c hc E1 Y₂ _ h₂)))).symm
  have houter := mcL_compL_outer s₁ s s₃ s₄
    (FreeGrL.shEv (genBasis c hc) (STree.node m₁ (update ch j (.leaf m))) Y₁ h₁)
    (unitCoeffL_shEv_node c hc m₂ _ _ hY₂') (FreeGrL.shEv (genBasis c hc) y _ hYy)
  have hih := ih _ _ _ _ s₃ (STree.node m₁ (update ch j (.leaf m))) _ _ (hm.trans hfirst.symm)
    (by rw [update_idem]) rfl rfl h₁ hY₂' hY₁₂
  have hcomp := compL_shEv (genBasis c hc) (par_genBasis c hc) s₄ _ y hY₁₂ hYy
    (by rw [E2]; exact h)
  have hRR := shEv_congr c hc E2 Y (by rw [E2]; exact h) h
  have hcoef : rmCoeff K m₁ (update ch j (.node m₂ (update c₂ i₀ (.leaf m')))) j
      (update c₂ i₀ (.leaf m')) * σ K (vpar (fun _ _ => true) y && vaft (fun _ _ => true)
        (rootMerge m₁ (update ch j (.node m₂ (update c₂ i₀ (.leaf m')))) j m₂
          (update c₂ i₀ (.leaf m'))) m') = rmCoeff K m₁ ch j c₂ := by
    have hRM' := exists_rootMerge_eq hj' ht'
    obtain ⟨M', -, hR'eq⟩ := hRM'
    have hπ : sortP (planar (update ch j (.node m₂ (update c₂ i₀ (.leaf m')))) j
        (update c₂ i₀ (.leaf m')) (mergeN_eq m₁ l)) = sortP (planar ch j c₂ (mergeN_eq m₁ l)) := by
      rw [hQ]
      refine sortP_congr fun r => ?_
      by_cases hr : r = posEquivF j l _ (mergeN_eq m₁ l) (Sum.inr i₀)
      · rw [hr, update_self, first_leaf, hyQ, hm']
      · rw [update_of_ne hr]
    rw [hπ, hQ] at hR'eq
    rw [hR'eq]
    have hcv := kz_mul_σ_vaft K M' (planar ch j c₂ (mergeN_eq m₁ l))
      (posEquivF j l _ (mergeN_eq m₁ l) (Sum.inr i₀)) m' hdQ
      (sortP (planar ch j c₂ (mergeN_eq m₁ l)))
    rw [prod_after_right K ch j c₂ (mergeN_eq m₁ l) i₀ hl₁ hafter, mul_one, hyQ] at hcv
    have hKz := kz_mul_self K (fun r => preKeys (planar ch j c₂ (mergeN_eq m₁ l) r))
      (sortP (planar ch j c₂ (mergeN_eq m₁ l)))
    have hKz' := kz_mul_self K (fun r => preKeys (update (planar ch j c₂ (mergeN_eq m₁ l))
      (posEquivF j l _ (mergeN_eq m₁ l) (Sum.inr i₀)) (.leaf m') r))
      (sortP (planar ch j c₂ (mergeN_eq m₁ l)))
    unfold rmCoeff
    rw [update_idem, hπ, hQ]
    linear_combination (-1 : K) ^ ((STree.node m₁ (update ch j (.leaf 0))).weight - 1)
      * (kz K (fun r => preKeys (update (planar ch j c₂ (mergeN_eq m₁ l))
          (posEquivF j l _ (mergeN_eq m₁ l) (Sum.inr i₀)) (.leaf m') r))
          (sortP (planar ch j c₂ (mergeN_eq m₁ l)))
        * (kz K (fun r => preKeys (planar ch j c₂ (mergeN_eq m₁ l) r))
          (sortP (planar ch j c₂ (mergeN_eq m₁ l))) * hcv
          - σ K (vpar (fun _ _ => true) y && vaft (fun _ _ => true) (STree.node M'
            (update (planar ch j c₂ (mergeN_eq m₁ l))
              (posEquivF j l _ (mergeN_eq m₁ l) (Sum.inr i₀)) (.leaf m')
            ∘ sortP (planar ch j c₂ (mergeN_eq m₁ l)))) m') * hKz)
        + kz K (fun r => preKeys (planar ch j c₂ (mergeN_eq m₁ l) r))
          (sortP (planar ch j c₂ (mergeN_eq m₁ l))) * hKz')
  have hmain := (congrArg (fun X => mcL (I := Ibar K E c hc) s
    (FreeGrL.shEv (genBasis c hc) (STree.node m₁ (update ch j (.leaf m))) Y₁ h₁) X) hev₂).trans
    houter
  have h3 := (congrArg (fun X => compL K s₄ X (FreeGrL.shEv (genBasis c hc) y _ hYy)) hih).trans
    ((LinearMap.map_smul₂ _ _ _ _).trans ((congrArg
      (fun X => rmCoeff K m₁ (update ch j (.node m₂ (update c₂ i₀ (.leaf m')))) j
        (update c₂ i₀ (.leaf m')) • X) (hcomp.trans (congrArg
        (fun X => σ K (vpar (fun _ _ => true) y && vaft (fun _ _ => true)
          (rootMerge m₁ (update ch j (.node m₂ (update c₂ i₀ (.leaf m')))) j m₂
            (update c₂ i₀ (.leaf m'))) m') • X) hRR))).trans (smul_smul _ _ _)))
  exact hmain.trans (h3.trans
    (congrArg (· • FreeGrL.shEv (genBasis c hc) (rootMerge m₁ ch j m₂ c₂) Y h) hcoef))

/-- **Merging the root of a child into the vertex**, on the trees all of whose children after the
child `j` are leaves: by induction on the number of vertices, peeling off the last child of the
vertex that is not a leaf (`rm_stepA`), then the last child of the child (`rm_stepB`), down to two
corollas (`rm_base`). -/
theorem rmProp : ∀ (n : ℕ) {k l : ℕ} (m₁ : VMono G k) (ch : Fin k → STree (VMono G)) (j : Fin k)
    (m₂ : VMono G l) (c₂ : Fin l → STree (VMono G)), (STree.node m₁ ch).weight ≤ n →
    ch j = .node m₂ c₂ → (STree.node m₁ ch).IsShuffle → (STree.node m₁ ch).labels.Nodup →
    (∀ a, j < a → (ch a).weight = 0) → RMProp c hc m₁ ch j m₂ c₂
  | 0, _, _, _, _, _, _, _, hw, _, _, _, _ => by
    simp only [weight_node] at hw
    omega
  | n + 1, k, l, m₁, ch, j, m₂, c₂, hw, hj, ht, hnd, hlast => by
    by_cases hA : ∃ a, a ≠ j ∧ (ch a).weight ≠ 0
    · have hS : (Finset.univ.filter fun a => a ≠ j ∧ (ch a).weight ≠ 0).Nonempty := by
        obtain ⟨a, ha⟩ := hA
        exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩⟩
      have hex : ∃ i₀ : Fin k, (i₀ ≠ j ∧ (ch i₀).weight ≠ 0)
          ∧ ∀ a, a ≠ j → (ch a).weight ≠ 0 → a ≤ i₀ :=
        ⟨_, (Finset.mem_filter.1 (Finset.max'_mem _ hS)).2, fun a ha hw' =>
          Finset.le_max' _ a (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha, hw'⟩)⟩
      obtain ⟨i₀, ⟨hi₀, hy0⟩, hle⟩ := hex
      have hafter : ∀ a, i₀ < a → a ≠ j → (ch a).weight = 0 := fun a ha haj => by
        by_contra hne
        exact absurd (hle a haj hne) (not_le.2 ha)
      have hlt : i₀ < j := by
        rcases lt_or_gt_of_ne hi₀ with h | h
        · exact h
        · exact absurd (hlast i₀ h) hy0
      refine rm_stepA c hc m₁ ch j m₂ c₂ hj ht hnd i₀ hi₀ hlt hafter (ch i₀) rfl _ rfl ?_
      have hw' := weight_update_child m₁ ch i₀ (.leaf (ch i₀).first)
      rw [weight_leaf, add_zero] at hw'
      exact rmProp n m₁ _ j m₂ c₂ (by omega) ((update_of_ne hi₀.symm _ _).trans hj)
        (isShuffle_update_child ht i₀ (isShuffle_leaf _) rfl)
        (Multiset.nodup_of_le (labels_update_leaf_le m₁ ch i₀ (first_mem (ht.child i₀))) hnd)
        (fun a ha => by
          rw [update_of_ne (ne_of_gt (lt_trans hlt ha))]
          exact hlast a ha)
    · push Not at hA
      by_cases hB : ∃ i, (c₂ i).weight ≠ 0
      · have hS : (Finset.univ.filter fun i => (c₂ i).weight ≠ 0).Nonempty := by
          obtain ⟨i, hi⟩ := hB
          exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
        have hex : ∃ i₀ : Fin l, (c₂ i₀).weight ≠ 0 ∧ ∀ i, (c₂ i).weight ≠ 0 → i ≤ i₀ :=
          ⟨(Finset.univ.filter fun i => (c₂ i).weight ≠ 0).max' hS,
            (Finset.mem_filter.1 (Finset.max'_mem _ hS)).2, fun i hi =>
            Finset.le_max' _ i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)⟩
        obtain ⟨i₀, hy0, hle⟩ := hex
        have hafter : ∀ i, i₀ < i → (c₂ i).weight = 0 := fun i hi => by
          by_contra hne
          exact absurd (hle i hne) (not_le.2 hi)
        refine rm_stepB c hc m₁ ch j m₂ c₂ hj ht hnd hA i₀ hafter (c₂ i₀) rfl _ rfl ?_
        have ht₂ : (STree.node m₂ c₂).IsShuffle := hj ▸ ht.child j
        have hw₂ := weight_update_child m₂ c₂ i₀ (.leaf (c₂ i₀).first)
        have hw₁ := weight_update_child m₁ ch j (.node m₂ (update c₂ i₀ (.leaf (c₂ i₀).first)))
        rw [weight_leaf, add_zero] at hw₂
        rw [hj] at hw₁
        exact rmProp n m₁ _ j m₂ _ (by omega) (update_self _ _ _)
          (isShuffle_update_child ht j (isShuffle_update_child ht₂ i₀ (isShuffle_leaf _) rfl)
            (by rw [first_node_update_child m₂ c₂ i₀ (.leaf (c₂ i₀).first) rfl, hj]))
          (Multiset.nodup_of_le (labels_update_le m₁ ch j (by
            rw [hj]
            exact labels_update_leaf_le m₂ c₂ i₀ (first_mem (ht₂.child i₀)))) hnd)
          (fun a ha => by
            rw [update_of_ne (ne_of_gt ha)]
            exact hlast a ha)
      · push Not at hB
        exact rm_base c hc m₁ ch j m₂ c₂ hj ht hA hB

end RootMergeProof

end ShuffleBarSym

namespace ShuffleBarSym

/-! ## Lists -/

lemma sum_mapIdx_congr {α M : Type*} [AddCommMonoid M] :
    ∀ (l : List α) {f g : ℕ → α → M}, (∀ i a, a ∈ l → f i a = g i a) →
      (l.mapIdx f).sum = (l.mapIdx g).sum
  | [], _, _, _ => rfl
  | a :: l, f, g, h => by
    rw [List.mapIdx_cons, List.mapIdx_cons, List.sum_cons, List.sum_cons,
      h 0 a List.mem_cons_self,
      sum_mapIdx_congr l fun i b hb => h (i + 1) b (List.mem_cons_of_mem a hb)]

lemma map_sum_mapIdx {α M N : Type*} [AddCommMonoid M] [AddCommMonoid N] (F : M →+ N) :
    ∀ (l : List α) (f : ℕ → α → M), F (l.mapIdx f).sum = (l.mapIdx fun i a => F (f i a)).sum
  | [], _ => map_zero F
  | a :: l, f => by
    rw [List.mapIdx_cons, List.mapIdx_cons, List.sum_cons, List.sum_cons, map_add,
      map_sum_mapIdx F l]

lemma sum_mapIdx_append_cons {α M : Type*} [AddCommMonoid M] (A B : List α) (x : α)
    (f : ℕ → α → M) :
    ((A ++ x :: B).mapIdx f).sum
      = (A.mapIdx f).sum + f A.length x + (B.mapIdx fun i a => f (i + A.length + 1) a).sum := by
  simp only [List.mapIdx_append, List.mapIdx_cons, List.sum_append, List.sum_cons, Nat.zero_add,
    add_assoc]
  rw [Nat.add_comm 1 A.length]

/-- **A sum over a list without repetitions, weighted by positions**, as a sum over its entries. -/
lemma sum_mapIdx_eq_sum_toFinset {α M : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    [AddCommMonoid M] :
    ∀ (l : List α), l.Nodup → ∀ f : ℕ → α → M,
      (l.mapIdx f).sum = ∑ a ∈ l.toFinset, f (l.idxOf a) a
  | [], _, _ => rfl
  | a :: l, hl, f => by
    have ha := (List.nodup_cons.1 hl).1
    rw [List.mapIdx_cons, List.sum_cons, sum_mapIdx_eq_sum_toFinset l (List.nodup_cons.1 hl).2,
      List.toFinset_cons, Finset.sum_insert (by simpa using ha), List.idxOf_cons_self]
    congr 1
    refine Finset.sum_congr rfl fun b hb => ?_
    have hba : b ≠ a := fun e => ha (e ▸ List.mem_toFinset.1 hb)
    rw [List.idxOf_cons_ne _ (Ne.symm hba)]

/-! ## Keys of a tree cut at a child -/

section CutKeys

variable {B : ℕ → Type*}

lemma flatten_drop_ofFn_eq_nil {k : ℕ} (ch : Fin k → STree B) (j : Fin k)
    (hlast : ∀ a, j < a → (ch a).weight = 0) :
    ((List.ofFn fun a => preKeys (ch a)).drop (j + 1)).flatten = [] := by
  rw [List.flatten_eq_nil_iff]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [List.getElem_drop, List.getElem_ofFn]
  simp only [List.length_drop, List.length_ofFn] at hi
  exact preKeys_of_weight_eq_zero (hlast _ (show (j : ℕ) < j + 1 + i by omega))

/-- **The keys of a tree whose children after `j` are leaves**: those of the tree cut at `j`,
then those of the child `j`. -/
lemma tail_preKeys_cut {k : ℕ} (β : B k) (ch : Fin k → STree B) (j : Fin k)
    (hlast : ∀ a, j < a → (ch a).weight = 0) (m : ℕ) :
    (preKeys (STree.node β ch)).tail
      = (preKeys (STree.node β (update ch j (.leaf m)))).tail ++ preKeys (ch j) := by
  rw [preKeys_node, preKeys_node, List.tail_cons, List.tail_cons, flatten_ofFn_split _ j,
    flatten_ofFn_split _ j, take_ofFn_update preKeys ch j (.leaf m),
    drop_ofFn_update preKeys ch j (.leaf m), flatten_drop_ofFn_eq_nil ch j hlast, update_self]
  simp [preKeys]

end CutKeys

/-! ## Merging an edge of a tree cut at a child -/

section CutMerge

variable {G : Type} [Fintype G] [DecidableEq G]

lemma kzAt_of_mem_tail_child (K : Type u) [CommRing K] {k : ℕ} {m : VMono G k}
    {ch : Fin k → STree (VMono G)} (ht : (STree.node m ch).IsShuffle)
    (hnd : (STree.node m ch).labels.Nodup) {a : Fin k} {κ : ℕ ×ₗ ℕ}
    (hκ : κ ∈ (preKeys (ch a)).tail) : kzAt K (STree.node m ch) κ = kzAt K (ch a) κ := by
  have hno : ¬∃ j, vkey (ch j) = κ ∧ (ch j).weight ≠ 0 := by
    rintro ⟨j, rfl, hw'⟩
    by_cases hjj : j = a
    · subst hjj
      have hnd' := nodup_preKeys_child ht hnd j
      rw [preKeys_eq_cons hw'] at hnd'
      exact (List.nodup_cons.1 hnd').1 hκ
    · exact not_mem_preKeys_of_ne ht hnd (Ne.symm hjj) (List.mem_of_mem_tail hκ)
        (by rw [preKeys_eq_cons hw']; exact List.mem_cons_self ..)
  rw [kzAt, dif_neg hno, Fintype.prod_eq_single a fun j hj =>
    kzAt_of_not_mem K (not_mem_preKeys_of_ne ht hnd (Ne.symm hj) (List.mem_of_mem_tail hκ))]

/-- The keys of a tree cut at a child `j`: the keys of the other children. -/
lemma exists_mem_preKeys_of_cut {k : ℕ} {m₁ : VMono G k} {ch : Fin k → STree (VMono G)}
    {j : Fin k} {m : ℕ} {κ : ℕ ×ₗ ℕ}
    (hκ : κ ∈ (preKeys (STree.node m₁ (update ch j (.leaf m)))).tail) :
    ∃ a, a ≠ j ∧ κ ∈ preKeys (ch a) := by
  rw [preKeys_node, List.tail_cons, mem_flatten_ofFn] at hκ
  obtain ⟨a, ha⟩ := hκ
  have haj : a ≠ j := fun e => by
    subst e
    rw [update_self] at ha
    simp [preKeys] at ha
  rw [update_of_ne haj] at ha
  exact ⟨a, haj, ha⟩

lemma exists_node_of_weight_ne_zero {t : STree (VMono G)} (hw : t.weight ≠ 0) :
    ∃ (l : ℕ) (m₂ : VMono G l) (c₂ : Fin l → STree (VMono G)), t = .node m₂ c₂ := by
  cases t with
  | leaf => simp at hw
  | node m₂ c₂ => exact ⟨_, m₂, c₂, rfl⟩

/-- **Merging an edge of a tree cut at a child, then substituting the child back**, merges the
edge of the tree. -/
theorem mergeT_cut_subst {k : ℕ} (m₁ : VMono G k) (ch : Fin k → STree (VMono G)) (j : Fin k)
    (ht : (STree.node m₁ ch).IsShuffle) (hnd : (STree.node m₁ ch).labels.Nodup) (m : ℕ)
    (hm : (ch j).first = m) {κ : ℕ ×ₗ ℕ}
    (hκ : κ ∈ (preKeys (STree.node m₁ (update ch j (.leaf m)))).tail) :
    (mergeT (STree.node m₁ (update ch j (.leaf m))) κ).subst (update STree.leaf m (ch j))
      = mergeT (STree.node m₁ ch) κ := by
  have hmj : m ∈ (ch j).labels := hm ▸ first_mem (ht.child j)
  have ht₁ : (STree.node m₁ (update ch j (.leaf m))).IsShuffle :=
    isShuffle_update_child ht j (isShuffle_leaf m) (by rw [first_leaf, hm])
  have hnd₁ : (STree.node m₁ (update ch j (.leaf m))).labels.Nodup :=
    Multiset.nodup_of_le (labels_update_leaf_le m₁ ch j hmj) hnd
  have hdm : ∀ a, a ≠ j → m ∉ (ch a).labels := fun a ha => not_mem_of_node hnd (Ne.symm ha) hmj
  have hex := exists_mem_preKeys_of_cut hκ
  obtain ⟨a, haj, ha⟩ := hex
  have hw := weight_ne_zero_of_mem ha
  rw [preKeys_eq_cons hw, List.mem_cons] at ha
  rcases ha with rfl | ha
  · have hn := exists_node_of_weight_ne_zero hw
    obtain ⟨l, m₂, c₂, hc⟩ := hn
    have hc₁ : update ch j (.leaf m) a = .node m₂ c₂ := (update_of_ne haj _ _).trans hc
    have e1 := mergeT_root ht₁ hc₁
    rw [update_of_ne haj] at e1
    rw [e1, mergeT_root ht hc]
    refine rootMerge_subst hc hc₁ ht ht₁ (posEquivF a l _ (mergeN_eq m₁ l) (Sum.inl ⟨j, haj.symm⟩))
      (planar_update_left ch a c₂ _ j haj.symm _) (planar_inl ch a c₂ _ _) hm fun r hr => ?_
    obtain ⟨x, rfl⟩ := (posEquivF a l _ (mergeN_eq m₁ l)).surjective r
    rcases x with b | i
    · rw [planar_inl]
      exact hdm b.1 fun e => hr (by rw [show b = ⟨j, haj.symm⟩ from Subtype.ext e])
    · rw [planar_inr]
      intro hmc
      exact hdm a haj (by rw [hc]; exact mem_labels_node.2 ⟨i, hmc⟩)
  · have ha₁ : κ ∈ (preKeys (update ch j (.leaf m) a)).tail := by
      rw [update_of_ne haj]
      exact ha
    rw [mergeT_child ht₁ hnd₁ ha₁, mergeT_child ht hnd ha, update_of_ne haj,
      update_comm (Ne.symm haj)]
    have hX := (mergeT_spec (ch a) κ (ht.child a) (nodup_of_node hnd a) ha).2.1
    rw [subst_update_child m₁ _ j m (ch j) fun b hb => by
      by_cases hba : b = a
      · subst hba
        rw [update_self, hX]
        exact hdm b hb
      · rw [update_of_ne hba]
        exact hdm b hb]
    rw [show ch j = update ch a (mergeT (ch a) κ) j from (update_of_ne (Ne.symm haj) _ _).symm,
      update_eq_self]

variable (K : Type u) [CommRing K]

/-- **The Koszul sign of merging an edge of a tree cut at its last child `j` that is not a leaf**,
times the parity of the vertices of that child after its leaf, is the Koszul sign of the tree. -/
theorem kzAt_cut {k : ℕ} (m₁ : VMono G k) (ch : Fin k → STree (VMono G)) (j : Fin k)
    (ht : (STree.node m₁ ch).IsShuffle) (hnd : (STree.node m₁ ch).labels.Nodup)
    (hlast : ∀ a, j < a → (ch a).weight = 0) (m : ℕ) (hm : (ch j).first = m) {κ : ℕ ×ₗ ℕ}
    (hκ : κ ∈ (preKeys (STree.node m₁ (update ch j (.leaf m)))).tail) :
    kzAt K (STree.node m₁ (update ch j (.leaf m))) κ
        * σ K (vpar (fun _ _ => true) (ch j)
          && vaft (fun _ _ => true) (mergeT (STree.node m₁ (update ch j (.leaf m))) κ) m)
      = kzAt K (STree.node m₁ ch) κ := by
  have hmj : m ∈ (ch j).labels := hm ▸ first_mem (ht.child j)
  have ht₁ : (STree.node m₁ (update ch j (.leaf m))).IsShuffle :=
    isShuffle_update_child ht j (isShuffle_leaf m) (by rw [first_leaf, hm])
  have hnd₁ : (STree.node m₁ (update ch j (.leaf m))).labels.Nodup :=
    Multiset.nodup_of_le (labels_update_leaf_le m₁ ch j hmj) hnd
  have hdm : ∀ a, a ≠ j → m ∉ (ch a).labels := fun a ha => not_mem_of_node hnd (Ne.symm ha) hmj
  have hex := exists_mem_preKeys_of_cut hκ
  obtain ⟨a, haj, ha⟩ := hex
  have hw := weight_ne_zero_of_mem ha
  have haj' : a < j := by
    rcases lt_or_gt_of_ne haj with h | h
    · exact h
    · exact absurd (hlast a h) hw
  rw [preKeys_eq_cons hw, List.mem_cons] at ha
  rcases ha with rfl | ha
  · have hn := exists_node_of_weight_ne_zero hw
    obtain ⟨l, m₂, c₂, hc⟩ := hn
    have hc₁ : update ch j (.leaf m) a = .node m₂ c₂ := (update_of_ne haj _ _).trans hc
    have e1 := mergeT_root ht₁ hc₁
    have k1 := kzAt_root K ht₁ hc₁
    rw [update_of_ne haj] at e1 k1
    rw [e1, k1, kzAt_root K ht hc]
    have hQ := planar_update_left ch a c₂ (mergeN_eq m₁ l) j haj.symm (.leaf m)
    have hyQ : planar ch a c₂ (mergeN_eq m₁ l)
        (posEquivF a l _ (mergeN_eq m₁ l) (Sum.inl ⟨j, haj.symm⟩)) = ch j :=
      planar_inl ch a c₂ _ _
    have hdQ : ∀ r, r ≠ posEquivF a l _ (mergeN_eq m₁ l) (Sum.inl ⟨j, haj.symm⟩) →
        m ∉ (planar ch a c₂ (mergeN_eq m₁ l) r).labels := by
      intro r hr
      obtain ⟨x, rfl⟩ := (posEquivF a l _ (mergeN_eq m₁ l)).surjective r
      rcases x with b | i
      · rw [planar_inl]
        exact hdm b.1 fun e => hr (by rw [show b = ⟨j, haj.symm⟩ from Subtype.ext e])
      · rw [planar_inr]
        intro hmc
        exact hdm a haj (by rw [hc]; exact mem_labels_node.2 ⟨i, hmc⟩)
    have hπ : sortP (planar (update ch j (.leaf m)) a c₂ (mergeN_eq m₁ l))
        = sortP (planar ch a c₂ (mergeN_eq m₁ l)) := by
      rw [hQ]
      refine sortP_congr fun r => ?_
      by_cases hr : r = posEquivF a l _ (mergeN_eq m₁ l) (Sum.inl ⟨j, haj.symm⟩)
      · rw [hr, update_self, first_leaf, hyQ, hm]
      · rw [update_of_ne hr]
    have hRM := exists_rootMerge_eq hc₁ ht₁
    obtain ⟨M, -, hReq⟩ := hRM
    rw [hπ, hQ] at hReq
    rw [hReq, hπ, hQ]
    have hcv := kz_mul_σ_vaft K M (planar ch a c₂ (mergeN_eq m₁ l))
      (posEquivF a l _ (mergeN_eq m₁ l) (Sum.inl ⟨j, haj.symm⟩)) m hdQ
      (sortP (planar ch a c₂ (mergeN_eq m₁ l)))
    rw [prod_after_merged K ch a c₂ (mergeN_eq m₁ l) j haj.symm haj' hlast, mul_one, hyQ] at hcv
    have hKz := kz_mul_self K (fun r => preKeys (planar ch a c₂ (mergeN_eq m₁ l) r))
      (sortP (planar ch a c₂ (mergeN_eq m₁ l)))
    have hKz' := kz_mul_self K (fun r => preKeys (update (planar ch a c₂ (mergeN_eq m₁ l))
      (posEquivF a l _ (mergeN_eq m₁ l) (Sum.inl ⟨j, haj.symm⟩)) (.leaf m) r))
      (sortP (planar ch a c₂ (mergeN_eq m₁ l)))
    linear_combination kz K (fun r => preKeys (update (planar ch a c₂ (mergeN_eq m₁ l))
        (posEquivF a l _ (mergeN_eq m₁ l) (Sum.inl ⟨j, haj.symm⟩)) (.leaf m) r))
        (sortP (planar ch a c₂ (mergeN_eq m₁ l)))
        * (kz K (fun r => preKeys (planar ch a c₂ (mergeN_eq m₁ l) r))
          (sortP (planar ch a c₂ (mergeN_eq m₁ l))) * hcv
          - σ K (vpar (fun _ _ => true) (ch j) && vaft (fun _ _ => true) (STree.node M
            (update (planar ch a c₂ (mergeN_eq m₁ l))
              (posEquivF a l _ (mergeN_eq m₁ l) (Sum.inl ⟨j, haj.symm⟩)) (.leaf m)
            ∘ sortP (planar ch a c₂ (mergeN_eq m₁ l)))) m) * hKz)
      + kz K (fun r => preKeys (planar ch a c₂ (mergeN_eq m₁ l) r))
        (sortP (planar ch a c₂ (mergeN_eq m₁ l))) * hKz'
  · have ha₁ : κ ∈ (preKeys (update ch j (.leaf m) a)).tail := by
      rw [update_of_ne haj]
      exact ha
    rw [kzAt_of_mem_tail_child K ht₁ hnd₁ ha₁, kzAt_of_mem_tail_child K ht hnd ha,
      update_of_ne haj, mergeT_child ht₁ hnd₁ ha₁]
    have hX := (mergeT_spec (ch a) κ (ht.child a) (nodup_of_node hnd a) ha).2.1
    rw [σ_and_vaft_node_of_leaf K _ m₁ _ j m (by rw [update_of_ne (Ne.symm haj), update_self])
      fun b hb => by
        by_cases hba : b = a
        · subst hba
          rw [update_self, update_of_ne haj, hX]
          exact hdm b hb
        · rw [update_of_ne hba, update_of_ne hb]
          exact hdm b hb]
    rw [Finset.prod_eq_one fun b _ => ?_, mul_one]
    split_ifs with hb
    · have hba : b ≠ a := fun e => absurd (e ▸ hb) (not_lt.2 (le_of_lt haj'))
      rw [update_of_ne hba, update_of_ne (ne_of_gt hb),
        vpar_true_of_weight_eq_zero (hlast b hb), Bool.and_false, σ_false]
    · rfl

end CutMerge

end ShuffleBarSym

namespace ShuffleBarSym

section Expansion

variable {K : Type u} [CommRing K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {G : Type} [Fintype G] [DecidableEq G]
  (c : ∀ k, Module.Basis (BinGen G k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen G k), GrSpecies.par (R := K) false (c k β) = c k β)

/-- **The evaluation of the tree with the edge above the vertex of key `κ` merged**, zero when `κ`
is not the key of a vertex other than the root of a shuffle tree with distinct leaves. -/
noncomputable def evM (t : STree (VMono G)) (κ : ℕ ×ₗ ℕ) (Y : Finset ℕ) (h : t.labels = Y.val) :
    FreeGrL K (BarGen (Ibar K E c hc)) (Lab Y) :=
  @dite _ (κ ∈ (preKeys t).tail ∧ t.IsShuffle ∧ t.labels.Nodup) (Classical.propDecidable _)
    (fun hκ => FreeGrL.shEv (genBasis c hc) (mergeT t κ) Y
      ((mergeT_spec t κ hκ.2.1 hκ.2.2 hκ.1).2.1.trans h)) fun _ => 0

lemma evM_eq {t : STree (VMono G)} {κ : ℕ ×ₗ ℕ} (hκ : κ ∈ (preKeys t).tail) (ht : t.IsShuffle)
    (hnd : t.labels.Nodup) (Y : Finset ℕ) (h : t.labels = Y.val)
    (h' : (mergeT t κ).labels = Y.val) :
    evM c hc t κ Y h = FreeGrL.shEv (genBasis c hc) (mergeT t κ) Y h' := by
  unfold evM
  rw [dif_pos ⟨hκ, ht, hnd⟩]

/-- **The expansion of the bar differential over the edges**, on the evaluations of a tree. -/
def DProp (t : STree (VMono G)) : Prop :=
  ∀ (Y : Finset ℕ) (h : t.labels = Y.val),
    Bar.d (Ibar K E c hc) (Lab Y) (FreeGrL.shEv (genBasis c hc) t Y h)
      = ((preKeys t).tail.mapIdx fun i κ =>
          ((-1 : K) ^ i * kzAt K t κ) • evM c hc t κ Y h).sum

lemma d_unitL (A : Type) [Fintype A] [DecidableEq A] :
    Bar.d (Ibar K E c hc) A (FreeGrL.unitL K (BarGen (Ibar K E c hc)) A) = 0 := by
  rw [FreeGrL.unitL, map_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [Bar.d_map]
  have := Bar.d_one (I := Ibar K E c hc)
  erw [this, map_zero]

lemma dProp_leaf (a : ℕ) : DProp c hc (.leaf a) := by
  intro Y h
  rw [FreeGrL.shEv_leaf, d_unitL]
  rfl

lemma dProp_of_weight_one {t : STree (VMono G)} (hw : t.weight = 1) : DProp c hc t := by
  intro Y h
  have hco := exists_corolla_of_weight_eq_one hw
  obtain ⟨l, m, ch, rfl, hl⟩ := hco
  have hcor := FreeGrL.exists_shEv_corolla (genBasis c hc) m ch Y h hl
  obtain ⟨θ, -, hev⟩ := hcor
  have htail : (preKeys (STree.node m ch)).tail = [] :=
    List.eq_nil_of_length_eq_zero (by rw [List.length_tail, length_preKeys, hw])
  rw [htail]
  exact (congrArg _ hev).trans (Bar.d_map_ι _ θ _)

/-- **The expansion of the bar differential, splitting off the last child that is not a leaf**:
the edges of the tree cut at that child (`kzAt_cut`, `mergeT_cut_subst`), the edges of the child,
and the edge above the child (`rmProp`). -/
theorem dProp_step {k : ℕ} (m₁ : VMono G k) (ch : Fin k → STree (VMono G)) (j : Fin k)
    (ht : (STree.node m₁ ch).IsShuffle) (hnd : (STree.node m₁ ch).labels.Nodup)
    (hlast : ∀ a, j < a → (ch a).weight = 0) (hj0 : (ch j).weight ≠ 0) (m : ℕ)
    (hm : (ch j).first = m) (ih₁ : DProp c hc (STree.node m₁ (update ch j (.leaf m))))
    (ih₂ : DProp c hc (ch j)) : DProp c hc (STree.node m₁ ch) := by
  intro Y h
  have hn := exists_node_of_weight_ne_zero hj0
  obtain ⟨l, m₂, c₂, hc₂⟩ := hn
  have hmj : m ∈ (ch j).labels := hm ▸ first_mem (ht.child j)
  have ht₁ : (STree.node m₁ (update ch j (.leaf m))).IsShuffle :=
    isShuffle_update_child ht j (isShuffle_leaf m) (by rw [first_leaf, hm])
  have hnd₁ : (STree.node m₁ (update ch j (.leaf m))).labels.Nodup :=
    Multiset.nodup_of_le (labels_update_leaf_le m₁ ch j hmj) hnd
  have hnd₂ : (ch j).labels.Nodup := nodup_of_node hnd j
  have hdm : ∀ a, a ≠ j → m ∉ (ch a).labels := fun a ha => not_mem_of_node hnd (Ne.symm ha) hmj
  have hm₁ : m ∈ (STree.node m₁ (update ch j (.leaf m))).labels :=
    mem_labels_node.2 ⟨j, by
      rw [update_self]
      exact Multiset.mem_singleton_self _⟩
  have hsub : (STree.node m₁ (update ch j (.leaf m))).subst (update STree.leaf m (ch j))
      = STree.node m₁ ch := by
    rw [subst_update_child m₁ ch j m (ch j) hdm, update_eq_self]
  have hY₁ := FreeGrL.labels_eq_toFinset hnd₁
  have hY₂ := FreeGrL.labels_eq_toFinset hnd₂
  have s : LabSplit Y (STree.node m₁ (update ch j (.leaf m))).labels.toFinset
      (ch j).labels.toFinset m := LabSplit.of_val (Multiset.mem_toFinset.2 hm₁) (by
    rw [← h, ← hY₁, ← hY₂, ← hsub]
    exact labels_subst_update_add _ _ hm₁ hnd₁)
  -- the leaf `m` has only leaves after it
  have hvaft : ∀ x, σ K (x && vaft (fun _ _ => true) (STree.node m₁ (update ch j (.leaf m))) m)
      = 1 := fun x => by
    rw [σ_and_vaft_node_of_leaf K _ m₁ _ j m (update_self _ _ _) fun a ha => by
      rw [update_of_ne ha]
      exact hdm a ha]
    refine Finset.prod_eq_one fun a _ => ?_
    split_ifs with ha
    · rw [update_of_ne (ne_of_gt ha), vpar_true_of_weight_eq_zero (hlast a ha), Bool.and_false,
        σ_false]
    · rfl
  -- the tree as a composite
  have hsplit := ((compL_shEv (genBasis c hc) (par_genBasis c hc) s _ (ch j) hY₁ hY₂
    (by rw [hsub]; exact h)).trans ((congrArg (· • _) (hvaft _)).trans ((one_smul K _).trans
      (shEv_congr c hc hsub Y _ h)))).symm
  have hd := (congrArg (Bar.d (Ibar K E c hc) (Lab Y)) hsplit).trans (d_compL s _ _)
  have hL : (preKeys (STree.node m₁ ch)).tail
      = (preKeys (STree.node m₁ (update ch j (.leaf m)))).tail
        ++ vkey (ch j) :: (preKeys (ch j)).tail := by
    rw [tail_preKeys_cut m₁ ch j hlast m]
    exact congrArg _ (preKeys_eq_cons hj0)
  have hw₁ : 1 ≤ (STree.node m₁ (update ch j (.leaf m))).weight := by
    rw [weight_node]
    omega
  have hlen : (preKeys (STree.node m₁ (update ch j (.leaf m)))).tail.length + 1
      = (STree.node m₁ (update ch j (.leaf m))).weight := by
    rw [List.length_tail, length_preKeys]
    omega
  -- the edges of the tree cut at `j`
  have hA : compL K s (Bar.d (Ibar K E c hc) _ (FreeGrL.shEv (genBasis c hc)
      (STree.node m₁ (update ch j (.leaf m))) _ hY₁)) (FreeGrL.shEv (genBasis c hc) (ch j) _ hY₂)
      = ((preKeys (STree.node m₁ (update ch j (.leaf m)))).tail.mapIdx fun i κ =>
          ((-1 : K) ^ i * kzAt K (STree.node m₁ ch) κ)
            • evM c hc (STree.node m₁ ch) κ Y h).sum := by
    refine (congrArg (fun X => compL K s X (FreeGrL.shEv (genBasis c hc) (ch j) _ hY₂))
      (ih₁ _ hY₁)).trans ?_
    refine (map_sum_mapIdx ((compL K s).flip
      (FreeGrL.shEv (genBasis c hc) (ch j) _ hY₂)).toAddMonoidHom _ _).trans ?_
    refine sum_mapIdx_congr _ fun i κ hκ => ?_
    have hκt : κ ∈ (preKeys (STree.node m₁ ch)).tail := by
      rw [hL]
      exact List.mem_append_left _ hκ
    have hs₁ := (mergeT_spec _ κ ht₁ hnd₁ hκ).2.1
    have hst := (mergeT_spec _ κ ht hnd hκt).2.1
    have hcut := mergeT_cut_subst m₁ ch j ht hnd m hm hκ
    have e₁ := evM_eq c hc hκ ht₁ hnd₁ _ hY₁ (hs₁.trans hY₁)
    have e₂ := evM_eq c hc hκt ht hnd Y h (hst.trans h)
    have hcs := compL_shEv (genBasis c hc) (par_genBasis c hc) s
      (mergeT (STree.node m₁ (update ch j (.leaf m))) κ) (ch j) (hs₁.trans hY₁) hY₂
      (by rw [hcut]; exact hst.trans h)
    have hk := kzAt_cut K m₁ ch j ht hnd hlast m hm hκ
    show compL K s (((-1 : K) ^ i * kzAt K _ κ) • evM c hc _ κ _ hY₁)
      (FreeGrL.shEv (genBasis c hc) (ch j) _ hY₂) = _
    refine (LinearMap.map_smul₂ _ _ _ _).trans ?_
    refine (congrArg (fun X => ((-1 : K) ^ i * kzAt K (STree.node m₁ (update ch j (.leaf m))) κ)
      • compL K s X (FreeGrL.shEv (genBasis c hc) (ch j) _ hY₂)) e₁).trans ?_
    refine (congrArg (fun X => ((-1 : K) ^ i
      * kzAt K (STree.node m₁ (update ch j (.leaf m))) κ) • X) hcs).trans ?_
    refine (smul_smul _ _ _).trans ?_
    refine (congrArg₂ (· • ·) ?_ (shEv_congr c hc hcut Y _ (hst.trans h))).trans
      (congrArg _ e₂.symm)
    rw [mul_assoc, hk]
  -- the edges of the child
  have hB : compL K s (GrOperad.tw (R := K) true (FreeGrL.shEv (genBasis c hc)
      (STree.node m₁ (update ch j (.leaf m))) _ hY₁))
      (Bar.d (Ibar K E c hc) _ (FreeGrL.shEv (genBasis c hc) (ch j) _ hY₂))
      = ((preKeys (ch j)).tail.mapIdx fun i κ =>
          ((-1 : K) ^ (i + (preKeys (STree.node m₁ (update ch j (.leaf m)))).tail.length + 1)
            * kzAt K (STree.node m₁ ch) κ) • evM c hc (STree.node m₁ ch) κ Y h).sum := by
    have htw := GrOperad.tw_hom (R := K) true
      (FreeGrL.par_shEv (genBasis c hc) (par_genBasis c hc) _ _ hY₁)
    refine (congrArg₂ (fun X Z => compL K s X Z) htw (ih₂ _ hY₂)).trans ?_
    refine (LinearMap.map_smul₂ _ _ _ _).trans ?_
    refine (congrArg (fun X => σ K (true && vpar (fun _ _ => true)
      (STree.node m₁ (update ch j (.leaf m)))) • X) (map_sum_mapIdx (compL K s
        (FreeGrL.shEv (genBasis c hc) (STree.node m₁ (update ch j (.leaf m))) _ hY₁)).toAddMonoidHom
          _ _)).trans ?_
    refine (map_sum_mapIdx (DistribSMul.toAddMonoidHom _ (σ K (true && vpar (fun _ _ => true)
      (STree.node m₁ (update ch j (.leaf m)))))) _ _).trans ?_
    refine sum_mapIdx_congr _ fun i κ hκ => ?_
    have hκt : κ ∈ (preKeys (STree.node m₁ ch)).tail := by
      rw [hL]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hκ)
    have hs₂ := (mergeT_spec _ κ (ht.child j) hnd₂ hκ).2.1
    have hst := (mergeT_spec _ κ ht hnd hκt).2.1
    have hchild : (STree.node m₁ (update ch j (.leaf m))).subst
        (update STree.leaf m (mergeT (ch j) κ)) = mergeT (STree.node m₁ ch) κ := by
      rw [subst_update_child m₁ ch j m _ hdm, mergeT_child ht hnd hκ]
    have e₁ := evM_eq c hc hκ (ht.child j) hnd₂ _ hY₂ (hs₂.trans hY₂)
    have e₂ := evM_eq c hc hκt ht hnd Y h (hst.trans h)
    have hcs := compL_shEv (genBasis c hc) (par_genBasis c hc) s _ (mergeT (ch j) κ) hY₁
      (hs₂.trans hY₂) (by rw [hchild]; exact hst.trans h)
    have hk := kzAt_of_mem_tail_child K ht hnd hκ
    show σ K _ • compL K s _ (((-1 : K) ^ i * kzAt K (ch j) κ) • evM c hc (ch j) κ _ hY₂) = _
    refine (congrArg (fun X => σ K (true && vpar (fun _ _ => true)
      (STree.node m₁ (update ch j (.leaf m)))) • X) ((LinearMap.map_smul _ _ _).trans
        (congrArg (fun X => ((-1 : K) ^ i * kzAt K (ch j) κ) • X)
          ((congrArg (compL K s _) e₁).trans (hcs.trans ((congrArg (· • _) (hvaft _)).trans
            ((one_smul K _).trans (shEv_congr c hc hchild Y _ (hst.trans h))))))))).trans ?_
    refine (smul_smul _ _ _).trans ((congrArg (· • _) ?_).trans (congrArg _ e₂.symm))
    rw [hk, Bool.true_and, vpar_true, σ_bodd, ← hlen, pow_add, pow_add]
    ring
  -- the edge above the child
  have hC : mcL s (FreeGrL.shEv (genBasis c hc) (STree.node m₁ (update ch j (.leaf m))) _ hY₁)
      (FreeGrL.shEv (genBasis c hc) (ch j) _ hY₂)
      = ((-1 : K) ^ (preKeys (STree.node m₁ (update ch j (.leaf m)))).tail.length
          * kzAt K (STree.node m₁ ch) (vkey (ch j)))
        • evM c hc (STree.node m₁ ch) (vkey (ch j)) Y h := by
    have hκ₀ : vkey (ch j) ∈ (preKeys (STree.node m₁ ch)).tail := by
      rw [hL]
      exact List.mem_append_right _ List.mem_cons_self
    have hroot := mergeT_root ht hc₂
    have hR : (rootMerge m₁ ch j m₂ c₂).labels = Y.val := by
      rw [← hroot]
      exact (mergeT_spec _ _ ht hnd hκ₀).2.1.trans h
    have hrm := rmProp c hc _ m₁ ch j m₂ c₂ le_rfl hc₂ ht hnd hlast _ _ _ m s _ _ _
      (hm.symm.trans (by rw [hc₂])) rfl hc₂ rfl hY₁ hY₂ hR
    have hR' : (mergeT (STree.node m₁ ch) (vkey (ch j))).labels = Y.val := by
      rw [hroot]
      exact hR
    refine hrm.trans (congrArg₂ (· • ·) ?_ ((shEv_congr c hc hroot.symm Y hR hR').trans
      (evM_eq c hc hκ₀ ht hnd Y h hR').symm))
    have e0 := weight_update_child m₁ ch j (.leaf 0)
    have em := weight_update_child m₁ ch j (.leaf m)
    rw [weight_leaf, add_zero] at e0 em
    rw [kzAt_root K ht hc₂]
    unfold rmCoeff
    rw [List.length_tail, length_preKeys]
    congr 2
    omega
  refine hd.trans ((congrArg₂ (· + ·) (congrArg₂ (· + ·) hA hB) hC).trans
    ((add_right_comm _ _ _).trans ?_))
  refine Eq.trans ?_ (congrArg (fun L => (L.mapIdx fun i κ =>
    ((-1 : K) ^ i * kzAt K (STree.node m₁ ch) κ) • evM c hc (STree.node m₁ ch) κ Y h).sum) hL).symm
  exact (sum_mapIdx_append_cons _ _ _ _).symm

/-- **The bar differential expands over the edges** on the evaluation of every shuffle tree of
monomials with distinct leaves, by induction on the number of vertices (`dProp_step`). -/
theorem dProp_all : ∀ (n : ℕ) (t : STree (VMono G)), t.weight ≤ n → t.IsShuffle →
    t.labels.Nodup → DProp c hc t
  | _, .leaf a, _, _, _ => dProp_leaf c hc a
  | 0, .node _ _, hw, _, _ => by
    simp only [weight_node] at hw
    omega
  | n + 1, .node m₁ ch, hw, ht, hnd => by
    by_cases hA : ∃ a, (ch a).weight ≠ 0
    · have hS : (Finset.univ.filter fun a => (ch a).weight ≠ 0).Nonempty := by
        obtain ⟨a, ha⟩ := hA
        exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩⟩
      have hex : ∃ j, (ch j).weight ≠ 0 ∧ ∀ a, (ch a).weight ≠ 0 → a ≤ j :=
        ⟨(Finset.univ.filter fun a => (ch a).weight ≠ 0).max' hS,
          (Finset.mem_filter.1 (Finset.max'_mem _ hS)).2, fun a ha =>
            Finset.le_max' _ a (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩)⟩
      obtain ⟨j, hj0, hle⟩ := hex
      have hlast : ∀ a, j < a → (ch a).weight = 0 := fun a ha => by
        by_contra hne
        exact absurd (hle a hne) (not_le.2 ha)
      have hw' := weight_update_child m₁ ch j (.leaf (ch j).first)
      rw [weight_leaf, add_zero] at hw'
      have hwj : (ch j).weight ≤ ∑ a, (ch a).weight :=
        Finset.single_le_sum (f := fun a => (ch a).weight) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ j)
      have hwn : (STree.node m₁ ch).weight = 1 + ∑ a, (ch a).weight := weight_node _ _
      refine dProp_step c hc m₁ ch j ht hnd hlast hj0 _ rfl
        (dProp_all n _ (by omega)
          (isShuffle_update_child ht j (isShuffle_leaf _) rfl)
          (Multiset.nodup_of_le (labels_update_leaf_le m₁ ch j (first_mem (ht.child j))) hnd))
        (dProp_all n (ch j) (by omega) (ht.child j) (nodup_of_node hnd j))
    · push Not at hA
      refine dProp_of_weight_one c hc ?_
      rw [weight_node, Finset.sum_eq_zero fun a _ => hA a, Nat.add_zero]

end Expansion

section ExpansionAll

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {G : Type} [Fintype G] [DecidableEq G]
  (c : ∀ k, Module.Basis (BinGen G k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen G k), GrSpecies.par (R := K) false (c k β) = c k β)

/-- **The expansion of the bar differential over the edges holds on every basis vector**: `Bar.d`
of the basis vector of `t` is the sum, over the keys `κ` of the vertices other than the root, of
`(-1)^p kzAt t κ` times the basis vector of `mergeT t κ`, `p` the position of `κ` in preorder. -/
theorem dExpansion {n : ℕ} (t : SMono (VMono G) (Finset.range n)) : DExpansion c hc t := by
  unfold DExpansion
  have hnd := nodup_smono t
  have h : t.1.labels = (Finset.range (Fintype.card (Fin n))).val := by
    rw [Fintype.card_fin]
    exact t.2.2
  have hdp := dProp_all c hc _ t.1 le_rfl t.2.1 hnd _ h
  refine ((congrArg (Bar.d _ _) (barBasisN_eq_shEv c hc n t h)).trans (Bar.d_map _ _)).trans ?_
  refine (congrArg _ hdp).trans ?_
  refine (map_sum_mapIdx (GrOperad.map (R := K) (P := FreeGrL K (BarGen (Ibar K E c hc)))
    (FreeGrL.posEquiv (Fin n)).symm).toAddMonoidHom
    _ _).trans ?_
  refine (sum_mapIdx_eq_sum_toFinset _ (nodup_tail_preKeys t.2.1 hnd) _).trans ?_
  refine Finset.sum_congr rfl fun κ hκ => ?_
  rw [List.mem_toFinset] at hκ
  have hs := (mergeT_spec t.1 κ t.2.1 hnd hκ).2.1
  have hS : (mergeS t κ).1.labels = (Finset.range (Fintype.card (Fin n))).val := by
    rw [mergeS_val t hκ, hs]
    exact h
  show GrOperad.map (R := K) (P := FreeGrL K (BarGen (Ibar K E c hc)))
    (FreeGrL.posEquiv (Fin n)).symm (_ • evM c hc t.1 κ _ h) = _
  refine (map_smul _ _ _).trans (congrArg (fun X => ((-1 : K) ^ (preKeys t.1).tail.idxOf κ
    * kzAt K t.1 κ) • X) ((congrArg (GrOperad.map (R := K) (FreeGrL.posEquiv (Fin n)).symm)
      ((evM_eq c hc hκ t.2.1 hnd _ h (hs.trans h)).trans
        (shEv_congr c hc (mergeS_val t hκ).symm _ _ hS))).trans
      (barBasisN_eq_shEv c hc n (mergeS t κ) hS).symm))

/-- **`Φ` intertwines the differentials**: `ΦL ∘ Bar.d = ShuffleBar.d ∘ ΦL` on all of
`B(T, Ī)(Fin n)`, `T` the free graded operad on the even binary generators `c`. -/
theorem ΦL_d {n : ℕ} (x : BarCoop (Ibar K E c hc) (Fin n)) :
    ΦL c hc n (Bar.d (Ibar K E c hc) (Fin n) x) = ShuffleBar.d K (ΦL c hc n x) :=
  ΦL_d_of_expansion c hc (fun t => dExpansion c hc t) x

end ExpansionAll

end ShuffleBarSym

end Operad
