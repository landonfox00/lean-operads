/-
# Binary quadratic presentations evaluated in an endomorphism operad

Step 3 of the bridge between symmetric and shuffle operads (Dotsenko–Khoroshkin), common part for
`Ass` and `Pois`. Let `E` be a graded linear species over a commutative ring `K` with an even
basis `c k` of each `E (Fin k)` indexed by `BinGen G k`, `T = FreeGrL K E`, and
`φ : T → SymGr (EndOp K V)` a morphism of graded operads into the endomorphism operad of a
`K`-module `V`, every operation even.

* **Trees evaluate to their values** (`SymPresB.app_shEv`): the operation `φ (ev t)` of the
  evaluation of a binary tree `t`, applied to the values `v a` of its leaves, is the value
  `SymPresB.sev` of `t` computed with the bilinear operations `φ (c 2 g)` at its vertices.
  Hence the same for the binary-tree basis `ShuffleBarSym.tBasis` (`SymPresB.app_tBasis`).
* **The relators of a model** (`SymPresB.kerRel`): the operations of arity three which `φ` kills.
  They are concentrated in arity three and stable under the permutations (`SymPresB.kerRel_ne`,
  `SymPresB.kerRel_perm`), and their shuffle relators `ShuffleBarSym.Rsh` are the coordinate
  vectors `v` whose combination `∑ v σ • σ` has the value zero on every family of three inputs
  (`SymPresB.mem_Rsh_kerRel`).
* **The regular representation of `𝔖₂` in arity two** (`SymPresB.Reg2`): the functions on the
  numberings `Fin 2 ≃ A`, an even graded linear species concentrated in arity two, and the
  morphism `SymPresB.model m` into `SymGr (EndOp K V)` sending the numbering `τ` to the bilinear
  map `m` applied to the inputs `τ 0, τ 1` (`SymPresB.model_apply`).
-/
import Operad.ShuffleBarJ
import Operad.GrFreeEven
import Operad.BinaryKoszul

universe u v

namespace Operad

open Function Sym GerBV STree

namespace SymPresB

/-! ## Evaluating operations of the endomorphism operad -/

section Eval

variable {K : Type u} [CommRing K] {V : Type v} [AddCommGroup V] [Module K V]

/-- **The value of an operation** of `SymGr (EndOp K V)` on a family of inputs. -/
def sgEv {A : Type} [Fintype A] [DecidableEq A] (x : SymGr (EndOp K V) A) (w : A → V) : V :=
  (show EndOp K V A from x) w

lemma sgEv_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    (x : SymGr (EndOp K V) A) (w : B → V) :
    sgEv (GrOperad.map (R := K) e x) w = sgEv x (w ∘ e) := rfl

lemma sgEv_comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (x : SymGr (EndOp K V) A) (y : SymGr (EndOp K V) B) (w : Without A i ⊕ B → V) :
    sgEv (GrOperad.comp (R := K) i x y) w = sgEv x (feed i w (sgEv y fun b => w (Sum.inr b))) :=
  rfl

lemma sgEv_one (w : Unit → V) : sgEv (GrOperad.one (R := K) (P := SymGr (EndOp K V))) w = w () :=
  rfl

lemma sgEv_add {A : Type} [Fintype A] [DecidableEq A] (x y : SymGr (EndOp K V) A) (w : A → V) :
    sgEv (x + y) w = sgEv x w + sgEv y w := rfl

lemma sgEv_smul {A : Type} [Fintype A] [DecidableEq A] (a : K) (x : SymGr (EndOp K V) A)
    (w : A → V) : sgEv (a • x) w = a • sgEv x w := rfl

lemma sgEv_sum {A : Type} [Fintype A] [DecidableEq A] {ι : Type*} (s : Finset ι)
    (x : ι → SymGr (EndOp K V) A) (w : A → V) :
    sgEv (∑ i ∈ s, x i) w = ∑ i ∈ s, sgEv (x i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, sgEv_add, ih]

lemma sgEv_zero {A : Type} [Fintype A] [DecidableEq A] (w : A → V) :
    sgEv (0 : SymGr (EndOp K V) A) w = 0 := rfl

/-- **An operation is zero iff its value on every family of inputs is.** -/
lemma eq_zero_iff {A : Type} [Fintype A] [DecidableEq A] (x : SymGr (EndOp K V) A) :
    x = 0 ↔ ∀ w, sgEv x w = 0 :=
  ⟨fun h w => by rw [h]; rfl, fun h => MultilinearMap.ext h⟩

end Eval

/-! ## The values of binary trees -/

section Trees

variable {G : Type} {V : Type v}

/-- **The value of a binary tree** at the values `v a` of its leaves, along the operations
`μ g` of the vertices. -/
def sev (μ : G → V → V → V) (v : ℕ → V) : STree (BinGen G) → V
  | .leaf a => v a
  | .node (BinGen.op g) c => μ g (sev μ v (c 0)) (sev μ v (c 1))

/-- **The value of a binary tree**, on binary trees. -/
def lev (μ : G → V → V → V) (v : ℕ → V) : LTree G → V
  | .leaf a => v a
  | .node g l r => μ g (lev μ v l) (lev μ v r)

lemma sev_toBinSTree (μ : G → V → V → V) (v : ℕ → V) :
    ∀ t : LTree G, sev μ v (LTree.toBinSTree t) = lev μ v t
  | .leaf _ => rfl
  | .node g l r => by
    show μ g (sev μ v (LTree.toBinSTree l)) (sev μ v (LTree.toBinSTree r)) = _
    rw [sev_toBinSTree μ v l, sev_toBinSTree μ v r]
    rfl

/-- **The value only depends on the values at the leaves.** -/
lemma sev_congr (μ : G → V → V → V) {v v' : ℕ → V} :
    ∀ t : STree (BinGen G), (∀ a ∈ t.labels, v a = v' a) → sev μ v t = sev μ v' t
  | .leaf a, h => h a (Multiset.mem_singleton_self a)
  | .node (BinGen.op g) c, h => by
    show μ g _ _ = μ g _ _
    rw [sev_congr μ (c 0) fun a ha => h a (mem_labels_node.2 ⟨0, ha⟩),
      sev_congr μ (c 1) fun a ha => h a (mem_labels_node.2 ⟨1, ha⟩)]

lemma lev_congr (μ : G → V → V → V) {v v' : ℕ → V} :
    ∀ t : LTree G, (∀ a ∈ t.labels, v a = v' a) → lev μ v t = lev μ v' t
  | .leaf a, h => h a (List.mem_singleton_self a)
  | .node g l r, h => by
    show μ g _ _ = μ g _ _
    rw [lev_congr μ l fun a ha => h a (by simp [ha]),
      lev_congr μ r fun a ha => h a (by simp [ha])]

/-- **A binary tree has a leaf.** -/
lemma exists_mem_labels : ∀ t : STree (BinGen G), ∃ a, a ∈ t.labels
  | .leaf a => ⟨a, Multiset.mem_singleton_self a⟩
  | .node (BinGen.op _) c => by
    obtain ⟨a, ha⟩ := exists_mem_labels (c 0)
    exact ⟨a, mem_labels_node.2 ⟨0, ha⟩⟩

end Trees

/-! ## Evaluations of trees under a morphism into an endomorphism operad -/

section Model

variable {K : Type u} [CommRing K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {G : Type} [Fintype G] [DecidableEq G]
  (c : ∀ k, Module.Basis (BinGen G k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen G k), GrSpecies.par (R := K) false (c k β) = c k β)
  {V : Type v} [AddCommGroup V] [Module K V]
  (φ : GrOperadHom K (FreeGrL K E) (SymGr (EndOp K V)))

/-- **The bilinear operation of a generator** under `φ`. -/
noncomputable def μ (g : G) (x y : V) : V :=
  sgEv (φ.app (Fin 2) ((FreeGrL.ι K E).app (Fin 2) (c 2 (BinGen.op g)))) ![x, y]

omit [Fintype G] [DecidableEq G] in
lemma shEv_tree_congr {t t' : STree (BinGen G)} (ht : t = t') (Y : Finset ℕ)
    (h : t.labels = Y.val) (h' : t'.labels = Y.val) :
    FreeGrL.shEv (R := K) c t Y h = FreeGrL.shEv c t' Y h' := by
  subst ht
  rfl

omit [Fintype G] [DecidableEq G] in
/-- **The unit on one leaf** takes the value of that leaf. -/
lemma app_unitL {Y : Finset ℕ} {a : ℕ} (hY : Y.val = {a}) (v : ℕ → V) :
    sgEv (φ.app (Lab Y) (FreeGrL.unitL K E (Lab Y))) (fun s => v s.1) = v a := by
  have ha : a ∈ Y := by
    rw [← Finset.mem_val, hY]
    exact Multiset.mem_singleton_self a
  let e : Unit ≃ Lab Y := ⟨fun _ => ⟨a, ha⟩, fun _ => (), fun _ => rfl, fun x => Subtype.ext (by
    have hx := x.2
    rw [← Finset.mem_val, hY, Multiset.mem_singleton] at hx
    exact hx.symm)⟩
  rw [FreeGrL.unitL_eq e, φ.app_map, φ.app_one]
  rfl

omit [Fintype G] [DecidableEq G] in
/-- **A corolla on two leaves** takes the value of its operation at the values of its leaves. -/
lemma app_corolla (g : G) {a b : ℕ} (hab : a ≠ b) (Y : Finset ℕ)
    (h : (STree.node (BinGen.op g) ![STree.leaf a, STree.leaf b] : STree (BinGen G)).labels
      = Y.val) (v : ℕ → V) :
    sgEv (φ.app (Lab Y) (FreeGrL.shEv c _ Y h)) (fun s => v s.1) = μ c φ g (v a) (v b) := by
  have hY : Y.val = {a, b} := by
    rw [← h]
    simp [Fin.sum_univ_two]
  have hmem : ∀ j : Fin 2, (![a, b] j : ℕ) ∈ Y := fun j => by
    rw [← Finset.mem_val, hY]
    fin_cases j <;> simp
  let θ : Fin 2 ≃ Lab Y := Equiv.ofBijective (fun j => ⟨![a, b] j, hmem j⟩)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨fun i j hij => by
      have hij' : (![a, b] i : ℕ) = ![a, b] j := congrArg Subtype.val hij
      fin_cases i <;> fin_cases j <;> simp_all [eq_comm], by
      rw [Fintype.card_fin, Fintype.card_coe, ← Finset.card_val, hY]
      simp⟩)
  have ht : (STree.node (BinGen.op g) ![STree.leaf a, STree.leaf b] : STree (BinGen G))
      = STree.node (BinGen.op g) fun j => STree.leaf (θ j).1 := by
    congr 1
    funext j
    fin_cases j <;> rfl
  rw [shEv_tree_congr c ht Y h (ht ▸ h), FreeGrL.shEv_corolla, φ.app_map, sgEv_map]
  have hw : ((fun s : Lab Y => v s.1) ∘ θ) = ![v a, v b] := by
    funext j
    fin_cases j <;> rfl
  rw [hw]
  rfl

omit [Fintype G] [DecidableEq G] in
include hc in
/-- **Substituting a tree at a leaf** substitutes its value for the value of that leaf. -/
lemma app_subst (t t' : STree (BinGen G)) {Y₁ Y₂ : Finset ℕ} (h₁ : t.labels = Y₁.val)
    (h₂ : t'.labels = Y₂.val) {m : ℕ} (hm : m ∈ Y₁) (hd : Disjoint (Y₁.erase m) Y₂)
    (Y : Finset ℕ) (h : (t.subst (update STree.leaf m t')).labels = Y.val) (v : ℕ → V) :
    sgEv (φ.app (Lab Y) (FreeGrL.shEv c (t.subst (update STree.leaf m t')) Y h))
        (fun s => v s.1)
      = sgEv (φ.app (Lab Y₁) (FreeGrL.shEv c t Y₁ h₁)) (fun s => update v m
          (sgEv (φ.app (Lab Y₂) (FreeGrL.shEv c t' Y₂ h₂)) (fun s => v s.1)) s.1) := by
  have hY : Y = (Y₁.erase m).disjUnion Y₂ hd :=
    Finset.val_inj.1 (h.symm.trans (FreeGrL.labels_subst_update h₁ h₂ hm hd))
  obtain ⟨Ψ, hΨ⟩ := FreeGrL.exists_svalEquiv (Y := Y) (⟨m, hm⟩ : Lab Y₁)
    (fun x hx hne hx₂ => Finset.disjoint_left.1 hd (Finset.mem_erase.2 ⟨hne, hx⟩) hx₂)
    (fun x => by rw [hY, Finset.mem_disjUnion, Finset.mem_erase]; tauto)
  have hcs := FreeGrL.comp_shEv c (p := fun _ _ => false) hc t' Y₂ h₂ t Y₁ h₁ m hm Y h Ψ.symm
    (fun x => by rw [← hΨ, Equiv.apply_symm_apply])
  rw [ShuffleBarSym.vpar_false, Bool.false_and, σ_false, one_smul] at hcs
  have hev : FreeGrL.shEv c (t.subst (update STree.leaf m t')) Y h
      = GrOperad.map (R := K) Ψ (GrOperad.comp (R := K) (⟨m, hm⟩ : Lab Y₁)
        (FreeGrL.shEv c t Y₁ h₁) (FreeGrL.shEv c t' Y₂ h₂)) := by
    rw [hcs, ← GrOperad.map_trans, Equiv.symm_trans_self, GrOperad.map_refl]
  rw [hev, φ.app_map, φ.app_comp, sgEv_map, sgEv_comp]
  have hin : (fun b : Lab Y₂ => ((fun s : Lab Y => v s.1) ∘ Ψ) (Sum.inr b)) = fun s => v s.1 :=
    funext fun b => by
      show v (Ψ (Sum.inr b)).1 = v b.1
      rw [hΨ]
      rfl
  rw [hin]
  congr 1
  funext s
  by_cases hs : s = ⟨m, hm⟩
  · subst hs
    rw [feed_self, update_self]
  · have hs' : s.1 ≠ m := fun e => hs (Subtype.ext e)
    rw [feed_of_ne hs, update_of_ne hs']
    show v (Ψ (Sum.inl ⟨s, hs⟩)).1 = v s.1
    rw [hΨ]
    rfl

omit [Fintype G] [DecidableEq G] in
lemma labels_eq_toFinset {t : STree (BinGen G)} (h : t.labels.Nodup) :
    t.labels = t.labels.toFinset.val := by
  rw [Multiset.toFinset_val, Multiset.Nodup.dedup h]

omit [Fintype G] [DecidableEq G] in
include hc in
/-- **The evaluation of a binary tree takes its value**: `φ (ev t)`, applied to the values of
the leaves, is the value of `t` computed with the operations `μ g` at the vertices. -/
theorem app_shEv : ∀ (t : STree (BinGen G)) (Y : Finset ℕ) (h : t.labels = Y.val) (v : ℕ → V),
    sgEv (φ.app (Lab Y) (FreeGrL.shEv c t Y h)) (fun s => v s.1) = sev (μ c φ) v t
  | .leaf a, Y, h, v => by
    rw [FreeGrL.shEv_leaf]
    exact app_unitL φ h.symm v
  | .node (BinGen.op g) ch, Y, h, v => by
    have hnd : (STree.node (BinGen.op g) ch).labels.Nodup := h ▸ Y.nodup
    obtain ⟨m₀, hm₀⟩ := exists_mem_labels (ch 0)
    obtain ⟨m₁, hm₁⟩ := exists_mem_labels (ch 1)
    have h01 : ∀ x ∈ (ch 0).labels, x ∉ (ch 1).labels := fun x hx =>
      not_mem_of_node hnd (show (0 : Fin 2) ≠ 1 by decide) hx
    have hne : m₀ ≠ m₁ := fun e => h01 m₀ hm₀ (e ▸ hm₁)
    have hm₁₀ : m₁ ∉ (ch 0).labels := fun hx => h01 m₁ hx hm₁
    have hnd₀ := nodup_of_node hnd 0
    have hnd₁ := nodup_of_node hnd 1
    -- the tree with the second child cut down to its leaf `m₁`
    let t₁ : STree (BinGen G) := STree.node (BinGen.op g) ![ch 0, STree.leaf m₁]
    have hl₁ : t₁.labels = (ch 0).labels + {m₁} := by
      simp [t₁, Fin.sum_univ_two]
    have hnd₁' : t₁.labels.Nodup := by
      rw [hl₁, Multiset.nodup_add]
      exact ⟨hnd₀, Multiset.nodup_singleton _, Multiset.disjoint_singleton.2 hm₁₀⟩
    have ht : STree.node (BinGen.op g) ch = t₁.subst (update STree.leaf m₁ (ch 1)) := by
      simp only [t₁, subst_node]
      congr 1
      funext j
      fin_cases j
      · show ch 0 = (ch 0).subst _
        conv_lhs => rw [← subst_leaf (ch 0)]
        exact subst_congr _ fun a ha => by
          rw [update_of_ne (show a ≠ m₁ from fun e => hm₁₀ (e ▸ ha))]
      · show ch 1 = update STree.leaf m₁ (ch 1) m₁
        rw [update_self]
    have hm₁Y : m₁ ∈ t₁.labels.toFinset := by
      rw [Multiset.mem_toFinset, hl₁]
      simp
    have hd₁ : Disjoint (t₁.labels.toFinset.erase m₁) (ch 1).labels.toFinset := by
      rw [Finset.disjoint_left]
      intro x hx hx₁
      rw [Finset.mem_erase, Multiset.mem_toFinset, hl₁] at hx
      rw [Multiset.mem_toFinset] at hx₁
      rcases Multiset.mem_add.1 hx.2 with hx' | hx'
      · exact h01 x hx' hx₁
      · exact hx.1 (Multiset.mem_singleton.1 hx')
    rw [shEv_tree_congr c ht Y h (ht ▸ h), app_subst c hc φ t₁ (ch 1) (labels_eq_toFinset hnd₁')
      (labels_eq_toFinset hnd₁) hm₁Y hd₁ Y _ v, app_shEv (ch 1) _ (labels_eq_toFinset hnd₁) v]
    -- the corolla with both children cut down to leaves
    set v₁ := update v m₁ (sev (μ c φ) v (ch 1))
    let t₀ : STree (BinGen G) := STree.node (BinGen.op g) ![STree.leaf m₀, STree.leaf m₁]
    have hl₀ : t₀.labels = {m₀, m₁} := by
      simp [t₀, Fin.sum_univ_two]
    have hnd₀' : t₀.labels.Nodup := by
      rw [hl₀]
      simp [hne]
    have ht₁ : t₁ = t₀.subst (update STree.leaf m₀ (ch 0)) := by
      simp only [t₀, t₁, subst_node]
      congr 1
      funext j
      fin_cases j
      · show ch 0 = update STree.leaf m₀ (ch 0) m₀
        rw [update_self]
      · show STree.leaf m₁ = update STree.leaf m₀ (ch 0) m₁
        rw [update_of_ne hne.symm]
    have hm₀Y : m₀ ∈ t₀.labels.toFinset := by
      rw [Multiset.mem_toFinset, hl₀]
      simp
    have hd₀ : Disjoint (t₀.labels.toFinset.erase m₀) (ch 0).labels.toFinset := by
      rw [Finset.disjoint_left]
      intro x hx hx₀
      rw [Finset.mem_erase, Multiset.mem_toFinset, hl₀] at hx
      rw [Multiset.mem_toFinset] at hx₀
      have : x = m₁ := by simpa [hx.1] using hx.2
      exact hm₁₀ (this ▸ hx₀)
    rw [shEv_tree_congr c ht₁ _ (labels_eq_toFinset hnd₁') (ht₁ ▸ labels_eq_toFinset hnd₁'),
      app_subst c hc φ t₀ (ch 0) (labels_eq_toFinset hnd₀') (labels_eq_toFinset hnd₀) hm₀Y hd₀
        _ _ v₁, app_shEv (ch 0) _ (labels_eq_toFinset hnd₀) v₁,
      app_corolla c φ g hne _ (labels_eq_toFinset hnd₀')]
    have hv₁ : sev (μ c φ) v₁ (ch 0) = sev (μ c φ) v (ch 0) :=
      sev_congr _ (ch 0) fun a ha => update_of_ne (show a ≠ m₁ from fun e => hm₁₀ (e ▸ ha)) _ _
    rw [hv₁, update_self, update_of_ne hne.symm]
    show μ c φ g _ (update v m₁ _ m₁) = _
    rw [update_self]
    rfl

/-- **The values of the binary-tree basis**: the basis vector of a binary shuffle tree `t`, under
`φ`, takes at the inputs `w` the value of `t` with the leaf `a` valued `w a`. -/
theorem app_tBasis {n : ℕ} (t : {t // t ∈ LTree.monomials (E := G) (Fintype.card (Fin n))})
    (w : Fin n → V) :
    sgEv (φ.app (Fin n) (ShuffleBarSym.tBasis c hc (Fin n) t)) w
      = lev (μ c φ) (fun a => if h : a < n then w ⟨a, h⟩ else 0) t.1 := by
  rw [ShuffleBarSym.tBasis_apply, FreeGrL.shuffleBasis_apply, φ.app_map, sgEv_map]
  have hw : w ∘ (FreeGrL.posEquiv (Fin n)).symm
      = fun s => (fun a => if h : a < n then w ⟨a, h⟩ else 0) s.1 := by
    funext s
    have hs : s.1 = (((FreeGrL.posEquiv (Fin n)).symm s : Fin n) : ℕ) := by
      conv_lhs => rw [← (FreeGrL.posEquiv (Fin n)).apply_symm_apply s]
      rw [FreeGrL.posEquiv_apply, opos_fin]
    have hlt : s.1 < n := hs ▸ Fin.is_lt _
    simp only [comp_apply, dif_pos hlt]
    congr 1
    exact Fin.ext hs.symm
  rw [hw]
  exact (app_shEv c hc φ (LTree.binMonoEquiv _ t).1 _ (LTree.binMonoEquiv _ t).2.2
    (fun a => if h : a < n then w ⟨a, h⟩ else 0)).trans (sev_toBinSTree _ _ t.1)

end Model

/-! ## The relators of a model -/

section Ker

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {G : Type} [Fintype G] [DecidableEq G]
  (c : ∀ k, Module.Basis (BinGen G k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen G k), GrSpecies.par (R := K) false (c k β) = c k β)
  {V : Type v} [AddCommGroup V] [Module K V]
  (φ : GrOperadHom K (FreeGrL K E) (SymGr (EndOp K V)))

/-- **The relators of a model**: the operations of arity three killed by `φ`, and none in the
other arities. -/
def kerRel (n : ℕ) : Set (FreeGrL K E (Fin n)) := {x | n = 3 ∧ φ.app (Fin n) x = 0}

/-- The relators of a model are concentrated in arity three. -/
lemma kerRel_ne {n : ℕ} (hn : n ≠ 3) : kerRel φ n = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hx => hn hx.1

/-- **The relators of a model are stable under the permutations**, `φ` being equivariant. -/
lemma kerRel_perm (σ : Equiv.Perm (Fin 3)) (x : FreeGrL K E (Fin 3)) (hx : x ∈ kerRel φ 3) :
    GrOperad.map (R := K) σ x ∈ Submodule.span K (kerRel φ 3) :=
  Submodule.subset_span ⟨rfl, by rw [φ.app_map, hx.2, map_zero]⟩

/-- The leaves `0, 1, 2` valued by three inputs. -/
def ext3 (w : Fin 3 → V) (a : ℕ) : V := if h : a < 3 then w ⟨a, h⟩ else 0

/-- The monomials of arity three, as the indices of the basis `ShuffleBarSym.tBasis`. -/
def monoEquiv : {t // t ∈ LTree.monomials (E := G) (Fintype.card (Fin 3))} ≃ LTree.Mono G 3 :=
  Equiv.subtypeEquivRight fun t => by rw [Fintype.card_fin]

include hc in
lemma sgEv_app_sum (a : {t // t ∈ LTree.monomials (E := G) (Fintype.card (Fin 3))} → K)
    (w : Fin 3 → V) :
    sgEv (φ.app (Fin 3) (∑ t, a t • ShuffleBarSym.tBasis c hc (Fin 3) t)) w
      = ∑ σ : LTree.Mono G 3, a (monoEquiv.symm σ) • lev (μ c φ) (ext3 w) σ.1 := by
  rw [map_sum, sgEv_sum]
  refine Fintype.sum_equiv monoEquiv _ _ fun t => ?_
  rw [map_smul, sgEv_smul, app_tBasis c hc φ]
  rfl

/-- **The shuffle relators of a model**: a coordinate vector `v` on the monomials of arity three
lies in `Rsh` of the relators of the model iff the combination `∑ v σ • σ` of the values of the
monomials vanishes on every family of three inputs. -/
theorem mem_Rsh_kerRel (v : LTree.Mono G 3 → K) :
    v ∈ ShuffleBarSym.Rsh c hc (kerRel φ) ↔
      ∀ w : Fin 3 → V, ∑ σ : LTree.Mono G 3, v σ • lev (μ c φ) (ext3 w) σ.1 = 0 := by
  let b := ShuffleBarSym.tBasis c hc (Fin 3)
  let F : FreeGrL K E (Fin 3) →ₗ[K] (LTree.Mono G 3 → K) :=
    LinearMap.pi fun σ => b.coord (monoEquiv.symm σ)
  have hRsh : ShuffleBarSym.Rsh c hc (kerRel φ) = (LinearMap.ker (φ.app (Fin 3))).map F := by
    rw [ShuffleBarSym.Rsh, ← Submodule.span_eq (Submodule.map F _), Submodule.map_coe]
    congr 1
    ext x
    simp only [Set.mem_image, SetLike.mem_coe, LinearMap.mem_ker]
    refine exists_congr fun y => and_congr (by simp [kerRel]) ?_
    refine Iff.of_eq (congrArg (· = x) (funext fun σ => ?_))
    rfl
  rw [hRsh, Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩ w
    rw [LinearMap.mem_ker] at hx
    have h0 := sgEv_app_sum c hc φ (fun t => b.repr x t) w
    rw [b.sum_repr, hx] at h0
    rw [← h0.symm.trans (sgEv_zero w)]
    rfl
  · intro h
    refine ⟨b.equivFun.symm (v ∘ monoEquiv), ?_, funext fun σ => ?_⟩
    · rw [LinearMap.mem_ker, eq_zero_iff]
      intro w
      rw [Module.Basis.equivFun_symm_apply, sgEv_app_sum c hc φ, ← h w]
      refine Finset.sum_congr rfl fun σ _ => ?_
      simp
    · show b.coord _ _ = v σ
      rw [Module.Basis.coord_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
      simp

/-- **The bridge for the relators of a model**: over a field of characteristic zero, the operad
presented by the relators of a model is Koszul iff the shuffle operad presented by their shuffle
relators is. -/
theorem isKoszul_kerRel_iff [CharZero K] :
    Koszul.IsKoszul K E (kerRel φ) ↔ ShuffleBar.IsKoszul K (ShuffleBarSym.Rsh c hc (kerRel φ)) :=
  ShuffleBarSym.isKoszul_iff_shuffle c hc (fun _ hn => kerRel_ne φ hn) (kerRel_perm φ)

end Ker

/-! ## The regular representation of `𝔖₂` in arity two -/

section Reg2

variable (K : Type u) [CommRing K]

/-- **The regular representation of `𝔖₂` in arity two**: on `A`, the functions on the
numberings `Fin 2 ≃ A`, zero unless `A` has two elements. -/
@[nolint unusedArguments]
def Reg2 (A : Type) [Fintype A] [DecidableEq A] : Type u := (Fin 2 ≃ A) → K

instance (A : Type) [Fintype A] [DecidableEq A] : AddCommGroup (Reg2 K A) :=
  inferInstanceAs (AddCommGroup ((Fin 2 ≃ A) → K))

instance (A : Type) [Fintype A] [DecidableEq A] : Module K (Reg2 K A) :=
  inferInstanceAs (Module K ((Fin 2 ≃ A) → K))

variable {K} in
/-- The value of an element of `Reg2 K A` at a numbering. -/
def Reg2.val {A : Type} [Fintype A] [DecidableEq A] (f : Reg2 K A) (τ : Fin 2 ≃ A) : K := f τ

/-- Relabelling: precompose the numberings with the inverse bijection. -/
def Reg2.map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B) :
    Reg2 K A →ₗ[K] Reg2 K B :=
  LinearMap.funLeft K K fun τ : Fin 2 ≃ B => τ.trans e.symm

/-- The parity projections: everything is even. -/
def Reg2.par {A : Type} [Fintype A] [DecidableEq A] (b : Bool) : Reg2 K A →ₗ[K] Reg2 K A :=
  cond b 0 LinearMap.id

/-- **The regular representation of `𝔖₂` is an even graded linear species.** -/
instance Reg2.instGrSpecies : GrSpecies K (Reg2 K) where
  map e := Reg2.map K e
  map_refl x := funext fun τ => congrArg x (Equiv.ext fun _ => rfl)
  map_trans e f x := funext fun τ => congrArg x (Equiv.ext fun _ => rfl)
  par b := Reg2.par K b
  par_add x := by simp [Reg2.par]
  par_par b b' x := by cases b <;> cases b' <;> simp [Reg2.par]
  map_par e b x := by cases b <;> simp [Reg2.par]

variable {K}

@[simp] lemma Reg2.val_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) (f : Reg2 K A) (τ : Fin 2 ≃ B) :
    (SymSpecies.map (R := K) e f).val τ = f.val (τ.trans e.symm) := rfl

@[simp] lemma Reg2.val_add {A : Type} [Fintype A] [DecidableEq A] (f g : Reg2 K A)
    (τ : Fin 2 ≃ A) : (f + g).val τ = f.val τ + g.val τ := rfl

@[simp] lemma Reg2.val_smul {A : Type} [Fintype A] [DecidableEq A] (a : K) (f : Reg2 K A)
    (τ : Fin 2 ≃ A) : (a • f).val τ = a * f.val τ := rfl

/-- Every vector is even. -/
lemma Reg2.par_false {A : Type} [Fintype A] [DecidableEq A] (f : Reg2 K A) :
    GrSpecies.par (R := K) false f = f := rfl

omit [CommRing K] in
/-- `Reg2 K (Fin k)` vanishes for `k ≠ 2`. -/
lemma Reg2.subsingleton {k : ℕ} (hk : k ≠ 2) : Subsingleton (Reg2 K (Fin k)) := by
  haveI : IsEmpty (Fin 2 ≃ Fin k) :=
    ⟨fun e => hk (by simpa using (Fintype.card_congr e).symm)⟩
  exact inferInstanceAs (Subsingleton ((Fin 2 ≃ Fin k) → K))

/-- The two numberings of `Fin 2`. -/
lemma univ_perm_two :
    (Finset.univ : Finset (Fin 2 ≃ Fin 2)) = {Equiv.refl _, Equiv.swap 0 1} := by
  decide

variable {V : Type v} [AddCommGroup V] [Module K V] (m : V →ₗ[K] V →ₗ[K] V)

/-- **The model map** on `A`: a function on the numberings `τ` to the sum of the bilinear maps `m`
applied to the inputs `τ 0, τ 1`. -/
noncomputable def modelApp (A : Type) [Fintype A] [DecidableEq A] :
    Reg2 K A →ₗ[K] SymGr (EndOp K V) A where
  toFun f := ∑ τ, f.val τ • EndOp.mapL K V τ (FreeBin.bilinOp m)
  map_add' f g := by
    simp only [Reg2.val_add, add_smul]
    exact Finset.sum_add_distrib
  map_smul' a f := by
    simp only [Reg2.val_smul, mul_smul, RingHom.id_apply, Finset.smul_sum]
    rfl

lemma sgEv_modelApp {A : Type} [Fintype A] [DecidableEq A] (f : Reg2 K A) (w : A → V) :
    sgEv (modelApp m A f) w = ∑ τ, f.val τ • m (w (τ 0)) (w (τ 1)) := by
  show sgEv (∑ τ, f.val τ • EndOp.mapL K V τ (FreeBin.bilinOp m)) w = _
  rw [sgEv_sum]
  rfl

/-- **The model morphism of graded linear species** `Reg2 K → SymGr (EndOp K V)`. -/
noncomputable def modelHom : GrSpeciesHom K (Reg2 K) (SymGr (EndOp K V)) where
  app := modelApp m
  app_map e f := by
    refine MultilinearMap.ext fun w => ?_
    show sgEv (modelApp m _ _) w = sgEv (GrOperad.map (R := K) e (modelApp m _ f)) w
    rw [sgEv_map, sgEv_modelApp, sgEv_modelApp]
    let e' : (Fin 2 ≃ _) ≃ (Fin 2 ≃ _) :=
      ⟨fun τ => τ.trans e.symm, fun τ => τ.trans e, fun τ => by ext; simp, fun τ => by ext; simp⟩
    exact Fintype.sum_equiv e' _ _ fun τ => by
      simp only [Reg2.val_map, comp_apply, e', Equiv.coe_fn_mk, Equiv.trans_apply,
        Equiv.apply_symm_apply]
  app_par b f := by
    cases b
    · rfl
    · show modelApp m _ (Reg2.par K true f) = 0
      simp [Reg2.par]

/-- **The model morphism of graded operads** `FreeGrL K (Reg2 K) → SymGr (EndOp K V)`. -/
noncomputable def model : GrOperadHom K (FreeGrL K (Reg2 K)) (SymGr (EndOp K V)) :=
  FreeGrL.homEquiv.symm (modelHom m)

/-- **The operation of a generator in the model**, on two inputs. -/
lemma μ_model {G : Type} (c : ∀ k, Module.Basis (BinGen G k) K (Reg2 K (Fin k))) (g : G)
    (x y : V) :
    μ c (model m) g x y = (c 2 (BinGen.op g)).val (Equiv.refl _) • m x y
      + (c 2 (BinGen.op g)).val (Equiv.swap 0 1) • m y x := by
  rw [μ, model, FreeGrL.homEquiv_symm_ι]
  show sgEv (modelApp m _ _) _ = _
  rw [sgEv_modelApp, univ_perm_two, Finset.sum_pair (by decide)]
  rfl

end Reg2

end SymPresB

end Operad
