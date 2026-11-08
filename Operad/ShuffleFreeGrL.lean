/-
# The shuffle basis of the free graded operad

Step (2a) of the bridge between symmetric and shuffle operads for presentations by a graded linear
species (Dotsenko–Khoroshkin). Let `W` be a graded linear species over a commutative ring `R`
with, in each arity `k`, a basis `b k` of `W (Fin k)` indexed by `B k` and **homogeneous** of
parities `p k : B k → Bool` (`GrSpecies.par (p k β) (b k β) = b k β`), and no basis vectors in
arity zero (`IsEmpty (B 0)`). **The free graded operad `FreeGrL R W` has, on every finite linear
order `A`, a basis indexed by the shuffle monomials `SMono B (Finset.range |A|)`**
(`Operad.FreeGrL.shuffleBasis`, `Operad.FreeGrL.shuffleEquiv`).

* **Leaves.** A finite set `Y` of natural numbers is a finite linear order `Operad.Lab Y`; a tree
  whose leaves are the elements of `Y`, each once, is evaluated in `FreeGrL R W (Lab Y)`.
* **The evaluation of a tree** (`Operad.FreeGrL.shEv`): a leaf is the unit, and a vertex labelled
  `β` with children `c 0, …, c (k - 1)` is the basis vector `b k β` grafted with the evaluations of
  its children, read from left to right: the total composite `FreeGrL.graft` of the generator
  `b k β ⊗ (c 0, …, c (k - 1))` of `W ∘ T(W)`, its inputs in the standard order of `Fin k`
  (`Operad.FreeGrL.shEv_node`, `Operad.FreeGrL.shEv_leaf`). A corolla is a relabelled generator
  `ι (b k β)` (`Operad.FreeGrL.shEv_corolla`), and an evaluation is homogeneous of the parity
  `|t|` of its vertices (`Operad.STree.vpar`, `Operad.FreeGrL.par_shEv`).
* **The sign convention** is that of the trees of the free graded operad (`FreeGr`): the
  evaluation of a tree is the composite of its vertices in the preorder, reading the tree from the
  root, depth first and left to right. So **composing evaluations at a leaf costs the Koszul sign
  of the vertices moved across** (`Operad.FreeGrL.comp_shEv`):

    `ev(t) ∘ₘ ev(t') = σ(|t'| · aft_t(m)) ev(t[m := t'])`,

  `aft_t(m)` the parity of the vertices of `t` met after the leaf `m` in the preorder
  (`Operad.STree.vaft`), `t[m := t']` the substitution `t.subst (update leaf m t')`, and the
  inputs of the composite named by their values (`Operad.FreeGrL.sval`). With `t` a corolla, this
  is the grafting of an evaluation onto an input of a vertex, `ι (b k β) ∘ᵢ ev(t')`.
* **Coordinates** (`Operad.FreeGrL.shCoord`), by recursion on trees through the root
  decomposition `ρ : T(W) → W ∘ T(W)` (`FreeGrL.root`): the coefficient of the unit for a leaf,
  and for a vertex, on a generator of `W ∘ T(W)` whose inputs are matched with the children, the
  reordering sign to the order of the children, the coordinate of the outer operation in the
  basis and the coordinates of the inner operations (`Operad.FreeGrL.compFun`, a linear map out of
  the graded composite by `Operad.FreeGrL.compFun_respects`). **The coordinates are dual to the
  evaluations of the shuffle trees** (`Operad.FreeGrL.shCoord_shEv`), so these are linearly
  independent (`Operad.FreeGrL.linearIndependent_shEv`), with or without basis vectors in arity
  zero.
* **Spanning** (`Operad.FreeGrL.shSpan_eq_top`), by the induction principle of `T(W)`
  (`FreeGrL.submodule_eq_top`) on the operations lying in the span of the shuffle trees however
  their inputs are named by natural numbers (`Operad.FreeGrL.shSpanFam`): a generator is a
  combination of corollas, and a composite of two evaluations of shuffle trees is one, by
  `Operad.FreeGrL.comp_shEv` with the input composed at named by the least leaf of the inner tree
  (`Operad.FreeGrL.isShuffle_subst_update`, `Operad.FreeGrL.labels_subst_update`).
* **The basis**: `Operad.FreeGrL.shBasisLab` on `Lab Y`, and `Operad.FreeGrL.shuffleBasis` on a
  finite linear order through the positions of its elements (`Operad.FreeGrL.posEquiv`), with
  `Operad.FreeGrL.shuffleBasis_apply` (a basis vector is the relabelled evaluation of its tree),
  `Operad.FreeGrL.par_shuffleBasis` (it is homogeneous of the parity of its vertices),
  `Operad.FreeGrL.finrank_eq_card`, and the composition of basis vectors at the least leaf of the
  inner one, a signed basis vector (`Operad.FreeGrL.comp_shBasisLab`).

Not proved here: the agreement with `FreeL.shuffleBasis` through `FreeGrL.freeLEquiv` for even
generators.
-/
import Operad.FreeGrGraft
import Operad.ShuffleFreeAny

universe u v w

namespace Operad

open Function Sym GerBV GrComposite

/-- **The leaves `Y`**, as a type: a finite linear order. -/
abbrev Lab (Y : Finset ℕ) : Type := {x // x ∈ Y}

namespace STree

variable {B : ℕ → Type w} (p : ∀ k, B k → Bool)

/-! ## Parities of trees -/

/-- **The parity of a tree**: the sum of the parities of its vertices. -/
def vpar : STree B → Bool
  | leaf _ => false
  | node β c => xor (p _ β) (GrEnd.tot fun j => vpar (c j))

open Classical in
/-- **The parity after a leaf**: the sum of the parities of the vertices met after the leaf `m` in
the preorder, reading the tree from the root, depth first and left to right. -/
noncomputable def vaft : STree B → ℕ → Bool
  | leaf _, _ => false
  | node _ c, m => GrEnd.tot fun j => if m ∈ (c j).labels then vaft (c j) m
      else if ∃ j', j' < j ∧ m ∈ (c j').labels then vpar p (c j) else false

@[simp] lemma vpar_leaf (a : ℕ) : vpar p (leaf a : STree B) = false := rfl

lemma vpar_node {k : ℕ} (β : B k) (c : Fin k → STree B) :
    vpar p (node β c) = xor (p k β) (GrEnd.tot fun j => vpar p (c j)) := rfl

@[simp] lemma vaft_leaf (a m : ℕ) : vaft p (leaf a : STree B) m = false := rfl

open Classical in
lemma vaft_node {k : ℕ} (β : B k) (c : Fin k → STree B) (m : ℕ) :
    vaft p (node β c) m = GrEnd.tot fun j => if m ∈ (c j).labels then vaft p (c j) m
      else if ∃ j', j' < j ∧ m ∈ (c j').labels then vpar p (c j) else false := rfl

/-! ## The children of a vertex -/

variable {k : ℕ} {β : B k} {c : Fin k → STree B} {Y : Finset ℕ}

lemma exists_child (h : (node β c).labels = Y.val) (s : Lab Y) : ∃ j, s.1 ∈ (c j).labels :=
  mem_labels_node.1 (by rw [h]; exact s.2)

/-- **The owner of a leaf**: the child it lies in. -/
noncomputable def own (h : (node β c).labels = Y.val) (s : Lab Y) : Fin k :=
  (exists_child h s).choose

lemma mem_own (h : (node β c).labels = Y.val) (s : Lab Y) : s.1 ∈ (c (own h s)).labels :=
  (exists_child h s).choose_spec

lemma nodup_node (h : (node β c).labels = Y.val) : (node β c).labels.Nodup := h ▸ Y.nodup

lemma child_eq (h : (node β c).labels = Y.val) {j j' : Fin k} {x : ℕ} (hx : x ∈ (c j).labels)
    (hx' : x ∈ (c j').labels) : j = j' :=
  by_contra fun hne => not_mem_of_node (nodup_node h) hne hx hx'

lemma own_eq (h : (node β c).labels = Y.val) {s : Lab Y} {j : Fin k} (hs : s.1 ∈ (c j).labels) :
    own h s = j :=
  child_eq h (mem_own h s) hs

lemma mem_of_child (h : (node β c).labels = Y.val) {j : Fin k} {x : ℕ} (hx : x ∈ (c j).labels) :
    x ∈ Y := by
  have hx' : x ∈ (node β c).labels := mem_labels_node.2 ⟨j, hx⟩
  rw [h] at hx'
  exact hx'

/-- **The leaves of a child**, as a finite set. -/
abbrev cLab (c : Fin k → STree B) (j : Fin k) : Finset ℕ := (c j).labels.toFinset

lemma labels_child (h : (node β c).labels = Y.val) (j : Fin k) :
    (c j).labels = (cLab c j).val := by
  rw [Multiset.toFinset_val, Multiset.Nodup.dedup (nodup_of_node (nodup_node h) j)]

/-- **The leaves of a child are the leaves it owns.** -/
noncomputable def childEquiv (h : (node β c).labels = Y.val) (j : Fin k) :
    Lab (cLab c j) ≃ Fib (own h) j where
  toFun x := ⟨⟨x.1, mem_of_child h (Multiset.mem_toFinset.1 x.2)⟩,
    own_eq h (Multiset.mem_toFinset.1 x.2)⟩
  invFun s := ⟨s.1.1, Multiset.mem_toFinset.2 (by have := mem_own h s.1; rwa [s.2] at this)⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma childEquiv_val (h : (node β c).labels = Y.val) (j : Fin k) (x : Lab (cLab c j)) :
    (childEquiv h j x).1.1 = x.1 := rfl

end STree

/-! ## Evaluating trees in the free graded operad -/

namespace FreeGrL

variable {R : Type u} [CommRing R]
  {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)] [GrSpecies R W]
  {B : ℕ → Type w} (b : ∀ k, Module.Basis (B k) R (W (Fin k)))

open STree

/-- **The evaluation of a tree** with leaves `Y` in the free graded operad: a leaf is the unit, and
a vertex labelled by `β` is the basis vector `b β` grafted with the evaluations of its children,
read from left to right. -/
noncomputable def shEv : (t : STree B) → (Y : Finset ℕ) → t.labels = Y.val → FreeGrL R W (Lab Y)
  | .leaf _, Y, _ => unitL R W (Lab Y)
  | .node β c, Y, h => graft R W (Lab Y) (mk R (ownGen (LinOrd.std _) (b _ β) (own h)
      fun j => GrOperad.map (R := R) (childEquiv h j) (shEv (c j) (cLab c j) (labels_child h j))))

lemma shEv_leaf (a : ℕ) (Y : Finset ℕ) (h : (STree.leaf a : STree B).labels = Y.val) :
    shEv b (.leaf a) Y h = unitL R W (Lab Y) := by
  rw [shEv]

lemma shEv_node {k : ℕ} (β : B k) (c : Fin k → STree B) (Y : Finset ℕ)
    (h : (STree.node β c).labels = Y.val) :
    shEv b (.node β c) Y h = graft R W (Lab Y) (mk R (ownGen (LinOrd.std _) (b _ β) (own h)
      fun j => GrOperad.map (R := R) (childEquiv h j) (shEv b (c j) (cLab c j)
        (labels_child h j)))) := by
  rw [shEv]

/-- **The evaluation along equal trees and leaves.** -/
lemma map_shEv {t t' : STree B} (ht : t = t') {Y Y' : Finset ℕ} (hY : Y = Y')
    (h : t.labels = Y.val) (h' : t'.labels = Y'.val) (e : Lab Y ≃ Lab Y')
    (he : ∀ x, (e x).1 = x.1) :
    GrOperad.map (R := R) e (shEv b t Y h) = shEv b t' Y' h' := by
  subst ht hY
  rw [show e = Equiv.refl _ from Equiv.ext fun x => Subtype.ext (he x), GrOperad.map_refl]

/-- **Grafting preserves parities.** -/
lemma par_graft {S : Type} [Fintype S] [DecidableEq S] (q : Bool)
    (ω : GrComposite R W (FreeGrL R W) S) :
    GrOperad.par (R := R) q (graft R W S ω) = graft R W S (GrComposite.par R W (FreeGrL R W) q ω)
    := by
  have hu : unitCoeffL R W S (GrOperad.par (R := R) q (graft R W S ω)) = 0 := by
    rw [unitCoeffL_par, unitCoeffL_graft]
    cases q <;> rfl
  rw [← secC_of_unitCoeff hu, ← graft_root, root_par, root_graft]

section Par

variable {p : ∀ k, B k → Bool}
  (hb : ∀ k (β : B k), GrSpecies.par (R := R) (p k β) (b k β) = b k β)
include hb

/-- **The evaluation of a tree is homogeneous**, of the parity of its vertices. -/
theorem par_shEv : ∀ (t : STree B) (Y : Finset ℕ) (h : t.labels = Y.val),
    GrOperad.par (R := R) (vpar p t) (shEv b t Y h) = shEv b t Y h
  | .leaf _, Y, h => by
    rw [vpar_leaf, shEv_leaf, par_unitL]
    rfl
  | .node β c, Y, h => by
    rw [vpar_node, shEv_node, par_graft, par_mk, parFun_hom _ _ (hb _ β)
      (c := fun j => vpar p (c j)) (fun j => ?_), if_pos rfl]
    show GrOperad.par (R := R) _ (GrOperad.map (R := R) _ _) = _
    rw [← GrOperad.map_par, par_shEv (c j)]

end Par

/-! ## Coordinates -/

/-- A product of values on a family, at an updated coordinate, when the value there is additive. -/
lemma prod_update_add {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type*} [∀ i, Add (M i)]
    (F : ∀ i, M i → R) (y : ∀ i, M i) (i : ι) (z z' : M i)
    (hF : F i (z + z') = F i z + F i z') :
    ∏ j, F j (update y i (z + z') j) = ∏ j, F j (update y i z j) + ∏ j, F j (update y i z' j) := by
  have hu : ∀ w : M i, (fun j => F j (update y i w j)) = update (fun j => F j (y j)) i (F i w) :=
    fun w => funext fun j => apply_update F y i w j
  rw [hu, hu, hu, Finset.prod_update_of_mem (Finset.mem_univ i),
    Finset.prod_update_of_mem (Finset.mem_univ i), Finset.prod_update_of_mem (Finset.mem_univ i),
    hF, add_mul]

/-- A product of values on a family, at an updated coordinate, when the value there is
homogeneous. -/
lemma prod_update_smul {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type*} [∀ i, SMul R (M i)]
    (F : ∀ i, M i → R) (y : ∀ i, M i) (i : ι) (r : R) (z : M i) (hF : F i (r • z) = r * F i z) :
    ∏ j, F j (update y i (r • z) j) = r * ∏ j, F j (update y i z j) := by
  have hu : ∀ w : M i, (fun j => F j (update y i w j)) = update (fun j => F j (y j)) i (F i w) :=
    fun w => funext fun j => apply_update F y i w j
  rw [hu, hu, Finset.prod_update_of_mem (Finset.mem_univ i),
    Finset.prod_update_of_mem (Finset.mem_univ i), hF, mul_assoc]

section Coord

variable (p : ∀ k, B k → Bool) {k : ℕ} {β : B k} {c : Fin k → STree B} {Y : Finset ℕ}
  (h : (STree.node β c).labels = Y.val) (ψ : ∀ j, FreeGrL R W (Lab (cLab c j)) →ₗ[R] R)

/-- The coordinate of a child, on the leaves it owns, after projecting to its parity. -/
noncomputable def childCoord (j : Fin k) : FreeGrL R W (Fib (own h) j) →ₗ[R] R :=
  ψ j ∘ₗ GrOperad.map (R := R) (childEquiv h j).symm ∘ₗ GrOperad.par (R := R) (vpar p (c j))

/-- The leaves owned by an input, matched with a child. -/
def fibNu {A : Type} (f : Lab Y → A) (ν : A ≃ Fin k) (hν : ∀ s, ν (f s) = own h s) (a : A) :
    Fib f a ≃ Fib (own h) (ν a) :=
  Equiv.subtypeEquivRight fun s => by rw [← hν s, ν.injective.eq_iff]

/-- **The coefficient of a vertex** with given children coordinates, on a generator of `W ∘ T(W)`
given by owners: for every matching of the inputs with the children, the reordering sign to the
order of the children, the coordinate of the outer operation, and the coordinates of the inner
operations. -/
noncomputable def compOwn {A : Type} [Fintype A] [DecidableEq A] (L : LinOrd A) (m : W A)
    (f : Lab Y → A) (y : ∀ a, FreeGrL R W (Fib f a)) : R :=
  ∑ ν : A ≃ Fin k, if hν : ∀ s, ν (f s) = own h s then
    GrEnd.rsg R L (LinOrd.map ν.symm (LinOrd.std k)) (fun a => vpar p (c (ν a))) *
      ((b k).coord β (SymSpecies.map (R := R) ν m) *
        ∏ a, childCoord p h ψ (ν a) (GrOperad.map (R := R) (fibNu h f ν hν a) (y a)))
    else 0

variable {A : Type} [Fintype A] [DecidableEq A]

lemma compOwn_add_m (L : LinOrd A) (m m' : W A) (f : Lab Y → A) (y : ∀ a, FreeGrL R W (Fib f a)) :
    compOwn b p h ψ L (m + m') f y = compOwn b p h ψ L m f y + compOwn b p h ψ L m' f y := by
  unfold compOwn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  split_ifs with hν
  · rw [map_add, map_add]
    ring
  · rw [add_zero]

lemma compOwn_smul_m (L : LinOrd A) (r : R) (m : W A) (f : Lab Y → A)
    (y : ∀ a, FreeGrL R W (Fib f a)) :
    compOwn b p h ψ L (r • m) f y = r • compOwn b p h ψ L m f y := by
  unfold compOwn
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  split_ifs with hν
  · rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    ring
  · rw [smul_zero]

lemma compOwn_update_add (L : LinOrd A) (m : W A) (f : Lab Y → A)
    (y : ∀ a, FreeGrL R W (Fib f a)) (a : A) (w w' : FreeGrL R W (Fib f a)) :
    compOwn b p h ψ L m f (update y a (w + w'))
      = compOwn b p h ψ L m f (update y a w) + compOwn b p h ψ L m f (update y a w') := by
  unfold compOwn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  split_ifs with hν
  · have key := prod_update_add (fun a' x => childCoord p h ψ (ν a')
      (GrOperad.map (R := R) (fibNu h f ν hν a') x)) y a w w' (by simp only [map_add])
    beta_reduce at key
    rw [key]
    ring
  · rw [add_zero]

lemma compOwn_update_smul (L : LinOrd A) (m : W A) (f : Lab Y → A)
    (y : ∀ a, FreeGrL R W (Fib f a)) (a : A) (r : R) (w : FreeGrL R W (Fib f a)) :
    compOwn b p h ψ L m f (update y a (r • w)) = r • compOwn b p h ψ L m f (update y a w) := by
  unfold compOwn
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  split_ifs with hν
  · have key := prod_update_smul (fun a' x => childCoord p h ψ (ν a')
      (GrOperad.map (R := R) (fibNu h f ν hν a') x)) y a r w
      (by simp only [map_smul, smul_eq_mul])
    beta_reduce at key
    rw [key, smul_eq_mul]
    ring
  · rw [smul_zero]

omit [Fintype A] [DecidableEq A] in
lemma linOrd_map_trans {A' A'' : Type} (e : A ≃ A') (e' : A' ≃ A'') (L : LinOrd A) :
    LinOrd.map (e.trans e') L = LinOrd.map e' (LinOrd.map e L) :=
  LinOrd.ext fun _ _ => Iff.rfl

lemma compOwn_outer {A' : Type} [Fintype A'] [DecidableEq A'] (σ : A' ≃ A) (L : LinOrd A)
    (m : W A') (f : Lab Y → A) (y : ∀ a, FreeGrL R W (Fib f a)) :
    compOwn b p h ψ L (SymSpecies.map (R := R) σ m) f y
      = compOwn b p h ψ (LinOrd.map σ.symm L) m (σ.symm ∘ f)
          (fun a' => GrOperad.map (R := R) (fibOuter σ f a') (y (σ a'))) := by
  unfold compOwn
  refine Fintype.sum_equiv ⟨fun ν => σ.trans ν, fun ν' => σ.symm.trans ν',
    fun ν => by ext; simp, fun ν' => by ext; simp⟩ _ _ fun ν => ?_
  have hiff : (∀ s, ν (f s) = own h s) ↔ ∀ s, (σ.trans ν) ((σ.symm ∘ f) s) = own h s := by
    simp
  by_cases hν : ∀ s, ν (f s) = own h s
  · rw [dif_pos hν]
    erw [dif_pos (hiff.1 hν)]
    have h1 : GrEnd.rsg R (LinOrd.map σ.symm L) (LinOrd.map (σ.trans ν).symm (LinOrd.std k))
        (fun a' => vpar p (c ((σ.trans ν) a')))
        = GrEnd.rsg R L (LinOrd.map ν.symm (LinOrd.std k)) (fun a => vpar p (c (ν a))) := by
      rw [show (σ.trans ν).symm = ν.symm.trans σ.symm from rfl, linOrd_map_trans, GrEnd.rsg_map]
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    have h2 : SymSpecies.map (R := R) (σ.trans ν) m
        = SymSpecies.map (R := R) ν (SymSpecies.map (R := R) σ m) := SymSpecies.map_trans _ _ _
    have h3 : ∏ a', childCoord p h ψ ((σ.trans ν) a')
        (GrOperad.map (R := R) (fibNu h (σ.symm ∘ f) (σ.trans ν) (hiff.1 hν) a')
          (GrOperad.map (R := R) (fibOuter σ f a') (y (σ a'))))
        = ∏ a, childCoord p h ψ (ν a) (GrOperad.map (R := R) (fibNu h f ν hν a) (y a)) :=
      Fintype.prod_equiv σ _ _ fun a' => by
        show childCoord p h ψ (ν (σ a')) _ = _
        rw [← GrOperad.map_trans]
        exact congrArg _ (gmap_congr (fun x => Subtype.ext rfl) _)
    refine Eq.trans ?_ (congrArg₂ (· * ·) h1.symm (congrArg₂ (· * ·)
      (congrArg ((b k).coord β) h2.symm) h3.symm))
    rfl
  · rw [dif_neg hν]
    erw [dif_neg (fun h' => hν (hiff.2 h'))]

lemma compOwn_reorder (L L' : LinOrd A) (m : W A) (f : Lab Y → A)
    (y : ∀ a, FreeGrL R W (Fib f a)) (cc : A → Bool)
    (hy : ∀ a, GrOperad.par (R := R) (cc a) (y a) = y a) :
    compOwn b p h ψ L m f y = GrEnd.rsg R L L' cc • compOwn b p h ψ L' m f y := by
  unfold compOwn
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  split_ifs with hν
  · by_cases hc : ∀ a, cc a = vpar p (c (ν a))
    · rw [show cc = fun a => vpar p (c (ν a)) from funext hc, smul_eq_mul,
        ← GrEnd.rsg_trans L L' (LinOrd.map ν.symm (LinOrd.std k))]
      ring
    · push Not at hc
      obtain ⟨a, ha⟩ := hc
      have h0 : childCoord p h ψ (ν a) (GrOperad.map (R := R) (fibNu h f ν hν a) (y a)) = 0 := by
        simp only [childCoord, LinearMap.coe_comp, Function.comp_apply]
        rw [← hy a]
        simp only [GrOperad.map_par, GrOperad.par_par, if_neg (Ne.symm ha), map_zero]
      rw [Finset.prod_eq_zero (Finset.mem_univ a) h0, mul_zero, mul_zero, mul_zero, smul_zero]
  · rw [smul_zero]

lemma compOwn_congr (L : LinOrd A) (m : W A) {f f' : Lab Y → A} (hf : f = f')
    (y : ∀ a, FreeGrL R W (Fib f a)) :
    compOwn b p h ψ L m f y = compOwn b p h ψ L m f' (fun a =>
      GrOperad.map (R := R) (Equiv.subtypeEquivRight fun s => by rw [hf]) (y a)) := by
  subst hf
  congr 1
  funext a
  rw [show (Equiv.subtypeEquivRight _ : Fib f a ≃ Fib f a) = Equiv.refl _ from
    Equiv.ext fun _ => rfl, GrOperad.map_refl]

/-- **The coefficient of a vertex**, on generators. -/
noncomputable def compFun (g : GrCompGen W (FreeGrL R W) (Lab Y)) : R :=
  compOwn b p h ψ g.L g.m (owner g) (ownY (R := R) g)

/-- **The coordinate of a child on a relabelled evaluation.** -/
lemma childCoord_map {k' : ℕ} {β' : B k'} {c' : Fin k' → STree B}
    (h' : (STree.node β' c').labels = Y.val) (j' : Fin k') (i : Fin k)
    (E : Fib (own h') j' ≃ Fib (own h) i) (hE : ∀ s, (E s).1.1 = s.1.1)
    (hsh : (c' j').labels = (cLab c i).val) :
    childCoord p h ψ i (GrOperad.map (R := R) E (GrOperad.map (R := R) (childEquiv h' j')
      (shEv b (c' j') (cLab c' j') (labels_child h' j'))))
      = ψ i (GrOperad.par (R := R) (vpar p (c i)) (shEv b (c' j') (cLab c i) hsh)) := by
  have hcl : cLab c' j' = cLab c i := by rw [cLab, hsh, Finset.val_toFinset]
  simp only [childCoord, LinearMap.coe_comp, Function.comp_apply]
  rw [← GrOperad.map_par, ← GrOperad.map_par, ← GrOperad.map_trans, ← GrOperad.map_trans,
    GrOperad.map_par, map_shEv b rfl hcl _ hsh _ (fun x => hE (childEquiv h' j' x))]

/-- The coefficient of a vertex on a generator given by owners. -/
lemma compFun_ownGen (L : LinOrd A) (m : W A) (f : Lab Y → A) (y : ∀ a, FreeGrL R W (Fib f a)) :
    compFun b p h ψ (ownGen L m f y) = compOwn b p h ψ L m f y := by
  unfold compFun
  congr 1
  funext a
  show GrOperad.map (R := R) (fibEquiv (ownGen L m f y) a) (y a) = y a
  rw [show fibEquiv (ownGen L m f y) a = Equiv.refl _ from Equiv.ext fun _ => Subtype.ext rfl]
  exact GrOperad.map_refl (R := R) _

lemma compFun_respects : GrCompGen.Respects R (compFun b p h ψ) where
  add_m g m' := compOwn_add_m b p h ψ g.L g.m m' (owner g) (ownY (R := R) g)
  smul_m g r := compOwn_smul_m b p h ψ g.L r g.m (owner g) (ownY (R := R) g)
  add_y g a w w' := by
    show compOwn b p h ψ g.L g.m (owner g) (ownY (R := R) { g with y := update g.y a (w + w') })
      = compOwn b p h ψ g.L g.m (owner g) (ownY (R := R) { g with y := update g.y a w })
        + compOwn b p h ψ g.L g.m (owner g) (ownY (R := R) { g with y := update g.y a w' })
    rw [ownY_update, ownY_update, ownY_update, map_add, compOwn_update_add]
  smul_y g a r w := by
    show compOwn b p h ψ g.L g.m (owner g) (ownY (R := R) { g with y := update g.y a (r • w) })
      = r • compOwn b p h ψ g.L g.m (owner g) (ownY (R := R) { g with y := update g.y a w })
    rw [ownY_update, ownY_update, map_smul, compOwn_update_smul]
  outer := @fun g A _ _ σ m => by
    show compOwn b p h ψ g.L (SymSpecies.map (R := R) σ m) (owner g) (ownY (R := R) g) = _
    rw [compOwn_outer, compFun, compOwn_congr b p h ψ _ m (owner_outer g σ m).symm]
    congr 1
    funext a'
    simp only [ownY, ← GrOperad.map_trans]
    apply gmap_congr
    intro x
    rfl
  inner := @fun g B _ _ τ => by
    show compOwn b p h ψ g.L g.m _ (ownY (R := R) (⟨g.A, B, g.L, g.m,
      fun a => SymSpecies.map (R := R) (τ a) (g.y a),
      (Equiv.sigmaCongrRight τ).symm.trans g.e⟩ : GrCompGen W (FreeGrL R W) (Lab Y)))
      = compFun b p h ψ g
    unfold compFun
    congr 1
    funext a
    apply gmap_comp_congr
    intro x
    exact Subtype.ext (show g.e ⟨a, (τ a).symm (τ a x)⟩ = g.e ⟨a, x⟩ by
      rw [Equiv.symm_apply_apply])
  reorder g L' cc hy := compOwn_reorder b p h ψ g.L L' g.m (owner g) (ownY (R := R) g) cc
    fun a => by
      show GrOperad.par (R := R) (cc a) (GrOperad.map (R := R) _ (g.y a)) = _
      rw [← GrOperad.map_par]
      exact congrArg _ (hy a)

end Coord

/-! ## Coordinates of trees -/

section ShCoord

variable (p : ∀ k, B k → Bool)

/-- **The coordinate of a tree**: for a leaf, the coefficient of the unit; for a vertex, the
coefficient of the vertex in the root decomposition, with the coordinates of the children. -/
noncomputable def shCoord : (t : STree B) → (Y : Finset ℕ) → t.labels = Y.val →
    (FreeGrL R W (Lab Y) →ₗ[R] R)
  | .leaf _, Y, _ => unitCoeffL R W (Lab Y)
  | .node _ c, Y, h => lift (compFun b p h fun j => shCoord (c j) (cLab c j) (labels_child h j))
      (compFun_respects b p h _) ∘ₗ root R W (Lab Y)

lemma shCoord_leaf (a : ℕ) (Y : Finset ℕ) (h : (STree.leaf a : STree B).labels = Y.val) :
    shCoord b p (.leaf a) Y h = unitCoeffL R W (Lab Y) := by
  rw [shCoord]

lemma shCoord_node {k : ℕ} (β : B k) (c : Fin k → STree B) (Y : Finset ℕ)
    (h : (STree.node β c).labels = Y.val) :
    shCoord b p (.node β c) Y h = lift (compFun b p h fun j => shCoord b p (c j) (cLab c j)
      (labels_child h j)) (compFun_respects b p h _) ∘ₗ root R W (Lab Y) := by
  rw [shCoord]

end ShCoord

end FreeGrL

/-! ## Matching children -/

namespace STree

/-- **A strictly monotone permutation of `Fin n` is the identity.** -/
lemma eq_refl_of_strictMono {n : ℕ} (ν : Fin n ≃ Fin n) (hν : StrictMono ν) :
    ν = Equiv.refl _ := by
  have hν' : StrictMono ν.symm := fun a b hab => by
    by_contra hle
    have := hν.monotone (not_lt.1 hle)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    exact absurd hab (not_lt.2 this)
  refine Equiv.ext fun i => le_antisymm ?_ (hν.le_apply)
  have := hν'.le_apply (x := ν i)
  rwa [Equiv.symm_apply_apply] at this

variable {B : ℕ → Type w} {k k' : ℕ} {β : B k} {c : Fin k → STree B} {β' : B k'}
  {c' : Fin k' → STree B} {Y : Finset ℕ}

/-- **Children matched by their leaves have the same leaves.** -/
lemma labels_eq_of_own (h : (node β c).labels = Y.val) (h' : (node β' c').labels = Y.val)
    (ν : Fin k' ≃ Fin k) (hν : ∀ s, ν (own h' s) = own h s) (j : Fin k') :
    (c' j).labels = (c (ν j)).labels := by
  refine (Multiset.Nodup.ext (nodup_of_node (nodup_node h') j)
    (nodup_of_node (nodup_node h) (ν j))).2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · have hs := own_eq h' (s := ⟨x, mem_of_child h' hx⟩) hx
    have hm := mem_own h ⟨x, mem_of_child h' hx⟩
    rwa [← hν, hs] at hm
  · have hs := own_eq h (s := ⟨x, mem_of_child h hx⟩) hx
    rw [← hν] at hs
    have hm := mem_own h' ⟨x, mem_of_child h hx⟩
    rwa [ν.injective hs] at hm

/-- **The children of shuffle trees with the same leaves, matched by their leaves, come in the
same order.** -/
lemma strictMono_of_own (ht : (node β c).IsShuffle) (ht' : (node β' c').IsShuffle)
    (h : (node β c).labels = Y.val) (h' : (node β' c').labels = Y.val) (ν : Fin k' ≃ Fin k)
    (hν : ∀ s, ν (own h' s) = own h s) : StrictMono ν := by
  have hf : ∀ j, (c' j).first = (c (ν j)).first := fun j =>
    first_eq_of_labels_eq (ht'.child j) (ht.child (ν j)) (labels_eq_of_own h h' ν hν j)
  intro j₁ j₂ hj
  have hlt := ht'.mono hj
  simp only [hf] at hlt
  exact ht.mono.lt_iff_lt.1 hlt

end STree

namespace FreeGrL

variable {R : Type u} [CommRing R]
  {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)] [GrSpecies R W]
  {B : ℕ → Type w} (b : ∀ k, Module.Basis (B k) R (W (Fin k)))

open STree

lemma unitCoeffL_unitL_of {Y : Finset ℕ} {a : ℕ} (hY : Y.val = {a}) :
    unitCoeffL R W (Lab Y) (unitL R W (Lab Y)) = 1 := by
  have ha : a ∈ Y := by
    rw [← Finset.mem_val, hY]
    exact Multiset.mem_singleton_self a
  let e : Unit ≃ Lab Y := ⟨fun _ => ⟨a, ha⟩, fun _ => (), fun _ => rfl, fun x => Subtype.ext (by
    have hx := x.2
    rw [← Finset.mem_val, hY, Multiset.mem_singleton] at hx
    exact hx.symm)⟩
  rw [unitL_eq e, unitCoeffL_map, unitCoeffL_one]

lemma root_unitL (A : Type) [Fintype A] [DecidableEq A] : root R W A (unitL R W A) = 0 := by
  rw [unitL, map_sum]
  exact Finset.sum_eq_zero fun e _ => by rw [root_map, root_one, map_zero]

lemma linOrd_map_refl {A : Type} (L : LinOrd A) : LinOrd.map (Equiv.refl A) L = L :=
  LinOrd.ext fun _ _ => Iff.rfl

section Dual

variable {p : ∀ k, B k → Bool}
  (hb : ∀ k (β : B k), GrSpecies.par (R := R) (p k β) (b k β) = b k β)
include hb

/-- **The coordinates are dual to the evaluations** of shuffle trees with the same leaves. -/
theorem shCoord_shEv [DecidableEq (STree B)] :
    ∀ (t : STree B) (Y : Finset ℕ) (h : t.labels = Y.val), t.IsShuffle →
    ∀ (t' : STree B) (h' : t'.labels = Y.val), t'.IsShuffle →
      shCoord b p t Y h (shEv b t' Y h') = if t = t' then 1 else 0
  | .leaf a, Y, h, _, .leaf a', h', _ => by
    rw [shCoord_leaf, shEv_leaf, unitCoeffL_unitL_of h.symm]
    have haa : a = a' := Multiset.singleton_inj.1 (h.trans h'.symm)
    subst haa
    rw [if_pos rfl]
  | .leaf a, Y, h, _, .node β' c', h', _ => by
    rw [shCoord_leaf, shEv_node, unitCoeffL_graft, if_neg (by simp)]
  | .node β c, Y, h, _, .leaf a', h', _ => by
    rw [shCoord_node, shEv_leaf, LinearMap.comp_apply, root_unitL, map_zero, if_neg (by simp)]
  | @STree.node _ k β c, Y, h, ht, @STree.node _ k' β' c', h', ht' => by
    rw [shCoord_node, shEv_node, LinearMap.comp_apply, root_graft, lift_mk, compFun_ownGen]
    unfold compOwn
    by_cases hm : ∃ ν : Fin k' ≃ Fin k, ∀ s, ν (own h' s) = own h s
    · obtain ⟨ν₀, hν₀⟩ := hm
      have hk : k' = k := by simpa using Fintype.card_congr ν₀
      subst hk
      have hrefl : ∀ ν : Fin k' ≃ Fin k', (∀ s, ν (own h' s) = own h s) → ν = Equiv.refl _ :=
        fun ν hν => eq_refl_of_strictMono ν (strictMono_of_own ht ht' h h' ν hν)
      have hown : ∀ s, (Equiv.refl (Fin k')) (own h' s) = own h s := by
        rw [← hrefl ν₀ hν₀]
        exact hν₀
      rw [Finset.sum_eq_single (Equiv.refl _) (fun ν _ hne => dif_neg fun hν =>
        hne (hrefl ν hν)) (fun h0 => absurd (Finset.mem_univ _) h0)]
      set y' : ∀ j, FreeGrL R W (Fib (own h') j) := fun j => GrOperad.map (R := R)
        (childEquiv h' j) (shEv b (c' j) (cLab c' j) (labels_child h' j)) with hy'
      have e1 : GrEnd.rsg R (LinOrd.std k') (LinOrd.map (Equiv.refl (Fin k')).symm
          (LinOrd.std k')) (fun a => vpar p (c ((Equiv.refl (Fin k')) a))) = 1 := by
        rw [show (Equiv.refl (Fin k')).symm = Equiv.refl _ from rfl, linOrd_map_refl,
          GrEnd.rsg_self]
      have e2 : (b k').coord β (SymSpecies.map (R := R) (Equiv.refl (Fin k')) (b k' β'))
          = Finsupp.single β' (1 : R) β := by
        rw [SymSpecies.map_refl, Module.Basis.coord_apply, Module.Basis.repr_self]
      have e3 : ∀ j, childCoord p h (fun j => shCoord b p (c j) (cLab c j) (labels_child h j))
          ((Equiv.refl (Fin k')) j) (GrOperad.map (R := R) (fibNu h (own h') (Equiv.refl _) hown j)
            (y' j)) = if c j = c' j then 1 else 0 := fun j => by
        have hl : (c' j).labels = (c j).labels := labels_eq_of_own h h' _ hown j
        have hsh : (c' j).labels = (cLab c j).val := hl.trans (labels_child h j)
        refine (childCoord_map b p h _ h' j ((Equiv.refl _) j) _ (fun s => rfl) hsh).trans ?_
        show shCoord b p (c j) (cLab c j) (labels_child h j)
          (GrOperad.par (R := R) (vpar p (c j)) (shEv b (c' j) (cLab c j) hsh)) = _
        rw [← par_shEv b hb (c' j) (cLab c j) hsh, GrOperad.par_par]
        by_cases hv : vpar p (c j) = vpar p (c' j)
        · rw [if_pos hv, par_shEv b hb]
          exact shCoord_shEv (c j) (cLab c j) (labels_child h j) (ht.child j) (c' j) hsh
            (ht'.child j)
        · rw [if_neg hv, map_zero, if_neg (fun he => hv (by rw [he]))]
      rw [dif_pos hown]
      refine Eq.trans (congrArg₂ (· * ·) e1 (congrArg₂ (· * ·) e2
        (Finset.prod_congr rfl fun j _ => e3 j))) ?_
      beta_reduce
      by_cases hn : STree.node β c = STree.node β' c'
      · cases hn
        simp
      · rw [if_neg hn]
        by_cases hβ : β' = β
        · subst hβ
          have hc : ∃ j, c j ≠ c' j := by
            by_contra hc
            push Not at hc
            exact hn (by rw [show c = c' from funext hc])
          obtain ⟨j, hj⟩ := hc
          rw [Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj), mul_zero, mul_zero]
        · rw [Finsupp.single_eq_of_ne (Ne.symm hβ), zero_mul, mul_zero]
    · rw [Finset.sum_eq_zero fun ν _ => dif_neg fun hν => hm ⟨ν, hν⟩, if_neg]
      intro heq
      cases heq
      exact hm ⟨Equiv.refl _, fun s => rfl⟩

end Dual

/-! ## Composition -/

/-- **The value of an input of a composite** of operations with inputs labelled by natural numbers.
-/
def sval {Y₁ Y₂ : Finset ℕ} {i : Lab Y₁} : Without (Lab Y₁) i ⊕ Lab Y₂ → ℕ :=
  Sum.elim (fun x => x.1.1) fun x => x.1

@[simp] lemma sval_inl {Y₁ Y₂ : Finset ℕ} {i : Lab Y₁} (x : Without (Lab Y₁) i) :
    sval (Y₂ := Y₂) (Sum.inl x) = x.1.1 := rfl

@[simp] lemma sval_inr {Y₁ Y₂ : Finset ℕ} {i : Lab Y₁} (x : Lab Y₂) :
    sval (i := i) (Sum.inr x) = x.1 := rfl

/-- The values tell the inputs of a composite apart, as soon as they are the values of a set. -/
lemma sval_injective {Y₁ Y₂ Y : Finset ℕ} {i : Lab Y₁} (E : Lab Y ≃ Without (Lab Y₁) i ⊕ Lab Y₂)
    (hE : ∀ x, sval (E x) = x.1) : Function.Injective (sval (Y₂ := Y₂) (i := i)) := by
  intro u v huv
  have huv' : E.symm u = E.symm v := Subtype.ext (by
    rw [← hE (E.symm u), ← hE (E.symm v), Equiv.apply_symm_apply, Equiv.apply_symm_apply, huv])
  exact E.symm.injective huv'

lemma mem_labels_subst {t : STree B} {xs : ℕ → STree B} {a x : ℕ} (ha : a ∈ t.labels)
    (hx : x ∈ (xs a).labels) : x ∈ (t.subst xs).labels := by
  rw [labels_subst]
  exact Multiset.mem_bind.2 ⟨a, ha, hx⟩

section Comp

variable {p : ∀ k, B k → Bool}
  (hb : ∀ k (β : B k), GrSpecies.par (R := R) (p k β) (b k β) = b k β)
include hb

/-- **Composing evaluations of trees**: substituting `t'` for the leaf `m` of `t`, with the Koszul
sign `σ(|t'| · aft_t(m))` of moving the vertices of `t'` across those of `t` after the leaf `m` in
the preorder. The inputs of the composite are named by their values (`E`, `hE`). -/
theorem comp_shEv (t' : STree B) (Y₂ : Finset ℕ) (h₂ : t'.labels = Y₂.val) :
    ∀ (t : STree B) (Y₁ : Finset ℕ) (h₁ : t.labels = Y₁.val) (m : ℕ) (hm : m ∈ Y₁)
      (Y : Finset ℕ) (h : (t.subst (update STree.leaf m t')).labels = Y.val)
      (E : Lab Y ≃ Without (Lab Y₁) ⟨m, hm⟩ ⊕ Lab Y₂) (_ : ∀ x, sval (E x) = x.1),
      GrOperad.comp (R := R) (⟨m, hm⟩ : Lab Y₁) (shEv b t Y₁ h₁) (shEv b t' Y₂ h₂)
        = σ R (vpar p t' && vaft p t m)
          • GrOperad.map (R := R) E (shEv b (t.subst (update STree.leaf m t')) Y h)
  | .leaf a, Y₁, h₁, m, hm, Y, h, E, hE => by
    have hY₁ : Y₁.val = {a} := h₁.symm
    have hma : m = a := by
      have hm' := hm
      rw [← Finset.mem_val, hY₁, Multiset.mem_singleton] at hm'
      exact hm'
    subst hma
    have hs : (STree.leaf m : STree B).subst (update STree.leaf m t') = t' := by
      rw [subst_leaf', update_self]
    have hY : Y = Y₂ := Finset.val_inj.1 (h.symm.trans ((congrArg labels hs).trans h₂))
    subst hY
    have hone : ∀ x : Lab Y₁, x = ⟨m, hm⟩ := fun x => Subtype.ext (by
      have hx := x.2
      rw [← Finset.mem_val, hY₁, Multiset.mem_singleton] at hx
      exact hx)
    let e₀ : Unit ≃ Lab Y₁ := ⟨fun _ => ⟨m, hm⟩, fun _ => (), fun _ => rfl, fun x => (hone x).symm⟩
    rw [vaft_leaf, Bool.and_false, σ_false, one_smul, shEv_leaf, comp_unitL,
      Finset.sum_eq_single e₀ (fun e _ hne => absurd (Equiv.ext fun u => (hone _).trans
        (hone _).symm) hne) (fun h0 => absurd (Finset.mem_univ _) h0),
      ← map_shEv b hs.symm rfl h₂ h (Equiv.refl _) (fun _ => rfl), ← GrOperad.map_trans]
    refine gmap_congr (fun x => sval_injective E hE ?_) _
    rw [Equiv.trans_apply, hE]
    rfl
  | @STree.node _ k β c, Y₁, h₁, m, hm, Y, h, E, hE => by
    have hinj := sval_injective E hE
    have hu : ∀ u, (E.symm u).1 = sval u := fun u => by rw [← hE (E.symm u), Equiv.apply_symm_apply]
    have h' : (STree.node β fun j => (c j).subst (update STree.leaf m t')).labels = Y.val := h
    have hR : shEv b ((STree.node β c).subst (update STree.leaf m t')) Y h
        = graft R W (Lab Y) (mk R (ownGen (LinOrd.std k) (b k β) (own h') fun j =>
          GrOperad.map (R := R) (childEquiv h' j) (shEv b ((c j).subst (update STree.leaf m t'))
            (cLab (fun j => (c j).subst (update STree.leaf m t')) j) (labels_child h' j)))) :=
      shEv_node b β _ Y h'
    have hmj : m ∈ (c (own h₁ ⟨m, hm⟩)).labels := mem_own h₁ ⟨m, hm⟩
    have hz := par_shEv b hb t' Y₂ h₂
    have hy : ∀ j, GrOperad.par (R := R) (vpar p (c j)) (GrOperad.map (R := R) (childEquiv h₁ j)
        (shEv b (c j) (cLab c j) (labels_child h₁ j))) = GrOperad.map (R := R) (childEquiv h₁ j)
        (shEv b (c j) (cLab c j) (labels_child h₁ j)) := fun j => by
      rw [← GrOperad.map_par, par_shEv b hb]
    have hF : actOwner (Y := Lab Y₂) (own h₁) ⟨m, hm⟩ = own h' ∘ E.symm := by
      funext u
      rcases u with s | y
      · show own h₁ s.1 = own h' (E.symm (Sum.inl s))
        refine (own_eq h' ?_).symm
        rw [hu, sval_inl]
        refine mem_labels_subst (mem_own h₁ s.1) ?_
        rw [update_of_ne (fun e => s.2 (Subtype.ext e)), labels_leaf]
        exact Multiset.mem_singleton_self _
      · show own h₁ ⟨m, hm⟩ = own h' (E.symm (Sum.inr y))
        refine (own_eq h' ?_).symm
        rw [hu, sval_inr]
        refine mem_labels_subst hmj ?_
        rw [update_self, h₂]
        exact y.2
    have hsmul : ∀ (F' : Without (Lab Y₁) ⟨m, hm⟩ ⊕ Lab Y₂ → Fin k) (s' : Fin k → R)
        (Y' : ∀ a, FreeGrL R W (Fib F' a)),
        mk R (ownGen (LinOrd.std k) (b k β) F' fun a => s' a • Y' a)
          = (∏ a, s' a) • mk R (ownGen (LinOrd.std k) (b k β) F' Y') :=
      fun F' s' Y' => (mkY (R := R) (ownGen (LinOrd.std k) (b k β) F' Y')).map_smul_univ s' Y'
    rw [hR, ← graft_map, map_mk_ownGen, shEv_node, ← graft_act, act_mk_ownGen,
      actOwn_hom _ _ _ _ _ _ hz, ← map_smul]
    congr 1
    have hY0 := funext (actY_hom (R := R) (LinOrd.std k) (own h₁) _ ⟨m, hm⟩ (shEv b t' Y₂ h₂)
      (vpar p t') (fun j => vpar p (c j)) hy)
    show mk R (ownGen (LinOrd.std k) (b k β) (actOwner (own h₁) ⟨m, hm⟩)
      (actY (R := R) (LinOrd.std k) (own h₁) _ ⟨m, hm⟩ (shEv b t' Y₂ h₂) (vpar p t'))) = _
    rw [hY0, hsmul, mk_ownGen_congr _ _ hF]
    have hinner : ∀ a, SymSpecies.map (R := R) (Equiv.subtypeEquivRight fun s => by rw [hF])
        (actY (R := R) (LinOrd.std k) (own h₁) (fun j => GrOperad.map (R := R) (childEquiv h₁ j)
          (shEv b (c j) (cLab c j) (labels_child h₁ j))) ⟨m, hm⟩ (shEv b t' Y₂ h₂) false a)
        = (if a = own h₁ ⟨m, hm⟩ then σ R (vpar p t' && vaft p (c a) m) else 1)
          • SymSpecies.map (R := R) (fibMap E (own h') a) (GrOperad.map (R := R) (childEquiv h' a)
            (shEv b ((c a).subst (update STree.leaf m t'))
              (cLab (fun j => (c j).subst (update STree.leaf m t')) a) (labels_child h' a))) := by
      intro a
      by_cases ha : own h₁ ⟨m, hm⟩ = a
      · subst ha
        rw [if_pos rfl]
        show SymSpecies.map (R := R) _ (actLin (R := R) (LinOrd.std k) (own h₁) ⟨m, hm⟩
          (shEv b t' Y₂ h₂) false _ _) = _
        rw [actLin_eq _ _ _ _ _ _ rfl]
        let θ := childEquiv h₁ (own h₁ ⟨m, hm⟩)
        let i' : Lab (cLab c (own h₁ ⟨m, hm⟩)) := ⟨m, Multiset.mem_toFinset.2 hmj⟩
        have hθ : θ i' = ⟨⟨m, hm⟩, rfl⟩ := Subtype.ext (Subtype.ext rfl)
        let Φ := ((compEquiv θ (Equiv.refl (Lab Y₂)) i').trans (slotEquiv hθ)).trans
          ((actEq (Y := Lab Y₂) (own h₁) ⟨m, hm⟩ _ rfl).trans
            (Equiv.subtypeEquivRight fun s => by rw [hF]))
        have hΦ : ∀ u, sval (Φ u).1 = sval u := by
          rintro (⟨⟨x, hx⟩, hne⟩ | y) <;> rfl
        let E₀ := (childEquiv h' (own h₁ ⟨m, hm⟩)).trans ((fibMap E (own h') _).trans Φ.symm)
        have hE₀ : ∀ x, sval (E₀ x) = x.1 := fun x => by
          rw [← hΦ (E₀ x)]
          show sval (Φ (Φ.symm _)).1 = _
          rw [Equiv.apply_symm_apply]
          exact hE _
        rw [GrOperad.comp_map_left θ i' _ hθ,
          comp_shEv t' Y₂ h₂ (c (own h₁ ⟨m, hm⟩)) _ (labels_child h₁ _) m
            (Multiset.mem_toFinset.2 hmj) _ (labels_child h' (own h₁ ⟨m, hm⟩)) E₀ hE₀]
        simp only [map_smul, GrOperad.toGrSpecies_map]
        congr 1
        simp only [← GrOperad.map_trans]
        apply gmap_congr
        intro x
        show Φ (E₀ x) = _
        simp only [E₀, Equiv.trans_apply, Equiv.apply_symm_apply]
      · rw [if_neg (Ne.symm ha), one_smul]
        show SymSpecies.map (R := R) _ (actLin (R := R) (LinOrd.std k) (own h₁) ⟨m, hm⟩
          (shEv b t' Y₂ h₂) false a _) = _
        rw [actLin_ne _ _ _ _ _ _ ha, Bool.false_and, GrOperad.tw_false]
        have hma : m ∉ (c a).labels := fun hmem => ha (child_eq h₁ hmj hmem)
        have hsa : (c a).subst (update STree.leaf m t') = c a :=
          (subst_congr (c a) fun a' ha' =>
            update_of_ne (fun e : a' = m => hma (e ▸ ha')) t' STree.leaf).trans
            (subst_leaf (c a))
        have hcl : cLab (fun j => (c j).subst (update STree.leaf m t')) a = cLab c a := by
          show ((c a).subst _).labels.toFinset = (c a).labels.toFinset
          rw [hsa]
        rw [← map_shEv b hsa.symm hcl.symm (labels_child h₁ a) (labels_child h' a)
          (Equiv.subtypeEquivRight fun x => by rw [hcl]) (fun _ => rfl)]
        simp only [GrOperad.toGrSpecies_map, ← GrOperad.map_trans]
        apply gmap_congr
        intro x
        refine Subtype.ext (hinj ?_)
        show x.1 = sval (E _)
        rw [hE]
        rfl
    rw [funext hinner, hsmul, smul_smul]
    congr 1
    rw [vaft_node, ← GrEnd.prod_σ_tot, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    by_cases ha : a = own h₁ ⟨m, hm⟩
    · subst ha
      rw [if_pos rfl, ltB_self, if_neg Bool.false_ne_true, one_mul, if_pos hmj]
    · have hma : m ∉ (c a).labels := fun hmem => ha (child_eq h₁ hmem hmj)
      rw [if_neg ha, mul_one, if_neg hma]
      by_cases hlt : own h₁ ⟨m, hm⟩ < a
      · rw [if_pos ((ltB_eq_true _ _ _).2 hlt),
          if_pos (show ∃ j', j' < a ∧ m ∈ (c j').labels from ⟨_, hlt, hmj⟩)]
      · rw [if_neg (fun hl => hlt ((ltB_eq_true _ _ _).1 hl)),
          if_neg (show ¬ ∃ j', j' < a ∧ m ∈ (c j').labels from fun ⟨j', hj', hmem⟩ =>
            hlt (by rw [child_eq h₁ hmj hmem]; exact hj')), Bool.and_false, σ_false]

end Comp

/-! ## Spanning -/

lemma labels_ne_zero {t : STree B} (ht : t.IsShuffle) : t.labels ≠ 0 := fun h0 => by
  have hm := first_mem ht
  rw [h0] at hm
  exact Multiset.notMem_zero _ hm

/-- **The leaves of a tree substituted at a leaf.** -/
lemma labels_subst_update {t₁ t₂ : STree B} {Y₁ Y₂ : Finset ℕ} {m : ℕ} (h₁ : t₁.labels = Y₁.val)
    (h₂ : t₂.labels = Y₂.val) (hm : m ∈ Y₁) (hd : Disjoint (Y₁.erase m) Y₂) :
    (t₁.subst (update STree.leaf m t₂)).labels = ((Y₁.erase m).disjUnion Y₂ hd).val := by
  have hY₁ : Y₁.val = m ::ₘ (Y₁.erase m).val := by
    rw [← Finset.insert_val_of_notMem (Finset.notMem_erase m Y₁), Finset.insert_erase hm]
  rw [labels_subst, h₁, hY₁, Multiset.cons_bind, update_self, h₂, Finset.disjUnion_val, add_comm]
  congr 1
  rw [Multiset.bind_congr (g := fun a => {a}) fun a ha => by
    rw [update_of_ne (Finset.ne_of_mem_erase ha), labels_leaf],
    Multiset.bind_singleton, Multiset.map_id']

/-- **Substituting a shuffle tree for a leaf, at its least leaf, gives a shuffle tree.** -/
lemma isShuffle_subst_update {t₁ t₂ : STree B} {m : ℕ} (ht₁ : t₁.IsShuffle) (ht₂ : t₂.IsShuffle)
    (hf : t₂.first = m) : (t₁.subst (update STree.leaf m t₂)).IsShuffle := by
  have hfirst : ∀ a, (update STree.leaf m t₂ a).first = a := fun a => by
    by_cases ha : a = m
    · subst ha
      rw [update_self, hf]
    · rw [update_of_ne ha, first_leaf]
  refine isShuffle_subst ht₁ (fun a _ => ?_) (fun a _ a' _ hlt => by simp only [hfirst]; exact hlt)
  by_cases ha : a = m
  · subst ha
    rw [update_self]
    exact ht₂
  · rw [update_of_ne ha]
    trivial

/-- **A generator, relabelled along a bijection with leaves, is the evaluation of a corolla.** -/
lemma shEv_corolla {n : ℕ} (β : B n) (Y : Finset ℕ) (θ : Fin n ≃ Lab Y)
    (h : (STree.node β fun j => STree.leaf (θ j).1).labels = Y.val) :
    shEv b (.node β fun j => .leaf (θ j).1) Y h
      = GrOperad.map (R := R) θ ((ι R W).app (Fin n) (b n β)) := by
  have hmem : ∀ j, (θ j).1 ∈ cLab (fun j => (STree.leaf (θ j).1 : STree B)) j := fun j => by
    simp [cLab]
  have hone : ∀ j (x : Lab (cLab (fun j => (STree.leaf (θ j).1 : STree B)) j)),
      x.1 = (θ j).1 := fun j x => by
    exact Multiset.mem_singleton.1 (Multiset.mem_toFinset.1 x.2)
  let e : ∀ j, Unit ≃ Lab (cLab (fun j => (STree.leaf (θ j).1 : STree B)) j) := fun j =>
    ⟨fun _ => ⟨(θ j).1, hmem j⟩, fun _ => (), fun _ => rfl, fun x => Subtype.ext (hone j x).symm⟩
  rw [shEv_node, ← graft_corolla, ← graft_map, map_corolla, corolla_apply,
    mk_corGen_outer θ (ordOf _) (LinOrd.std n) (b n β) (Equiv.refl _),
    ← mk_inner (corGen (C := FreeGrL R W) (R := R) (LinOrd.std n) (b n β) (θ.trans (Equiv.refl _)))
      (fun j => (e j).trans (childEquiv h j))]
  congr 2
  show (⟨Fin n, Fib (own h), LinOrd.std n, b n β, _, Equiv.sigmaFiberEquiv (own h)⟩ :
    GrCompGen W (FreeGrL R W) (Lab Y)) = ⟨Fin n, Fib (own h), LinOrd.std n, b n β, _, _⟩
  congr 1
  · funext j
    rw [shEv_leaf, unitL_eq (e j), ← GrOperad.map_trans]
    rfl
  · refine Equiv.ext ?_
    rintro ⟨j, s, hs⟩
    have hsm := mem_own h s
    rw [hs] at hsm
    exact Subtype.ext (Multiset.mem_singleton.1 hsm)

/-- **The span of the evaluations of the shuffle trees** with leaves `Y`. -/
noncomputable def shSpan (Y : Finset ℕ) : Submodule R (FreeGrL R W (Lab Y)) :=
  Submodule.span R (Set.range fun t : SMono B Y => shEv b t.1 Y t.2.2)

/-- The operations lying in the span of the shuffle trees, however their inputs are named by
natural numbers. -/
noncomputable def shSpanFam (A : Type) [Fintype A] [DecidableEq A] :
    Submodule R (FreeGrL R W A) :=
  ⨅ (Y : Finset ℕ), ⨅ e : A ≃ Lab Y, (shSpan b Y).comap (GrOperad.map (R := R) e)

lemma mem_shSpanFam {A : Type} [Fintype A] [DecidableEq A] {x : FreeGrL R W A} :
    x ∈ shSpanFam b A ↔
      ∀ (Y : Finset ℕ) (e : A ≃ Lab Y), GrOperad.map (R := R) e x ∈ shSpan b Y := by
  simp only [shSpanFam, Submodule.mem_iInf, Submodule.mem_comap]

lemma shEv_mem_shSpan {t : STree B} (ht : t.IsShuffle) {Y : Finset ℕ} (h : t.labels = Y.val) :
    shEv b t Y h ∈ shSpan b Y :=
  Submodule.subset_span ⟨⟨t, ht, h⟩, rfl⟩

section Span

variable {p : ∀ k, B k → Bool}
  (hb : ∀ k (β : B k), GrSpecies.par (R := R) (p k β) (b k β) = b k β) [IsEmpty (B 0)]
include hb

/-- **The evaluations of the shuffle trees span the free graded operad.** -/
theorem shSpan_eq_top (Y : Finset ℕ) : shSpan b Y = ⊤ := by
  have hunit : ∀ (A : Type) [Fintype A] [DecidableEq A] (e : Unit ≃ A),
      GrOperad.map (R := R) e (GrOperad.one (R := R) (P := FreeGrL R W)) ∈ shSpanFam b A := by
    intro A _ _ e
    rw [mem_shSpanFam]
    intro Y' e'
    rw [← GrOperad.map_trans, ← unitL_eq (e.trans e')]
    have hY' : Y' = {(e' (e ())).1} := Finset.eq_singleton_iff_unique_mem.2 ⟨(e' (e ())).2,
      fun x hx => by
        have hu : (e.trans e').symm ⟨x, hx⟩ = () := rfl
        have hv := congrArg Subtype.val ((e.trans e').apply_symm_apply ⟨x, hx⟩)
        rw [hu] at hv
        exact hv.symm⟩
    have hl : (STree.leaf (e' (e ())).1 : STree B).labels = Y'.val :=
      (Finset.val_eq_singleton_iff.2 hY').symm
    rw [← shEv_leaf b _ Y' hl]
    exact shEv_mem_shSpan b (isShuffle_leaf _) hl
  have hgen : ∀ (n : ℕ) (v : W (Fin n)), (ι R W).app (Fin n) v ∈ shSpanFam b (Fin n) := by
    intro n v
    rw [mem_shSpanFam]
    intro Y' e
    have hcard : Y'.card = n := by simpa using (Fintype.card_congr e).symm
    let θ : Fin n ≃ Lab Y' := (Finset.orderIsoOfFin Y' hcard).toEquiv
    have hθ : StrictMono fun j => (θ j).1 := fun a a' h =>
      (Finset.orderIsoOfFin Y' hcard).strictMono h
    show SymSpecies.map (R := R) e ((ι R W).app (Fin n) v) ∈ shSpan b Y'
    have hw : SymSpecies.map (R := R) e v = SymSpecies.map (R := R) θ
        (SymSpecies.map (R := R) θ.symm (SymSpecies.map (R := R) e v)) := by
      rw [← SymSpecies.map_trans, Equiv.symm_trans_self, SymSpecies.map_refl]
    rw [← (ι R W).app_map, hw, (ι R W).app_map]
    refine Submodule.span_induction (p := fun w _ =>
      SymSpecies.map (R := R) θ ((ι R W).app (Fin n) w) ∈ shSpan b Y') ?_ (by simp)
      (fun x y _ _ hx hy => by simp only [map_add]; exact add_mem hx hy)
      (fun r x _ hx => by simp only [map_smul]; exact Submodule.smul_mem _ r hx)
      ((b n).mem_span _)
    rintro _ ⟨β, rfl⟩
    have hn : 0 < n := Nat.pos_of_ne_zero fun h0 => by
      subst h0
      exact isEmptyElim β
    have hsum : (∑ j : Fin n, ({(θ j).1} : Multiset ℕ))
        = Finset.univ.val.map fun j => (θ j).1 := by
      rw [Finset.sum_eq_multiset_sum]
      conv_rhs => rw [← Multiset.sum_map_singleton (Finset.univ.val.map fun j => (θ j).1)]
      rw [Multiset.map_map]
      rfl
    have hl : (STree.node β fun j => STree.leaf (θ j).1).labels = Y'.val := by
      rw [labels_node]
      simp only [labels_leaf]
      rw [hsum]
      refine (Multiset.Nodup.ext (Finset.univ.nodup.map hθ.injective) Y'.nodup).2 fun x => ?_
      rw [Multiset.mem_map]
      refine ⟨?_, fun hx => ⟨θ.symm ⟨x, hx⟩, by simp, by simp⟩⟩
      rintro ⟨j, _, rfl⟩
      exact (θ j).2
    show GrOperad.map (R := R) θ _ ∈ _
    rw [← shEv_corolla b β Y' θ hl]
    exact shEv_mem_shSpan b (show (STree.node β fun j => STree.leaf (θ j).1 : STree B).IsShuffle
      from ⟨hn, fun _ => trivial, hθ⟩) hl
  have hmap : ∀ (A A' : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
      (e : A ≃ A') (x : FreeGrL R W A), x ∈ shSpanFam b A →
        GrOperad.map (R := R) e x ∈ shSpanFam b A' := by
    intro A A' _ _ _ _ e x hx
    rw [mem_shSpanFam] at hx ⊢
    intro Y' e'
    rw [← GrOperad.map_trans]
    exact hx Y' (e.trans e')
  have hcomp : ∀ (A B' : Type) [Fintype A] [DecidableEq A] [Fintype B'] [DecidableEq B'] (i : A)
      (x : FreeGrL R W A) (y : FreeGrL R W B'), x ∈ shSpanFam b A → y ∈ shSpanFam b B' →
        GrOperad.comp (R := R) i x y ∈ shSpanFam b (Without A i ⊕ B') := by
    intro A B' _ _ _ _ i x y hx hy
    rw [mem_shSpanFam] at hx hy ⊢
    intro Y e
    rcases isEmpty_or_nonempty B' with hB | ⟨⟨b₀⟩⟩
    · have hy0 : y = 0 := by
        have h0 := hy ∅ (Equiv.equivOfIsEmpty B' (Lab ∅))
        have hbot : shSpan b (∅ : Finset ℕ) = ⊥ := by
          rw [shSpan, Submodule.span_eq_bot]
          rintro _ ⟨t, rfl⟩
          exact absurd t.2.2 (labels_ne_zero t.2.1)
        rw [hbot, Submodule.mem_bot] at h0
        have h1 := congrArg (GrOperad.map (R := R) (Equiv.equivOfIsEmpty B' (Lab ∅)).symm) h0
        rwa [← GrOperad.map_trans, Equiv.self_trans_symm, GrOperad.map_refl, map_zero] at h1
      rw [hy0, map_zero, map_zero]
      exact zero_mem _
    let v₁ : Without A i → ℕ := fun a => (e (Sum.inl a)).1
    let v₂ : B' → ℕ := fun b' => (e (Sum.inr b')).1
    have hv₁ : Function.Injective v₁ := fun a a' h =>
      Sum.inl_injective (e.injective (Subtype.ext h))
    have hv₂ : Function.Injective v₂ := fun d d' h =>
      Sum.inr_injective (e.injective (Subtype.ext h))
    have hv₁₂ : ∀ a b', v₁ a ≠ v₂ b' := fun a b' h => Sum.inl_ne_inr (e.injective (Subtype.ext h))
    let Y₂ : Finset ℕ := Finset.univ.image v₂
    have hY₂ : Y₂.Nonempty := ⟨v₂ b₀, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
    let m := Y₂.min' hY₂
    have hm₂ : m ∈ Y₂ := Finset.min'_mem _ _
    let Y₁ : Finset ℕ := insert m (Finset.univ.image v₁)
    have hm : m ∈ Y₁ := Finset.mem_insert_self _ _
    have hmv : ∀ a, v₁ a ≠ m := fun a ham => by
      obtain ⟨b', _, hb'⟩ := Finset.mem_image.1 hm₂
      exact hv₁₂ a b' (ham.trans hb'.symm)
    let f₂ : B' → Lab Y₂ := fun b' => ⟨v₂ b', Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
    have hf₂ : Function.Bijective f₂ := ⟨fun d d' h => by
        have h' := congrArg Subtype.val h
        exact hv₂ h',
      fun ⟨z, hz⟩ => by
        obtain ⟨b', _, rfl⟩ := Finset.mem_image.1 hz
        exact ⟨b', rfl⟩⟩
    let e₂ := Equiv.ofBijective f₂ hf₂
    let f₁ : A → Lab Y₁ := fun a => if ha : a = i then ⟨m, hm⟩ else
      ⟨v₁ ⟨a, ha⟩, Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩
    have hf₁ : Function.Bijective f₁ := by
      refine ⟨fun a a' h => ?_, fun ⟨z, hz⟩ => ?_⟩
      · by_cases ha : a = i <;> by_cases ha' : a' = i
        · rw [ha, ha']
        · simp only [f₁, dif_pos ha, dif_neg ha'] at h
          exact absurd (congrArg Subtype.val h).symm (hmv _)
        · simp only [f₁, dif_neg ha, dif_pos ha'] at h
          exact absurd (congrArg Subtype.val h) (hmv _)
        · simp only [f₁, dif_neg ha, dif_neg ha'] at h
          have h' := congrArg Subtype.val h
          exact congrArg Subtype.val (hv₁ h')
      · rcases Finset.mem_insert.1 hz with rfl | hz'
        · exact ⟨i, by simp [f₁]⟩
        · obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hz'
          exact ⟨a.1, by simp [f₁, dif_neg a.2]⟩
    let e₁ := Equiv.ofBijective f₁ hf₁
    have he₁i : e₁ i = ⟨m, hm⟩ := by simp [e₁, f₁]
    have he₁a : ∀ a : Without A i, (e₁ a.1).1 = v₁ a := fun a => by simp [e₁, f₁, dif_neg a.2]
    have hd : Disjoint (Y₁.erase m) Y₂ := Finset.disjoint_left.2 fun z hz hz₂ => by
      have hz₁ := Finset.mem_of_mem_erase hz
      rcases Finset.mem_insert.1 hz₁ with rfl | hz'
      · exact Finset.ne_of_mem_erase hz rfl
      · obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hz'
        obtain ⟨b', _, hb'⟩ := Finset.mem_image.1 hz₂
        exact hv₁₂ a b' hb'.symm
    have hYeq : (Y₁.erase m).disjUnion Y₂ hd = Y := by
      ext z
      rw [Finset.mem_disjUnion]
      constructor
      · rintro (hz | hz)
        · have hz₁ := Finset.mem_of_mem_erase hz
          rcases Finset.mem_insert.1 hz₁ with rfl | hz'
          · exact absurd rfl (Finset.ne_of_mem_erase hz)
          · obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hz'
            exact (e (Sum.inl a)).2
        · obtain ⟨b', _, rfl⟩ := Finset.mem_image.1 hz
          exact (e (Sum.inr b')).2
      · intro hz
        rcases hu : e.symm ⟨z, hz⟩ with a | b'
        · left
          have hz' : z = v₁ a := by
            rw [show v₁ a = (e (Sum.inl a)).1 from rfl, ← hu, Equiv.apply_symm_apply]
          rw [hz']
          exact Finset.mem_erase.2 ⟨hmv a,
            Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩
        · right
          have hz' : z = v₂ b' := by
            rw [show v₂ b' = (e (Sum.inr b')).1 from rfl, ← hu, Equiv.apply_symm_apply]
          rw [hz']
          exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    let Ψ : Without (Lab Y₁) ⟨m, hm⟩ ⊕ Lab Y₂ ≃ Lab Y :=
      ((compEquiv (Equiv.refl _) (Equiv.refl _) (e₁ i)).trans (slotEquiv he₁i)).symm.trans
        ((compEquiv e₁ e₂ i).symm.trans e)
    have hΨ : ∀ u, (Ψ u).1 = sval u := by
      rintro (⟨⟨z, hz⟩, hne⟩ | ⟨z, hz⟩)
      · show (e (Sum.inl ⟨e₁.symm ⟨z, hz⟩, _⟩)).1 = z
        exact (he₁a ⟨_, _⟩).symm.trans (congrArg Subtype.val (e₁.apply_symm_apply ⟨z, hz⟩))
      · show (e (Sum.inr (e₂.symm ⟨z, hz⟩))).1 = z
        exact congrArg Subtype.val (e₂.apply_symm_apply ⟨z, hz⟩)
    have hcomp_eq : GrOperad.map (R := R) e (GrOperad.comp (R := R) i x y)
        = GrOperad.map (R := R) Ψ (GrOperad.comp (R := R) (⟨m, hm⟩ : Lab Y₁)
          (GrOperad.map (R := R) e₁ x) (GrOperad.map (R := R) e₂ y)) := by
      have h1 := GrOperad.map_comp (R := R) (P := FreeGrL R W) e₁ e₂ i x y
      have h2 := GrOperad.comp_map_left (R := R) (Q := FreeGrL R W) (Equiv.refl (Lab Y₁)) (e₁ i)
        ⟨m, hm⟩ he₁i (GrOperad.map (R := R) e₁ x) (GrOperad.map (R := R) e₂ y)
      rw [GrOperad.map_refl] at h2
      rw [h2, ← h1, ← GrOperad.map_trans, ← GrOperad.map_trans]
      exact gmap_congr (fun u => by simp [Ψ]) _
    rw [hcomp_eq]
    refine Submodule.span_induction (p := fun X' _ => GrOperad.map (R := R) Ψ
      (GrOperad.comp (R := R) (⟨m, hm⟩ : Lab Y₁) X' (GrOperad.map (R := R) e₂ y)) ∈ shSpan b Y)
      ?_ (by simp) (fun _ _ _ _ h1 h2 => by
        simp only [map_add, LinearMap.add_apply]
        exact add_mem h1 h2)
      (fun r _ _ h1 => by
        simp only [map_smul, LinearMap.smul_apply]
        exact Submodule.smul_mem _ r h1) (hx Y₁ e₁)
    rintro _ ⟨t₁, rfl⟩
    refine Submodule.span_induction (p := fun Y' _ => GrOperad.map (R := R) Ψ
      (GrOperad.comp (R := R) (⟨m, hm⟩ : Lab Y₁) (shEv b t₁.1 Y₁ t₁.2.2) Y') ∈ shSpan b Y)
      ?_ (by simp) (fun _ _ _ _ h1 h2 => by
        simp only [map_add]
        exact add_mem h1 h2)
      (fun r _ _ h1 => by
        simp only [map_smul]
        exact Submodule.smul_mem _ r h1) (hy Y₂ e₂)
    rintro _ ⟨t₂, rfl⟩
    have hf : t₂.1.first = m := le_antisymm (first_le t₂.2.1 m (t₂.mem_labels.2 hm₂))
      (Finset.min'_le _ _ (t₂.mem_labels.1 (first_mem t₂.2.1)))
    have hl : (t₁.1.subst (update STree.leaf m t₂.1)).labels = Y.val := by
      rw [labels_subst_update t₁.2.2 t₂.2.2 hm hd, hYeq]
    rw [comp_shEv b hb t₂.1 Y₂ t₂.2.2 t₁.1 Y₁ t₁.2.2 m hm Y hl Ψ.symm
      (fun z => by rw [← hΨ, Equiv.apply_symm_apply]), map_smul, ← GrOperad.map_trans,
      Equiv.symm_trans_self, GrOperad.map_refl]
    exact Submodule.smul_mem _ _ (shEv_mem_shSpan b (isShuffle_subst_update t₁.2.1 t₂.2.1 hf) hl)
  refine eq_top_iff.2 fun x _ => ?_
  have hx : x ∈ shSpanFam b (Lab Y) := by
    rw [submodule_eq_top (R := R) (V := W) (shSpanFam b) hunit hgen hmap hcomp (Lab Y)]
    exact Submodule.mem_top
  have hx' := (mem_shSpanFam b).1 hx Y (Equiv.refl _)
  rwa [GrOperad.map_refl] at hx'

end Span

/-! ## The shuffle basis -/

/-- The positions of the elements of a finite linear order, as leaves. -/
noncomputable def posEquiv (A : Type) [Fintype A] [LinearOrder A] :
    A ≃ Lab (Finset.range (Fintype.card A)) :=
  Equiv.ofBijective (fun a => ⟨opos a, Finset.mem_range.2 (opos_lt_card a)⟩)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun a a' h => opos_injective (congrArg Subtype.val h), by simp⟩)

lemma posEquiv_apply (A : Type) [Fintype A] [LinearOrder A] (a : A) :
    (posEquiv A a).1 = opos a := rfl

/-- Relabelling, as a linear equivalence. -/
noncomputable def mapLEquiv {A A' : Type} [Fintype A] [DecidableEq A] [Fintype A']
    [DecidableEq A'] (e : A ≃ A') : FreeGrL R W A ≃ₗ[R] FreeGrL R W A' :=
  LinearEquiv.ofLinear (GrOperad.map (R := R) e) (GrOperad.map (R := R) e.symm)
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, ← GrOperad.map_trans, Equiv.symm_trans_self, GrOperad.map_refl]
      rfl)
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, ← GrOperad.map_trans, Equiv.self_trans_symm, GrOperad.map_refl]
      rfl)


section Basis

variable {p : ∀ k, B k → Bool}
  (hb : ∀ k (β : B k), GrSpecies.par (R := R) (p k β) (b k β) = b k β)
include hb

/-- **The evaluations of the shuffle trees are linearly independent**, their coordinates being
dual to them (`FreeGrL.shCoord_shEv`). -/
theorem linearIndependent_shEv (Y : Finset ℕ) :
    LinearIndependent R (fun t : SMono B Y => shEv b t.1 Y t.2.2) := by
  haveI : DecidableEq (STree B) := Classical.decEq _
  refine linearIndependent_iff'.2 fun s g hg t ht => ?_
  have h0 := congrArg (shCoord b p t.1 Y t.2.2) hg
  rw [map_sum, map_zero] at h0
  simp only [map_smul, smul_eq_mul] at h0
  rw [Finset.sum_eq_single t (fun t' _ ht' => by
    rw [shCoord_shEv b hb t.1 Y t.2.2 t.2.1 t'.1 t'.2.2 t'.2.1,
      if_neg (fun h => ht' (Subtype.ext h).symm), mul_zero]) (fun h => absurd ht h),
    shCoord_shEv b hb t.1 Y t.2.2 t.2.1 t.1 t.2.2 t.2.1, if_pos rfl, mul_one] at h0
  exact h0

variable [IsEmpty (B 0)]

/-- **The shuffle basis on a finite set of leaves**: the evaluations of the shuffle trees with
leaves `Y`. -/
noncomputable def shBasisLab (Y : Finset ℕ) : Module.Basis (SMono B Y) R (FreeGrL R W (Lab Y)) :=
  Module.Basis.mk (linearIndependent_shEv b hb Y) (by
    rw [← shSpan, shSpan_eq_top b hb])

theorem shBasisLab_apply (Y : Finset ℕ) (t : SMono B Y) :
    shBasisLab b hb Y t = shEv b t.1 Y t.2.2 :=
  Module.Basis.mk_apply _ _ t

/-- **The shuffle basis of the free graded operad** on a graded linear species with a homogeneous
basis of its generators, without generators of arity zero: on a finite linear order `A`, the
shuffle trees with leaves the positions `0, …, |A| - 1`, vertices labelled by the basis vectors. -/
noncomputable def shuffleBasis (A : Type) [Fintype A] [LinearOrder A] :
    Module.Basis (SMono B (Finset.range (Fintype.card A))) R (FreeGrL R W A) :=
  (shBasisLab b hb _).map (mapLEquiv (posEquiv A).symm)

/-- **A shuffle basis vector is the evaluation of its tree**, with the position of each element of
`A` as its leaf. -/
theorem shuffleBasis_apply (A : Type) [Fintype A] [LinearOrder A]
    (t : SMono B (Finset.range (Fintype.card A))) :
    shuffleBasis b hb A t = GrOperad.map (R := R) (posEquiv A).symm (shEv b t.1 _ t.2.2) := by
  rw [shuffleBasis, Module.Basis.map_apply, shBasisLab_apply]
  rfl

/-- **The free graded operad is free on the shuffle trees**, on every finite linear order. -/
noncomputable def shuffleEquiv (A : Type) [Fintype A] [LinearOrder A] :
    FreeGrL R W A ≃ₗ[R] (SMono B (Finset.range (Fintype.card A)) →₀ R) :=
  (shuffleBasis b hb A).repr

/-- **A shuffle basis vector is homogeneous**, of the parity of its vertices. -/
theorem par_shuffleBasis (A : Type) [Fintype A] [LinearOrder A]
    (t : SMono B (Finset.range (Fintype.card A))) :
    GrOperad.par (R := R) (vpar p t.1) (shuffleBasis b hb A t) = shuffleBasis b hb A t := by
  rw [shuffleBasis_apply, ← GrOperad.map_par, par_shEv b hb]

/-- **The dimension of the free graded operad** is the number of shuffle trees, when there are
finitely many. -/
theorem finrank_eq_card [Nontrivial R] (A : Type) [Fintype A] [LinearOrder A]
    [Finite (SMono B (Finset.range (Fintype.card A)))] :
    Module.finrank R (FreeGrL R W A) = Nat.card (SMono B (Finset.range (Fintype.card A))) :=
  Module.finrank_eq_nat_card_basis (shuffleBasis b hb A)

/-- **Composing basis vectors**: substituting `t₂` for the leaf `m` of `t₁`, `m` the least leaf
of `t₂`, gives a basis vector, up to the Koszul sign `σ(|t₂| · aft_{t₁}(m))`. -/
theorem comp_shBasisLab {Y₁ Y₂ : Finset ℕ} (t₁ : SMono B Y₁) (t₂ : SMono B Y₂) {m : ℕ}
    (hm : m ∈ Y₁) (hf : t₂.1.first = m) (hd : Disjoint (Y₁.erase m) Y₂)
    (E : Lab ((Y₁.erase m).disjUnion Y₂ hd) ≃ Without (Lab Y₁) ⟨m, hm⟩ ⊕ Lab Y₂)
    (hE : ∀ x, sval (E x) = x.1) :
    GrOperad.comp (R := R) (⟨m, hm⟩ : Lab Y₁) (shBasisLab b hb Y₁ t₁) (shBasisLab b hb Y₂ t₂)
      = σ R (vpar p t₂.1 && vaft p t₁.1 m) • GrOperad.map (R := R) E
        (shBasisLab b hb _ ⟨t₁.1.subst (update STree.leaf m t₂.1),
          isShuffle_subst_update t₁.2.1 t₂.2.1 hf, labels_subst_update t₁.2.2 t₂.2.2 hm hd⟩) := by
  rw [shBasisLab_apply, shBasisLab_apply, shBasisLab_apply]
  exact comp_shEv b hb t₂.1 Y₂ t₂.2.2 t₁.1 Y₁ t₁.2.2 m hm _ _ E hE

end Basis

end FreeGrL

end Operad
