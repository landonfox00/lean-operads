/-
# Binary quadratic presentations: generators from `𝔖₂`-representations, relators by orbits

Step 3 of the bridge between symmetric and shuffle operads (Dotsenko–Khoroshkin), the generic
part. `ShuffleBarSym.isKoszul_iff_shuffle` compares `Koszul.IsKoszul K E r` with
`ShuffleBar.IsKoszul K (Rsh c hc r)` for an even binary species `E` with a basis `c` indexed by
`BinGen G`. This file supplies the species, its basis, and the computation of `Rsh` for relators
given as `𝔖₃`-orbits.

* **The species of a representation of `𝔖₂`** (`BinSp K V ρ`), for an involution `ρ` of a
  `K`-module `V` (`ρ (ρ v) = v`): on a finite type `A`, the functions `f` on the orderings
  `A ≃ Fin 2` with `f (e.trans (swap 0 1)) = ρ (f e)`, relabelled by precomposition, all even
  (`BinSp.instGrSpecies`). It vanishes outside arity two (`BinSp.subsingleton_of_ne`), and
  `BinSp.ofV : V ≃ₗ[K] BinSp K V ρ (Fin 2)` takes the value on the identity ordering; reversing
  the inputs acts by `ρ` (`BinSp.map_swap_ofV`). A basis `b` of `V` indexed by `G` gives the
  even basis `BinSp.basis ρ hρ b` indexed by `BinGen G` (`BinSp.basis_op`, `BinSp.par_basis`).
  If `ρ (b g) = ε g • b (τ g)` then reversing the inputs of the basis vector of `g` gives
  `ε g` times that of `τ g` (`BinSp.map_swap_basis_of`). The trivial and sign representations
  on `V = K` have `τ = id` and `ε = 1`, `ε = -1`.
* **Permuting and scaling the children of a vertex** of an evaluated tree, on even generators:
  if `map σ (b β) = a • b β'` then `a • ev(β'; d ∘ σ⁻¹) = ev(β; d)` (`FreeGrL.shEv_perm`, from
  `GrComposite.mk_ownGen_outer` and a reordering without sign); if each child evaluates to
  `a j` times another tree with the same leaves, the vertex evaluates to `∏ a j` times
  (`FreeGrL.shEv_node_smul`, multilinearity of `GrComposite.mkY`).
* **Sorting a binary tree** (`LTree.sortL τ`): at each vertex whose left child does not hold the
  least leaf, exchange the children and replace `g` by `τ g`; the sign `LTree.sgnL ε` is the
  product of the `ε g` at the exchanged vertices, `a ^ LTree.nSwap t` when `ε` is the constant
  `a` (`LTree.sgnL_const`). A tree with distinct leaves sorts to a shuffle tree
  (`LTree.isShuffle_sortL`), and its evaluation is `sgnL ε t` times that of its sorted tree
  (`FreeGrL.shEv_sortL`).
* **Permutations on the binary-tree basis** (`ShuffleBarSym.map_tBasis_perm`): relabelling the
  basis vector `tBasis c hc (Fin n) t` along `σ` gives `sgnL ε (t.relabel σ)` times the basis
  vector of the sorted relabelled tree (`ShuffleBarSym.permIdx`). On explicit trees of arity
  three, `decide` computes `sortL` and `nSwap`.
* **Orbit relators** (`ShuffleBarSym.orbitRel S`): the relabellings of a set `S` of operations of
  arity three along all bijections `Fin 3 ≃ Fin n`. They vanish outside arity three
  (`ShuffleBarSym.orbitRel_hr3`) and span a subspace stable under `𝔖₃`
  (`ShuffleBarSym.orbitRel_hrS`), so the bridge applies to them
  (`ShuffleBarSym.isKoszul_orbitRel_iff`), with `Rsh` spanned by the coordinates
  `ShuffleBarSym.coord3L` of the permuted elements of `S` (`ShuffleBarSym.rsh_orbitRel`).
  A basis vector has the coordinates `vecOf K 3` of its monomial
  (`ShuffleBarSym.coord3L_tBasis`), and a subspace of arity three stable under `swap 0 1` and
  `swap 1 2` is stable under `𝔖₃` (`ShuffleBarSym.map_mem_of_swaps`).

`Operad.SymPresComLie` applies this to `Com` and `Lie`.
-/
import Operad.ShuffleBarJ

universe u

namespace Operad

open Function Sym GerBV GrComposite STree

/-! ## A representation of `𝔖₂` as a species concentrated in arity two -/

namespace BinSp

variable (K : Type u) [CommRing K] (V : Type u) [AddCommGroup V] [Module K V] (ρ : V →ₗ[K] V)

/-- **The vectors of arity `A`**: the functions on the orderings `A ≃ Fin 2` of `A` exchanged by
`ρ` when the ordering is reversed. -/
@[nolint unusedArguments]
def sub (A : Type) [Fintype A] [DecidableEq A] : Submodule K ((A ≃ Fin 2) → V) where
  carrier := {f | ∀ e, f (e.trans (Equiv.swap 0 1)) = ρ (f e)}
  add_mem' {f f'} hf hf' e := by simp only [Pi.add_apply, hf e, hf' e, map_add]
  zero_mem' e := by simp only [Pi.zero_apply, map_zero]
  smul_mem' a f hf e := by simp only [Pi.smul_apply, hf e, map_smul]

end BinSp

variable (K : Type u) [CommRing K] (V : Type u) [AddCommGroup V] [Module K V] (ρ : V →ₗ[K] V)

/-- **The species of a representation `ρ` of `𝔖₂` on `V`, in arity two**: on a finite type `A`,
the functions `f` on the orderings `A ≃ Fin 2` with `f (e.trans (swap 0 1)) = ρ (f e)`. It
vanishes unless `A` has two elements, and on `Fin 2` it is `V` (`BinSp.ofV`). -/
abbrev BinSp (A : Type) [Fintype A] [DecidableEq A] : Type u := BinSp.sub K V ρ A

namespace BinSp

variable {K V ρ}

/-- Relabelling along a bijection. -/
def mapL {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (σ : A ≃ B) :
    BinSp K V ρ A →ₗ[K] BinSp K V ρ B where
  toFun f := ⟨fun e => f.1 (σ.trans e), fun e => f.2 (σ.trans e)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma mapL_apply {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (σ : A ≃ B) (f : BinSp K V ρ A) (e : B ≃ Fin 2) : (mapL σ f).1 e = f.1 (σ.trans e) := rfl

/-- The parity projections: everything is even. -/
def parL {A : Type} [Fintype A] [DecidableEq A] (b : Bool) : BinSp K V ρ A →ₗ[K] BinSp K V ρ A :=
  if b then 0 else LinearMap.id

instance instGrSpecies : GrSpecies K (BinSp K V ρ) where
  map σ := mapL σ
  map_refl _ := rfl
  map_trans _ _ _ := rfl
  par b := parL b
  par_add x := by simp [parL]
  par_par b b' x := by cases b <;> cases b' <;> simp [parL]
  map_par e b x := by cases b <;> simp [parL]

@[simp] lemma map_apply {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (σ : A ≃ B) (f : BinSp K V ρ A) (e : B ≃ Fin 2) :
    (SymSpecies.map (R := K) σ f).1 e = f.1 (σ.trans e) := rfl

lemma par_false {A : Type} [Fintype A] [DecidableEq A] (f : BinSp K V ρ A) :
    GrSpecies.par (R := K) false f = f := rfl

/-- The two orderings of `Fin 2`. -/
lemma perm_two (e : Fin 2 ≃ Fin 2) : e = Equiv.refl _ ∨ e = Equiv.swap 0 1 := by
  revert e
  decide

variable (ρ) in
/-- **The vector of `V` in arity two**: `v` on the identity ordering, `ρ v` on the other. -/
def ofFun (hρ : ∀ v, ρ (ρ v) = v) (v : V) : BinSp K V ρ (Fin 2) :=
  ⟨fun e => if e 0 = 0 then v else ρ v, fun e => by
    rcases perm_two e with rfl | rfl
    · simp
    · simp [hρ]⟩

variable (ρ) in
/-- **`V` is the arity two part of `BinSp K V ρ`**, through the value on the identity ordering. -/
def ofV (hρ : ∀ v, ρ (ρ v) = v) : V ≃ₗ[K] BinSp K V ρ (Fin 2) where
  toFun := ofFun ρ hρ
  map_add' v w := Subtype.ext (funext fun e => by
    show (if e 0 = 0 then v + w else ρ (v + w)) = (if e 0 = 0 then v else ρ v) +
      (if e 0 = 0 then w else ρ w)
    split_ifs <;> simp)
  map_smul' a v := Subtype.ext (funext fun e => by
    show (if e 0 = 0 then a • v else ρ (a • v)) = a • (if e 0 = 0 then v else ρ v)
    split_ifs <;> simp)
  invFun f := f.1 (Equiv.refl _)
  left_inv v := by simp [ofFun]
  right_inv f := Subtype.ext (funext fun e => by
    rcases perm_two e with rfl | rfl
    · simp [ofFun]
    · have := f.2 (Equiv.refl _)
      rw [Equiv.refl_trans] at this
      simp [ofFun, this])

lemma ofV_apply_refl (hρ : ∀ v, ρ (ρ v) = v) (v : V) : (ofV ρ hρ v).1 (Equiv.refl _) = v := by
  simp [ofV, ofFun]

/-- **Reversing the ordering of `Fin 2` acts by `ρ`.** -/
lemma map_swap_ofV (hρ : ∀ v, ρ (ρ v) = v) (v : V) :
    SymSpecies.map (R := K) (Equiv.swap (0 : Fin 2) 1) (ofV ρ hρ v) = ofV ρ hρ (ρ v) :=
  Subtype.ext (funext fun e => by
    rcases perm_two e with rfl | rfl <;> simp [ofV, ofFun, hρ])

/-- `BinSp K V ρ` vanishes outside arity two. -/
lemma subsingleton_of_ne {k : ℕ} (hk : k ≠ 2) : Subsingleton (BinSp K V ρ (Fin k)) := by
  haveI : IsEmpty (Fin k ≃ Fin 2) := ⟨fun e => hk (by simpa using Fintype.card_congr e)⟩
  exact ⟨fun f f' => Subtype.ext (funext isEmptyElim)⟩

lemma isEmpty_binGen {G : Type} {k : ℕ} (hk : k ≠ 2) : IsEmpty (BinGen G k) :=
  ⟨fun x => by cases x; exact hk rfl⟩

/-- The binary generators indexed by `G` are `G`. -/
def genEquiv (G : Type) : G ≃ BinGen G 2 where
  toFun := BinGen.op
  invFun | .op g => g
  left_inv _ := rfl
  right_inv | .op _ => rfl

variable (ρ) in
/-- **The basis of `BinSp K V ρ` from a basis `b` of `V`**, indexed by the binary generators:
in arity two the vector `ofV (b g)` for the generator `op g`, and nothing in other arities. -/
noncomputable def basis {G : Type} (hρ : ∀ v, ρ (ρ v) = v) (b : Module.Basis G K V) :
    ∀ k, Module.Basis (BinGen G k) K (BinSp K V ρ (Fin k))
  | 2 => (b.map (ofV ρ hρ)).reindex (genEquiv G)
  | 0 => haveI := subsingleton_of_ne (K := K) (V := V) (ρ := ρ) (k := 0) (by decide)
      haveI := isEmpty_binGen (G := G) (k := 0) (by decide)
      Module.Basis.empty _
  | 1 => haveI := subsingleton_of_ne (K := K) (V := V) (ρ := ρ) (k := 1) (by decide)
      haveI := isEmpty_binGen (G := G) (k := 1) (by decide)
      Module.Basis.empty _
  | k + 3 => haveI := subsingleton_of_ne (K := K) (V := V) (ρ := ρ) (k := k + 3) (by omega)
      haveI := isEmpty_binGen (G := G) (k := k + 3) (by omega)
      Module.Basis.empty _

lemma basis_op {G : Type} (hρ : ∀ v, ρ (ρ v) = v) (b : Module.Basis G K V) (g : G) :
    basis ρ hρ b 2 (.op g) = ofV ρ hρ (b g) := by
  simp only [basis, Module.Basis.reindex_apply, Module.Basis.map_apply]
  rfl

/-- **The basis is even.** -/
lemma par_basis {G : Type} (hρ : ∀ v, ρ (ρ v) = v) (b : Module.Basis G K V) (k : ℕ)
    (β : BinGen G k) : GrSpecies.par (R := K) false (basis ρ hρ b k β) = basis ρ hρ b k β := rfl

/-- **Reversing the inputs of a basis vector** is `ρ` on the basis of `V`. -/
lemma map_swap_basis {G : Type} (hρ : ∀ v, ρ (ρ v) = v) (b : Module.Basis G K V) (g : G) :
    SymSpecies.map (R := K) (Equiv.swap (0 : Fin 2) 1) (basis ρ hρ b 2 (.op g))
      = ofV ρ hρ (ρ (b g)) := by
  rw [basis_op, map_swap_ofV]

/-- **A monomial representation**: if `ρ (b g) = ε g • b (τ g)`, reversing the inputs of the basis
vector of `g` gives `ε g` times that of `τ g`. -/
lemma map_swap_basis_of {G : Type} (hρ : ∀ v, ρ (ρ v) = v) (b : Module.Basis G K V)
    (τ : G → G) (ε : G → K) (hb : ∀ g, ρ (b g) = ε g • b (τ g)) (g : G) :
    SymSpecies.map (R := K) (Equiv.swap (0 : Fin 2) 1) (basis ρ hρ b 2 (.op g))
      = ε g • basis ρ hρ b 2 (.op (τ g)) := by
  rw [map_swap_basis, hb, map_smul, basis_op]

end BinSp

/-! ## Permuting the children of a vertex, and scaling them -/

namespace FreeGrL

variable {R : Type u} [CommRing R]
  {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)] [GrSpecies R W]
  {B : ℕ → Type} (b : ∀ k, Module.Basis (B k) R (W (Fin k)))

/-- **Relabelled evaluations of equal trees**, along bijections agreeing on the values. -/
lemma map_shEv_eq {t t' : STree B} (ht : t = t') {Y Y' : Finset ℕ} (h : t.labels = Y.val)
    (h' : t'.labels = Y'.val) {Z : Type} [Fintype Z] [DecidableEq Z] (e : Lab Y ≃ Z)
    (e' : Lab Y' ≃ Z) (he : ∀ x x', x.1 = x'.1 → e x = e' x') :
    GrOperad.map (R := R) e (shEv b t Y h) = GrOperad.map (R := R) e' (shEv b t' Y' h') := by
  subst ht
  obtain rfl : Y = Y' := Finset.val_inj.1 (h.symm.trans h')
  rw [show e = e' from Equiv.ext fun x => he x x rfl]

variable (hb : ∀ k (β : B k), GrSpecies.par (R := R) false (b k β) = b k β)
include hb

/-- **Evaluations of trees on even generators are even.** -/
lemma par_shEv_false (t : STree B) (Y : Finset ℕ) (h : t.labels = Y.val) :
    GrOperad.par (R := R) false (shEv b t Y h) = shEv b t Y h := by
  have := par_shEv b (p := fun _ _ => false) hb t Y h
  rwa [ShuffleBarSym.vpar_false] at this

/-- **Permuting the children of a vertex** on even generators: if relabelling the inputs of the
generator `b β` along `σ` gives `a • b β'`, the vertex `β'` with the children `d ∘ σ⁻¹` evaluates,
times `a`, to the vertex `β` with the children `d`. -/
theorem shEv_perm {k : ℕ} (σ : Fin k ≃ Fin k) (β β' : B k) (a : R)
    (hσ : SymSpecies.map (R := R) σ (b k β) = a • b k β') (d : Fin k → STree B) (Y : Finset ℕ)
    (h : (STree.node β d).labels = Y.val)
    (h' : (STree.node β' fun j => d (σ.symm j)).labels = Y.val) :
    a • shEv b (.node β' fun j => d (σ.symm j)) Y h' = shEv b (.node β d) Y h := by
  have hown : σ.symm ∘ own h' = own h := funext fun s => by
    have hs := mem_own h' s
    exact (own_eq h hs).symm
  let ys' : ∀ j, FreeGrL R W (Fib (own h') j) := fun j => GrOperad.map (R := R)
    (childEquiv h' j) (shEv b (d (σ.symm j)) (cLab (fun j => d (σ.symm j)) j) (labels_child h' j))
  have step1 : a • shEv b (.node β' fun j => d (σ.symm j)) Y h'
      = graft R W (Lab Y) (mk R (ownGen (LinOrd.std k) (SymSpecies.map (R := R) σ (b k β))
          (own h') ys')) := by
    rw [shEv_node, hσ, ← map_smul]
    exact congrArg _ (mk_smul_m (ownGen (LinOrd.std k) (b k β') (own h') ys') a).symm
  rw [step1, mk_ownGen_outer, mk_reorder _ (LinOrd.std k) (fun _ => false) (fun a' => by
      show GrSpecies.par (R := R) false (SymSpecies.map (R := R) _ (GrOperad.map (R := R) _ _)) = _
      rw [← GrSpecies.map_par]
      congr 1
      show GrOperad.par (R := R) false (GrOperad.map (R := R) _ _) = _
      rw [← GrOperad.map_par, par_shEv_false b hb]),
    rsg_false, one_smul, shEv_node]
  refine congrArg _ ((mk_ownGen_congr (LinOrd.std k) (b k β) hown _).trans (congrArg _ ?_))
  congr 1
  funext a'
  show SymSpecies.map (R := R) _ (SymSpecies.map (R := R) _ (GrOperad.map (R := R) _ _)) = _
  simp only [GrOperad.toGrSpecies_map, ← GrOperad.map_trans]
  exact map_shEv_eq b (by simp) _ _ _ _ fun x x' hx => Subtype.ext (Subtype.ext hx)

omit hb in
/-- **Scaling the children of a vertex**: if each child `d j` evaluates to `a j` times `d' j`, with
the same leaves, the vertex evaluates to `∏ a j` times the vertex with the children `d'`. -/
theorem shEv_node_smul {k : ℕ} (β : B k) (d d' : Fin k → STree B) (a : Fin k → R)
    (Y : Finset ℕ) (h : (STree.node β d).labels = Y.val) (hl : ∀ j, (d' j).labels = (d j).labels)
    (h' : (STree.node β d').labels = Y.val)
    (hd : ∀ j, shEv b (d j) (cLab d j) (labels_child h j)
      = a j • shEv b (d' j) (cLab d j) ((hl j).trans (labels_child h j))) :
    shEv b (.node β d) Y h = (∏ j, a j) • shEv b (.node β d') Y h' := by
  simp only [shEv_eq_shEvF] at hd ⊢
  rw [shEvF_node, shEvF_node_congr _ β d' β d hl Y h h']
  simp only [hd, map_smul]
  rw [← map_smul]
  let z : ∀ j, FreeGrL R W (Fib (own h) j) := fun j => GrOperad.map (R := R) (childEquiv h j)
    (shEvF (R := R) (fun k => ⇑(b k)) (d' j) (cLab d j) ((hl j).trans (labels_child h j)))
  exact congrArg (graft R W (Lab Y))
    ((mkY (R := R) (ownGen (LinOrd.std k) (b k β) (own h) z)).map_smul_univ a z)

end FreeGrL

/-! ## Sorting the children of the vertices of a binary tree -/

namespace LTree

variable {G : Type} (τ : G → G)

/-- **Sorting a binary tree**: at every vertex whose left child does not carry the least leaf,
exchange the children and move the decoration `g` to `τ g`. -/
def sortL : LTree G → LTree G
  | leaf a => leaf a
  | node g l r => if l.minLabel < r.minLabel then node g (sortL l) (sortL r)
      else node (τ g) (sortL r) (sortL l)

variable {K : Type u} [CommRing K] (ε : G → K)

/-- **The sign of sorting a binary tree**: the product of `ε g` over the vertices `g` whose
children are exchanged. -/
def sgnL : LTree G → K
  | leaf _ => 1
  | node g l r => sgnL l * sgnL r * if l.minLabel < r.minLabel then 1 else ε g

@[simp] lemma sortL_leaf (a : ℕ) : sortL τ (leaf a : LTree G) = leaf a := rfl

lemma sortL_node (g : G) (l r : LTree G) : sortL τ (node g l r) =
    if l.minLabel < r.minLabel then node g (sortL τ l) (sortL τ r)
      else node (τ g) (sortL τ r) (sortL τ l) := rfl

@[simp] lemma sgnL_leaf (a : ℕ) : sgnL ε (leaf a : LTree G) = 1 := rfl

lemma sgnL_node (g : G) (l r : LTree G) : sgnL ε (node g l r) =
    sgnL ε l * sgnL ε r * if l.minLabel < r.minLabel then 1 else ε g := rfl

/-- **With `ε = 1` sorting has no sign.** -/
lemma sgnL_one : ∀ t : LTree G, sgnL (fun _ => (1 : K)) t = 1
  | leaf _ => rfl
  | node g l r => by rw [sgnL_node, sgnL_one l, sgnL_one r]; split_ifs <;> simp

/-- **The number of vertices whose children sorting exchanges.** -/
def nSwap : LTree G → ℕ
  | leaf _ => 0
  | node _ l r => nSwap l + nSwap r + if l.minLabel < r.minLabel then 0 else 1

/-- **With `ε` constant, the sign of sorting is a power**, of exponent `nSwap t`, which `decide`
computes on explicit trees. -/
lemma sgnL_const (a : K) : ∀ t : LTree G, sgnL (fun _ => a) t = a ^ nSwap t
  | leaf _ => (pow_zero a).symm
  | node g l r => by
    rw [sgnL_node, sgnL_const a l, sgnL_const a r, nSwap, pow_add, pow_add]
    split_ifs <;> simp

/-- Sorting permutes the leaves. -/
lemma perm_labels_sortL : ∀ t : LTree G, (sortL τ t).labels.Perm t.labels
  | leaf _ => List.Perm.refl _
  | node g l r => by
    rw [sortL_node]
    split_ifs
    · exact (perm_labels_sortL l).append (perm_labels_sortL r)
    · exact ((perm_labels_sortL r).append (perm_labels_sortL l)).trans List.perm_append_comm

lemma minLabel_sortL : ∀ t : LTree G, (sortL τ t).minLabel = t.minLabel
  | leaf _ => rfl
  | node g l r => by
    rw [sortL_node]
    split_ifs
    · simp [minLabel_sortL l, minLabel_sortL r]
    · simp [minLabel_sortL l, minLabel_sortL r, min_comm]

/-- **A tree with distinct leaves sorts to a shuffle tree.** -/
lemma isShuffle_sortL : ∀ t : LTree G, t.labels.Nodup → (sortL τ t).IsShuffle
  | leaf _, _ => trivial
  | node g l r, h => by
    rw [labels_node, List.nodup_append] at h
    rw [sortL_node]
    split_ifs with hlt
    · exact ⟨by rwa [minLabel_sortL, minLabel_sortL], isShuffle_sortL l h.1,
        isShuffle_sortL r h.2.1⟩
    · refine ⟨?_, isShuffle_sortL r h.2.1, isShuffle_sortL l h.1⟩
      rw [minLabel_sortL, minLabel_sortL]
      have hne : l.minLabel ≠ r.minLabel := fun he =>
        h.2.2 _ (minLabel_mem l) _ (minLabel_mem r) he
      omega

end LTree

namespace FreeGrL

variable {R : Type u} [CommRing R]
  {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)] [GrSpecies R W]
  {B : ℕ → Type}

/-- Evaluations of equal trees. -/
lemma shEv_congr (b : ∀ k, Module.Basis (B k) R (W (Fin k))) {t t' : STree B}
    (ht : t = t') (Y : Finset ℕ) (h : t.labels = Y.val) (h' : t'.labels = Y.val) :
    shEv b t Y h = shEv b t' Y h' := by
  subst ht
  rfl

variable {G : Type} (c : ∀ k, Module.Basis (BinGen G k) R (W (Fin k)))
  (hc : ∀ k (β : BinGen G k), GrSpecies.par (R := R) false (c k β) = c k β)
  (τ : G → G) (ε : G → R)
  (hsw : ∀ g, SymSpecies.map (R := R) (Equiv.swap (0 : Fin 2) 1) (c 2 (.op g))
    = ε g • c 2 (.op (τ g)))

lemma labels_toBinSTree_sortL (t : LTree G) :
    (LTree.toBinSTree (LTree.sortL τ t)).labels = (LTree.toBinSTree t).labels := by
  rw [LTree.labels_toBinSTree, LTree.labels_toBinSTree]
  exact Multiset.coe_eq_coe.2 (LTree.perm_labels_sortL τ t)

include hc hsw in
/-- **Sorting a binary tree on even generators**, `ε` and `τ` describing how reversing the inputs
acts on the generators (`hsw`): the evaluation of a tree is `sgnL ε t` times the evaluation of its
sorted tree. -/
theorem shEv_sortL : ∀ (t : LTree G) (Y : Finset ℕ) (h : (LTree.toBinSTree t).labels = Y.val)
    (h' : (LTree.toBinSTree (LTree.sortL τ t)).labels = Y.val),
    shEv c (LTree.toBinSTree t) Y h
      = LTree.sgnL ε t • shEv c (LTree.toBinSTree (LTree.sortL τ t)) Y h'
  | .leaf a, Y, h, h' => by rw [LTree.sgnL_leaf, one_smul]; rfl
  | .node g l r, Y, h, h' => by
    let d : Fin 2 → STree (BinGen G) := ![LTree.toBinSTree l, LTree.toBinSTree r]
    let d' : Fin 2 → STree (BinGen G) :=
      ![LTree.toBinSTree (LTree.sortL τ l), LTree.toBinSTree (LTree.sortL τ r)]
    have hl : ∀ j, (d' j).labels = (d j).labels := fun j => by
      fin_cases j
      · exact labels_toBinSTree_sortL τ l
      · exact labels_toBinSTree_sortL τ r
    have h0 : (STree.node (BinGen.op g) d).labels = Y.val := h
    have h1 : (STree.node (BinGen.op g) d').labels = Y.val := by
      rw [← h0, STree.labels_node, STree.labels_node]
      exact Finset.sum_congr rfl fun j _ => hl j
    have step1 : shEv c (STree.node (BinGen.op g) d) Y h0
        = (LTree.sgnL ε l * LTree.sgnL ε r) • shEv c (STree.node (BinGen.op g) d') Y h1 := by
      rw [shEv_node_smul c (BinGen.op g) d d' ![LTree.sgnL ε l, LTree.sgnL ε r] Y h0 hl h1
        fun j => ?_, Fin.prod_univ_two]
      · rfl
      · fin_cases j
        · exact shEv_sortL l _ _ _
        · exact shEv_sortL r _ _ _
    refine step1.trans ?_
    rw [LTree.sgnL_node]
    by_cases hlt : l.minLabel < r.minLabel
    · rw [if_pos hlt, mul_one]
      congr 1
      exact shEv_congr c (by rw [LTree.sortL_node, if_pos hlt]; rfl) Y h1 h'
    · rw [if_neg hlt]
      have ht : LTree.toBinSTree (LTree.sortL τ (.node g l r))
          = STree.node (BinGen.op (τ g)) fun j => d' ((Equiv.swap (0 : Fin 2) 1).symm j) := by
        rw [LTree.sortL_node, if_neg hlt]
        show STree.node _ _ = STree.node _ _
        congr 1
        funext j
        fin_cases j <;> rfl
      have h2 : (STree.node (BinGen.op (τ g)) fun j =>
          d' ((Equiv.swap (0 : Fin 2) 1).symm j)).labels = Y.val := by rw [← ht]; exact h'
      rw [← shEv_perm c hc (Equiv.swap 0 1) (.op g) (.op (τ g)) (ε g) (hsw g) d' Y h1 h2,
        smul_smul, shEv_congr c ht Y h' h2]

end FreeGrL

/-! ## Relabelling the binary-tree basis along a permutation -/

namespace LTree

variable {G : Type}

lemma toBinSTree_relabel (f : ℕ → ℕ) : ∀ t : LTree G,
    toBinSTree (t.relabel f) = (toBinSTree t).relabel f
  | leaf _ => rfl
  | node g l r => by
    show STree.node (BinGen.op g) ![toBinSTree (l.relabel f), toBinSTree (r.relabel f)]
      = STree.node (BinGen.op g) fun i => (![toBinSTree l, toBinSTree r] i).relabel f
    congr 1
    funext j
    fin_cases j
    · exact toBinSTree_relabel f l
    · exact toBinSTree_relabel f r

/-- **A permutation of `Fin n` on the leaves**, the identity from `n` on. -/
def permFun {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : ℕ) : ℕ :=
  if h : x < n then σ ⟨x, h⟩ else x

lemma permFun_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) {x : ℕ} (h : x < n) : permFun σ x = σ ⟨x, h⟩ :=
  dif_pos h

lemma perm_range_map_permFun {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ((List.range n).map (permFun σ)).Perm (List.range n) := by
  refine (List.perm_ext_iff_of_nodup ((List.nodup_range).map_on fun x hx y hy hxy => ?_)
    List.nodup_range).2 fun y => ?_
  · rw [List.mem_range] at hx hy
    rw [permFun_lt σ hx, permFun_lt σ hy] at hxy
    exact congrArg Fin.val (σ.injective (Fin.ext hxy))
  · simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [permFun_lt σ hx]
      exact (σ ⟨x, hx⟩).2
    · intro hy
      refine ⟨σ.symm ⟨y, hy⟩, (σ.symm ⟨y, hy⟩).2, ?_⟩
      rw [permFun_lt σ (σ.symm ⟨y, hy⟩).2]
      simp

variable [Fintype G] [DecidableEq G] (τ : G → G)

/-- **A monomial relabelled along a permutation sorts to a monomial.** -/
lemma sortL_relabel_mem {n : ℕ} (σ : Equiv.Perm (Fin n)) {t : LTree G} (ht : t ∈ monomials n) :
    sortL τ (t.relabel (permFun σ)) ∈ monomials n := by
  rw [mem_monomials] at ht ⊢
  have hp : (sortL τ (t.relabel (permFun σ))).labels.Perm (List.range n) :=
    (perm_labels_sortL τ _).trans (by
      rw [labels_relabel]
      exact (ht.2.map _).trans (perm_range_map_permFun σ))
  exact ⟨isShuffle_sortL τ _ ((hp.nodup_iff).2 List.nodup_range |>
    fun h => by rwa [(perm_labels_sortL τ _).nodup_iff] at h), hp⟩

end LTree

namespace ShuffleBarSym

open LTree

section Perm

variable {K : Type u} [CommRing K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {G : Type} [Fintype G] [DecidableEq G]
  (c : ∀ k, Module.Basis (BinGen G k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen G k), GrSpecies.par (R := K) false (c k β) = c k β)
  (τ : G → G) (ε : G → K)
  (hsw : ∀ g, SymSpecies.map (R := K) (Equiv.swap (0 : Fin 2) 1) (c 2 (.op g))
    = ε g • c 2 (.op (τ g)))

/-- The sorted relabelling of a basis index along a permutation. -/
def permIdx {n : ℕ} (σ : Equiv.Perm (Fin n))
    (t : {t // t ∈ LTree.monomials (E := G) (Fintype.card (Fin n))}) :
    {t // t ∈ LTree.monomials (E := G) (Fintype.card (Fin n))} :=
  ⟨sortL τ (t.1.relabel (permFun σ)),
    by simpa using sortL_relabel_mem τ σ (n := n) (by simpa using t.2)⟩

include hsw in
/-- **Relabelling a vector of the binary-tree basis along a permutation**: it is the basis vector
of the sorted relabelled tree, times the sign of sorting (`τ` and `ε` as in `hsw`). -/
theorem map_tBasis_perm {n : ℕ} (σ : Equiv.Perm (Fin n))
    (t : {t // t ∈ LTree.monomials (E := G) (Fintype.card (Fin n))}) :
    GrOperad.map (R := K) σ (tBasis c hc (Fin n) t)
      = sgnL ε (t.1.relabel (permFun σ)) • tBasis c hc (Fin n) (permIdx τ σ t) := by
  let P := FreeGrL.posEquiv (Fin n)
  let e := (P.symm.trans σ).trans P
  have he : ∀ x, (e x).1 = permFun σ x.1 := fun x => by
    have hx : x.1 < n := by simpa using x.2
    have hPx : P.symm x = ⟨x.1, hx⟩ :=
      P.symm_apply_eq.2 (Subtype.ext (by rw [FreeGrL.posEquiv_apply, opos_fin]))
    show (P (σ (P.symm x))).1 = _
    rw [FreeGrL.posEquiv_apply, opos_fin, hPx, permFun_lt σ hx]
  have hsplit : P.symm.trans σ = e.trans P.symm := Equiv.ext fun x => by simp [e]
  let R := Finset.range (Fintype.card (Fin n))
  have h₀ : (toBinSTree t.1).labels = R.val := (binMonoEquiv _ t).2.2
  have h₂ : (toBinSTree (sortL τ (t.1.relabel (permFun σ)))).labels = R.val :=
    (binMonoEquiv _ (permIdx τ σ t)).2.2
  have h₃ : (toBinSTree (t.1.relabel (permFun σ))).labels = R.val :=
    (FreeGrL.labels_toBinSTree_sortL τ _).symm.trans h₂
  have h₄ : ((toBinSTree t.1).relabel (permFun σ)).labels = R.val := by
    rw [← toBinSTree_relabel]
    exact h₃
  rw [tBasis_apply, tBasis_apply, FreeGrL.shuffleBasis_apply, FreeGrL.shuffleBasis_apply,
    ← GrOperad.map_trans, hsplit, GrOperad.map_trans, ← map_smul]
  refine congrArg _ ?_
  exact calc GrOperad.map (R := K) e (FreeGrL.shEv c (toBinSTree t.1) R h₀)
      = FreeGrL.shEv c ((toBinSTree t.1).relabel (permFun σ)) R h₄ :=
        (FreeGrL.shEv_relabel c (permFun σ) _ R h₀ R h₄ e he).symm
    _ = FreeGrL.shEv c (toBinSTree (t.1.relabel (permFun σ))) R h₃ :=
        FreeGrL.shEv_congr c (toBinSTree_relabel _ _).symm R h₄ h₃
    _ = sgnL ε (t.1.relabel (permFun σ))
          • FreeGrL.shEv c (toBinSTree (sortL τ (t.1.relabel (permFun σ)))) R h₂ :=
        FreeGrL.shEv_sortL c hc τ ε hsw _ R h₃ h₂

end Perm

/-! ## Orbit relators and their shuffle coordinates -/

section Orbit

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {G : Type} [Fintype G] [DecidableEq G]
  (c : ∀ k, Module.Basis (BinGen G k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen G k), GrSpecies.par (R := K) false (c k β) = c k β)

/-- **The shuffle coordinates in arity three**, `coord3`, as a linear map. -/
noncomputable def coord3L : FreeGrL K E (Fin 3) →ₗ[K] (LTree.Mono G 3 → K) where
  toFun := coord3 c hc
  map_add' x y := funext fun σ => by simp [coord3]
  map_smul' a x := funext fun σ => by simp [coord3]

lemma coord3L_apply (x : FreeGrL K E (Fin 3)) : coord3L c hc x = coord3 c hc x := rfl

/-- **The coordinates of a basis vector** are the vector of its monomial. -/
lemma coord3L_tBasis (t : {t // t ∈ LTree.monomials (E := G) (Fintype.card (Fin 3))}) :
    coord3L c hc (tBasis c hc (Fin 3) t) = vecOf K 3 t.1 := funext fun σ => by
  rw [coord3L_apply, coord3, Module.Basis.repr_self, vecOf, Finsupp.single_apply]
  by_cases h : σ.1 = t.1
  · rw [if_pos h, if_pos]
    exact Subtype.ext h.symm
  · rw [if_neg h, if_neg]
    intro h'
    exact h (congrArg Subtype.val h').symm

/-- **The relators generated by a set `S` of operations of arity three**: their relabellings
along all bijections `Fin 3 ≃ Fin n`, so nothing outside arity three, and in arity three the
`𝔖₃`-orbit of `S`. -/
def orbitRel (S : Set (FreeGrL K E (Fin 3))) (n : ℕ) : Set (FreeGrL K E (Fin n)) :=
  {y | ∃ e : Fin 3 ≃ Fin n, ∃ x ∈ S, y = GrOperad.map (R := K) e x}

/-- Orbit relators vanish outside arity three. -/
lemma orbitRel_hr3 (S : Set (FreeGrL K E (Fin 3))) : ∀ n ≠ 3, orbitRel S n = ∅ := by
  intro n hn
  refine Set.eq_empty_iff_forall_notMem.2 fun y ⟨e, _⟩ => hn ?_
  simpa using (Fintype.card_congr e).symm

/-- Orbit relators span a subspace stable under the permutations. -/
lemma orbitRel_hrS (S : Set (FreeGrL K E (Fin 3))) : ∀ σ : Equiv.Perm (Fin 3),
    ∀ y ∈ orbitRel S 3, GrOperad.map (R := K) σ y ∈ Submodule.span K (orbitRel S 3) := by
  rintro σ y ⟨e, x, hx, rfl⟩
  refine Submodule.subset_span ⟨e.trans σ, x, hx, ?_⟩
  rw [GrOperad.map_trans]

/-- **The shuffle relators of an orbit** are spanned by the coordinates of the relabellings of `S`
along the permutations of `Fin 3`. -/
lemma rsh_orbitRel (S : Set (FreeGrL K E (Fin 3))) :
    Rsh c hc (orbitRel S) = Submodule.span K
      {v | ∃ σ : Equiv.Perm (Fin 3), ∃ x ∈ S, v = coord3L c hc (GrOperad.map (R := K) σ x)} := by
  refine congrArg (Submodule.span K) (Set.ext fun v => ⟨?_, ?_⟩)
  · rintro ⟨y, ⟨e, x, hx, rfl⟩, rfl⟩
    exact ⟨e, x, hx, rfl⟩
  · rintro ⟨σ, x, hx, rfl⟩
    exact ⟨_, ⟨σ, x, hx, rfl⟩, rfl⟩

/-- **The bridge for orbit relators**: over a field of characteristic zero, the operad presented
by the orbit relators of `S` is Koszul iff the shuffle operad presented by their coordinates is. -/
theorem isKoszul_orbitRel_iff [CharZero K] (S : Set (FreeGrL K E (Fin 3))) :
    Koszul.IsKoszul K E (orbitRel S) ↔ ShuffleBar.IsKoszul K (Rsh c hc (orbitRel S)) :=
  isKoszul_iff_shuffle c hc (orbitRel_hr3 S) (orbitRel_hrS S)

/-- **Stability under the permutations of `Fin 3` from the two adjacent transpositions.** -/
lemma map_mem_of_swaps (M : Submodule K (FreeGrL K E (Fin 3)))
    (h01 : ∀ x ∈ M, GrOperad.map (R := K) (Equiv.swap (0 : Fin 3) 1) x ∈ M)
    (h12 : ∀ x ∈ M, GrOperad.map (R := K) (Equiv.swap (1 : Fin 3) 2) x ∈ M)
    (σ : Equiv.Perm (Fin 3)) : ∀ x ∈ M, GrOperad.map (R := K) σ x ∈ M := by
  let T : Submonoid (Equiv.Perm (Fin 3)) :=
    { carrier := {σ | ∀ x ∈ M, GrOperad.map (R := K) σ x ∈ M}
      one_mem' := fun x hx => by
        show GrOperad.map (R := K) (Equiv.refl _) x ∈ M
        rwa [GrOperad.map_refl]
      mul_mem' := fun {σ τ} hσ hτ x hx => by
        show GrOperad.map (R := K) (τ.trans σ) x ∈ M
        rw [GrOperad.map_trans]
        exact hσ _ (hτ x hx) }
  have hle : Submonoid.closure (Set.range fun i : Fin 2 =>
      Equiv.swap (Fin.castSucc i) (Fin.succ i)) ≤ T := by
    rw [Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact h01
    · exact h12
  rw [Equiv.Perm.mclosure_swap_castSucc_succ] at hle
  exact hle (Submonoid.mem_top σ)

end Orbit

end ShuffleBarSym

end Operad
