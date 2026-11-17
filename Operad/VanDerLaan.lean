/-
# The van der Laan twisting morphism

Let `P` be a dg operad with an even closed operation `e` with one input, idempotent, and an odd
operation `h` with one input with `∂h = e - 1` (`Operad.OpRetract`). On the bar construction
`B(P, I)` of an ideal `I` stable under `∂`, **the van der Laan map** sends a tree to the composite
in `P` of its decorations, with `h` on every internal edge and `e` at the root
(`Bar.vdL`). It is a twisting morphism `B(P, I) → P` for the differential `d_B + d_int` of the
bar construction of the dg operad (`Bar.vdL_mc`), with values in the operations `x` with
`e ∘ x = x` (`Bar.lcomp_vdL`).

* **Marked trees.** The decorations of a tree are marked with a kind (`VdL.Kind`): `h` (the
  decoration with `h` below it), `e` (with `e` below it), `p` (alone), and the negatives of the
  last two. One morphism of graded operads `VdL.ev` out of the free graded operad on marked
  decorations evaluates them all in `P`. The van der Laan map is `ev` on the tree with its root
  of kind `e` and its other vertices of kind `h` (`VdL.mR`).
* **The differential of `P`** along `ev` is the derivation extending its values on the
  generators, `∂ (h ∘ a) = e ∘ a - a - h ∘ ∂ a` and the like: the sum of three vertex derivations
  turning a vertex of kind `h` into one of kind `e`, into one of kind `p`, or applying `∂`
  (`VdL.d_ev`).
* Applying `∂` at the vertices is `-v ∘ d_int` (`VdL.ev_vD_gD`); turning the vertices other than
  the root into kind `p` is `v ∘ d_B`, the decorations at the two ends of an edge without `h` on it
  composing in `P` as they merge in the bar construction (`VdL.ev_vD_gP_mR`, `VdL.ev_mR_mcomp`);
  and turning them into kind `e` is `-v ⋆ v`, a vertex other than the root being the vertex of a
  cut of the tree (`VdL.ev_vD_gE_mR`, through `FreeGr.star_bas`).
-/
import Operad.BarInternalAdj
import Operad.CutStar
import Operad.CobarHomotopy
import Operad.InnerDer
import Operad.TreeRelabel

universe u v w w'

namespace Operad

open Sym GerBV TreeOfArity FreeGr
open scoped TensorProduct

/-! ## Composing after an operation with one input -/

namespace GrOperad

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Composing after the unit. -/
lemma lcomp_one (x : P A) : lcomp R (one (R := R) (P := P)) x = x := by
  rw [lcomp_apply, one_comp]

lemma lcomp_sub (D D' : P Unit) (x : P A) :
    lcomp R (D - D') x = lcomp R D x - lcomp R D' x := by
  simp only [lcomp_apply, map_sub, LinearMap.sub_apply]

lemma lcomp_neg (D : P Unit) (x : P A) : lcomp R (-D) x = -lcomp R D x := by
  simp only [lcomp_apply, map_neg, LinearMap.neg_apply]

/-- **Composing after a homogeneous operation adds the parities.** -/
lemma par_lcomp {b c : Bool} {D : P Unit} {x : P A} (hD : par (R := R) b D = D)
    (hx : par (R := R) c x = x) : par (R := R) (xor b c) (lcomp R D x) = lcomp R D x := by
  rw [lcomp_apply, ← map_par, ← hD, ← hx, comp_par]

/-- `D ∘ (D' ∘ x) = (D ∘ D') ∘ x`. -/
lemma lcomp_lcomp_eq (D D' : P Unit) (x : P A) :
    lcomp R D (lcomp R D' x) = lcomp R (lcomp R D D') x := by
  rw [lcomp_apply, lcomp_apply D', comp_map_right, ← comp_assoc_seq () () D D' x,
    lcomp_apply, lcomp_apply D D', ← map_trans, ← map_trans, comp_map_left _ (Sum.inr ()) ()
      rfl, ← map_trans]
  refine congrArg (fun e => map (R := R) e _) (Equiv.ext fun z => ?_)
  rcases z with (⟨(⟨u, hu⟩ | u), hw⟩ | a)
  · exact absurd (Subsingleton.elim u ()) hu
  · exact absurd rfl hw
  · rfl

end GrOperad

namespace DGOperad

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [DGOperad R P]
  {A : Type} [Fintype A] [DecidableEq A]

/-- **The Leibniz rule after an operation with one input.** -/
lemma d_lcomp (D : P Unit) (x : P A) :
    d (R := R) (GrOperad.lcomp R D x)
      = GrOperad.lcomp R (d (R := R) D) x
        + GrOperad.lcomp R (GrOperad.par (R := R) false D - GrOperad.par (R := R) true D)
            (d (R := R) x) := by
  rw [GrOperad.lcomp_apply, ← map_d, d_comp, map_add, GrOperad.lcomp_apply,
    GrOperad.lcomp_apply]

end DGOperad

/-! ## Retracts in a dg operad -/

variable (R : Type u) [CommRing R] (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [DGOperad R P] in
/-- **A retract datum in a dg operad**: an even closed idempotent operation `e` with one input
and an odd operation `h` with one input with `∂h = e - 1`. In the endomorphism operad of a
complex `V` with a contraction `(i, p, h)` onto `H`, `e = i p`. -/
structure OpRetract where
  /-- The idempotent. -/
  e : P Unit
  /-- The homotopy. -/
  h : P Unit
  e_even : GrOperad.par (R := R) false e = e
  h_odd : GrOperad.par (R := R) true h = h
  ee : GrOperad.lcomp R e e = e
  de : DGOperad.d (R := R) e = 0
  dh : DGOperad.d (R := R) h = e - GrOperad.one (R := R)

namespace VdL

/-! ## Marked decorations -/

/-- **The kinds of marked vertices**: `h` (with `h` below the decoration), `e` (with `e` below
it), `p` (alone), and the negatives `en`, `pn` of the last two. -/
inductive Kind
  | h | e | p | en | pn

/-- The differential on the kinds: `h` stays, `e` and `p` exchange with their negatives. -/
def Kind.dk : Kind → Kind
  | .h => .h
  | .e => .en
  | .en => .e
  | .p => .pn
  | .pn => .p

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [DGOperad R P]
  {I : GrOperadIdeal R P}
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable (I) in
/-- **Marked decorations**: a kind and a decoration of the bar construction. -/
abbrev MT (k : ℕ) : Type v := Kind × BarT I k

/-- **The parity of a marked decoration**: that of the decoration for the kind `h`, the opposite
one otherwise (the parity in `P`). -/
def mpar (k : ℕ) (u : MT I k) : Bool :=
  match u.1 with
  | .h => u.2.1.2
  | _ => !u.2.1.2

/-- The value of a kind on an operation. -/
noncomputable def kval (ρ : OpRetract R P) {A : Type} [Fintype A] [DecidableEq A] :
    Kind → P A → P A
  | .h, x => GrOperad.lcomp R ρ.h x
  | .e, x => GrOperad.lcomp R ρ.e x
  | .p, x => x
  | .en, x => -GrOperad.lcomp R ρ.e x
  | .pn, x => -x

/-- **The value of a marked decoration**: `h ∘ a`, `e ∘ a`, `a`, `-(e ∘ a)` or `-a`. -/
noncomputable def mval (ρ : OpRetract R P) (k : ℕ) (u : MT I k) : P (Fin k) :=
  kval ρ u.1 u.2.val

lemma par_mval (ρ : OpRetract R P) (k : ℕ) (u : MT I k) :
    GrOperad.par (R := R) (mpar k u) (mval ρ k u) = mval ρ k u := by
  obtain ⟨κ, a⟩ := u
  have ha := a.par_val
  have e1 : xor true (!a.1.2) = a.1.2 := by cases a.1.2 <;> rfl
  have e2 : xor false (!a.1.2) = !a.1.2 := by cases a.1.2 <;> rfl
  have hh := GrOperad.par_lcomp ρ.h_odd ha
  have he := GrOperad.par_lcomp ρ.e_even ha
  rw [e1] at hh
  rw [e2] at he
  cases κ
  · exact hh
  · exact he
  · exact ha
  · show GrOperad.par (R := R) (!a.1.2) (-GrOperad.lcomp R ρ.e a.val) = _
    rw [map_neg, he]
    rfl
  · show GrOperad.par (R := R) (!a.1.2) (-a.val) = -a.val
    rw [map_neg, ha]

variable (I) in
/-- **The evaluation of marked trees**: the morphism of graded operads extending the values of
the marked decorations. -/
noncomputable def ev (ρ : OpRetract R P) : GrOperadHom R (FreeGr R (mpar (I := I))) P :=
  FreeGr.homEquiv.symm ⟨fun k u => mval ρ k u, fun k u => par_mval ρ k u⟩

lemma ev_gen (ρ : OpRetract R P) {k : ℕ} (u : MT I k) :
    (ev I ρ).app (Fin k) (gen (R := R) (gp := mpar) u) = mval ρ k u :=
  FreeGr.homEquiv_symm_gen _ u

/-! ## Marking the trees of the bar construction -/

/-- Marking a decoration with the kind `h`. -/
def hK (k : ℕ) (a : BarT I k) : MT I k := (.h, a)

/-- Setting the kind of a marked decoration. -/
def setK (κ : Kind) (k : ℕ) (u : MT I k) : MT I k := (κ, u.2)

lemma mpar_hK (k : ℕ) (a : BarT I k) :
    mpar k (hK k a) = grGenPar R (BarGen I) k a := rfl

/-- **The marked tree**: every vertex of kind `h`, then the root relabelled by `r`. -/
def mrkR (r : ∀ k, MT I k → MT I k) (t : Reg (TreeOfArity (BarT I)) A) :
    Reg (TreeOfArity (MT I)) A :=
  relabelAtR r (FreeReg.relabelR hK t) 0

@[simp] lemma mrkR_fst (r : ∀ k, MT I k → MT I k) (t : Reg (TreeOfArity (BarT I)) A) :
    (mrkR r t).1 = t.1 := rfl

lemma treeOf_mrkR (r : ∀ k, MT I k → MT I k) (t : Reg (TreeOfArity (BarT I)) A) :
    treeOf (mrkR r t) = (Tree.relabel hK (treeOf t)).relabelAt r 0 := rfl

lemma isLeaf_relabel {E E' : ℕ → Type v} (f : ∀ k, E k → E' k) (t : Tree E) :
    (Tree.relabel f t).isLeaf = t.isLeaf := by
  cases t <;> rfl

lemma isLeaf_relabelAt {E : ℕ → Type v} (g : ∀ k, E k → E k) (t : Tree E) (k : ℕ) :
    (t.relabelAt g k).isLeaf = t.isLeaf := by
  cases t <;> cases k <;> rfl

lemma apar_relabelAt_zero {E : ℕ → Type v} (gp : ∀ k, E k → Bool) (g : ∀ k, E k → E k)
    (t : Tree E) (p : ℕ) : Tree.apar gp (t.relabelAt g 0) p = Tree.apar gp t p := by
  cases t <;> rfl

lemma tpar_relabelAt_zero {E : ℕ → Type v} (gp : ∀ k, E k → Bool) (g : ∀ k, E k → E k)
    (hg : ∀ k e, gp k (g k e) = !gp k e) {t : Tree E} (ht : t.isLeaf = false) :
    Tree.tpar gp (t.relabelAt g 0) = !Tree.tpar gp t := by
  cases t with
  | leaf => simp [Tree.isLeaf] at ht
  | node a f =>
    show xor (gp _ (g _ a)) _ = !(xor (gp _ a) _)
    rw [hg]
    cases gp _ a <;> cases Forest.tparF gp f <;> rfl

lemma relabelAt_relabelAt_zero {E : ℕ → Type v} (g g' : ∀ k, E k → E k) (t : Tree E) :
    (t.relabelAt g' 0).relabelAt g 0 = t.relabelAt (fun k a => g k (g' k a)) 0 := by
  cases t <;> rfl

/-- **Marking a composite**: the root of a composite with a vertex is that of the outer tree. -/
lemma mrkR_comp (r : ∀ k, MT I k → MT I k) (i : A) (s : Reg (TreeOfArity (BarT I)) A)
    (t : Reg (TreeOfArity (BarT I)) B) (hs : (treeOf s).isLeaf = false) :
    mrkR r (SetOperad.comp i s t)
      = SetOperad.comp i (mrkR r s) (FreeReg.relabelR hK t) := by
  have h1 : FreeReg.relabelR hK (SetOperad.comp i s t)
      = SetOperad.comp i (FreeReg.relabelR hK s) (FreeReg.relabelR hK t) :=
    (FreeReg.relabel hK).app_comp i s t
  have hs' : (treeOf (FreeReg.relabelR hK s)).isLeaf = false := by
    rw [FreeReg.treeOf_relabelR, isLeaf_relabel, hs]
  have hw := Tree.one_le_weight hs'
  have hv := Tree.one_le_vb hs' ((FreeReg.relabelR hK s).1.rank i)
  have h2 := relabelAtR_comp_outer r i (FreeReg.relabelR hK s) (FreeReg.relabelR hK t)
    (k := 0) (by omega)
  rw [if_neg (by omega), Nat.add_zero] at h2
  unfold mrkR
  rw [h1, h2]

/-- Relabelling commutes with the relabellings of the inputs. -/
lemma mrkR_map (r : ∀ k, MT I k → MT I k) (e : A ≃ B) (t : Reg (TreeOfArity (BarT I)) A) :
    mrkR r (SetOperad.map e t) = SetOperad.map e (mrkR r t) :=
  reg_ext rfl rfl

lemma relabelR_map (e : A ≃ B) (t : Reg (TreeOfArity (BarT I)) A) :
    FreeReg.relabelR hK (SetOperad.map e t) = SetOperad.map e (FreeReg.relabelR hK t) :=
  reg_ext rfl rfl

/-- The marked corolla. -/
lemma mrkR_std (r : ∀ k, MT I k → MT I k) {k : ℕ} (a : BarT I k) :
    mrkR r (Reg.std (corolla a)) = Reg.std (corolla (r k (hK k a))) := by
  unfold mrkR
  rw [show FreeReg.relabelR hK (Reg.std (corolla a)) = Reg.std (corolla (hK k a)) from
    FreeReg.relabel_std hK a]
  exact reg_ext rfl rfl

local notation "𝔟" => SgnLin.bas (treeSgn (grGenPar R (BarGen I))) R
local notation "𝔪" => SgnLin.bas (treeSgn (mpar (I := I))) R

variable (I) in
/-- **Marking every vertex with the kind `h`.** -/
noncomputable def nH (A : Type) [Fintype A] [DecidableEq A] :
    FreeGr R (grGenPar R (BarGen I)) A →ₗ[R] FreeGr R (mpar (I := I)) A :=
  Finsupp.linearCombination R fun t => 𝔪 (FreeReg.relabelR hK t)

lemma nH_bas (t : Reg (TreeOfArity (BarT I)) A) : nH I A (𝔟 t) = 𝔪 (FreeReg.relabelR hK t) :=
  (Finsupp.linearCombination_single R _ _).trans (one_smul R _)

variable (I) in
/-- **Marking a tree**: its root relabelled by `r`, its other vertices of kind `h`; zero on the
trivial tree. -/
noncomputable def mR (r : ∀ k, MT I k → MT I k) (A : Type) [Fintype A] [DecidableEq A] :
    FreeGr R (grGenPar R (BarGen I)) A →ₗ[R] FreeGr R (mpar (I := I)) A :=
  Finsupp.linearCombination R fun t =>
    if (treeOf t).isLeaf = true then 0 else 𝔪 (mrkR r t)

lemma mR_bas (r : ∀ k, MT I k → MT I k) {t : Reg (TreeOfArity (BarT I)) A}
    (ht : (treeOf t).isLeaf = false) : mR I r A (𝔟 t) = 𝔪 (mrkR r t) := by
  refine (Finsupp.linearCombination_single R _ _).trans ?_
  rw [one_smul, if_neg (by rw [ht]; decide)]

lemma mR_bas_leaf (r : ∀ k, MT I k → MT I k) {t : Reg (TreeOfArity (BarT I)) A}
    (ht : (treeOf t).isLeaf = true) : mR I r A (𝔟 t) = 0 := by
  refine (Finsupp.linearCombination_single R _ _).trans ?_
  rw [one_smul, if_pos ht]

lemma mpar_hK' : ∀ k (a : BarT I k), mpar k (hK k a) = grGenPar R (BarGen I) k a :=
  fun _ _ => rfl

lemma tpar_relabelR (t : Reg (TreeOfArity (BarT I)) A) :
    Tree.tpar mpar (treeOf (FreeReg.relabelR hK t))
      = Tree.tpar (grGenPar R (BarGen I)) (treeOf t) :=
  Tree.tpar_relabel hK mpar_hK' _

lemma apar_relabelR (t : Reg (TreeOfArity (BarT I)) A) (p : ℕ) :
    Tree.apar mpar (treeOf (FreeReg.relabelR hK t)) p
      = Tree.apar (grGenPar R (BarGen I)) (treeOf t) p :=
  Tree.apar_relabel hK mpar_hK' _ _

lemma apar_mrkR (r : ∀ k, MT I k → MT I k) (t : Reg (TreeOfArity (BarT I)) A) (p : ℕ) :
    Tree.apar mpar (treeOf (mrkR r t)) p = Tree.apar (grGenPar R (BarGen I)) (treeOf t) p := by
  rw [treeOf_mrkR, apar_relabelAt_zero]
  exact apar_relabelR t p

lemma tpar_mrkR {r : ∀ k, MT I k → MT I k} (hr : ∀ k u, mpar k (r k u) = !mpar k u)
    {t : Reg (TreeOfArity (BarT I)) A} (ht : (treeOf t).isLeaf = false) :
    Tree.tpar mpar (treeOf (mrkR r t)) = !Tree.tpar (grGenPar R (BarGen I)) (treeOf t) := by
  rw [treeOf_mrkR, tpar_relabelAt_zero mpar r hr (by rw [isLeaf_relabel, ht])]
  exact congrArg (!·) (tpar_relabelR t)

lemma nH_map (e : A ≃ B) (x : FreeGr R (grGenPar R (BarGen I)) A) :
    nH I B (GrOperad.map (R := R) e x) = GrOperad.map (R := R) e (nH I A x) := by
  have h := Lin.induction₁ (S := Reg (TreeOfArity (BarT I)))
    (nH I B ∘ₗ GrOperad.map (R := R) (P := FreeGr R (grGenPar R (BarGen I))) e)
    (GrOperad.map (R := R) (P := FreeGr R (mpar (I := I))) e ∘ₗ nH I A) (fun s => ?_) x
  · simpa using h
  show nH I B (GrOperad.map (R := R) e (𝔟 s)) = GrOperad.map (R := R) e (nH I A (𝔟 s))
  rw [SgnLin.map_bas, nH_bas, nH_bas, SgnLin.map_bas, relabelR_map]

lemma mR_map (r : ∀ k, MT I k → MT I k) (e : A ≃ B) (x : FreeGr R (grGenPar R (BarGen I)) A) :
    mR I r B (GrOperad.map (R := R) e x) = GrOperad.map (R := R) e (mR I r A x) := by
  have h := Lin.induction₁ (S := Reg (TreeOfArity (BarT I)))
    (mR I r B ∘ₗ GrOperad.map (R := R) (P := FreeGr R (grGenPar R (BarGen I))) e)
    (GrOperad.map (R := R) (P := FreeGr R (mpar (I := I))) e ∘ₗ mR I r A) (fun s => ?_) x
  · simpa using h
  show mR I r B (GrOperad.map (R := R) e (𝔟 s)) = GrOperad.map (R := R) e (mR I r A (𝔟 s))
  rw [SgnLin.map_bas]
  by_cases hs : (treeOf s).isLeaf = true
  · rw [mR_bas_leaf r hs, mR_bas_leaf r (by rw [treeOf_map]; exact hs), map_zero]
  · have hs' : (treeOf s).isLeaf = false := by simpa using hs
    rw [mR_bas r hs', mR_bas r (by rw [treeOf_map]; exact hs'), SgnLin.map_bas, mrkR_map]

lemma nH_par (b : Bool) (x : FreeGr R (grGenPar R (BarGen I)) A) :
    nH I A (GrOperad.par (R := R) b x) = GrOperad.par (R := R) b (nH I A x) := by
  have h := Lin.induction₁ (S := Reg (TreeOfArity (BarT I)))
    (nH I A ∘ₗ GrOperad.par (R := R) (P := FreeGr R (grGenPar R (BarGen I))) (A := A) b)
    (GrOperad.par (R := R) (P := FreeGr R (mpar (I := I))) (A := A) b ∘ₗ nH I A) (fun s => ?_) x
  · simpa using h
  show nH I A (GrOperad.par (R := R) b (𝔟 s)) = GrOperad.par (R := R) b (nH I A (𝔟 s))
  rw [par_bas_eq, nH_bas, par_bas_eq, tot_treeSgn, tot_treeSgn, tpar_relabelR]
  split_ifs
  · exact nH_bas s
  · exact map_zero _

/-- **Marking a tree with a parity-changing root is odd.** -/
lemma mR_par {r : ∀ k, MT I k → MT I k} (hr : ∀ k u, mpar k (r k u) = !mpar k u) (b : Bool)
    (x : FreeGr R (grGenPar R (BarGen I)) A) :
    mR I r A (GrOperad.par (R := R) (!b) x) = GrOperad.par (R := R) b (mR I r A x) := by
  have h := Lin.induction₁ (S := Reg (TreeOfArity (BarT I)))
    (mR I r A ∘ₗ GrOperad.par (R := R) (P := FreeGr R (grGenPar R (BarGen I))) (A := A) (!b))
    (GrOperad.par (R := R) (P := FreeGr R (mpar (I := I))) (A := A) b ∘ₗ mR I r A)
    (fun s => ?_) x
  · simpa using h
  show mR I r A (GrOperad.par (R := R) (!b) (𝔟 s)) = GrOperad.par (R := R) b (mR I r A (𝔟 s))
  rw [par_bas_eq, tot_treeSgn]
  by_cases hs : (treeOf s).isLeaf = true
  · rw [mR_bas_leaf r hs, map_zero]
    split_ifs
    · exact mR_bas_leaf r hs
    · exact map_zero _
  · have hs' : (treeOf s).isLeaf = false := by simpa using hs
    rw [mR_bas r hs', par_bas_eq, tot_treeSgn, tpar_mrkR hr hs']
    split_ifs with h1 h2 h2
    · exact mR_bas r hs'
    · exact absurd (by rw [h1, Bool.not_not]) h2
    · exact absurd (by rw [← h2, Bool.not_not]) h1
    · exact map_zero _

lemma mR_tw {r : ∀ k, MT I k → MT I k} (hr : ∀ k u, mpar k (r k u) = !mpar k u)
    (x : FreeGr R (grGenPar R (BarGen I)) A) :
    GrSpecies.tw (R := R) (V := FreeGr R (mpar (I := I))) true (mR I r A x)
      = -mR I r A (GrSpecies.tw (R := R) (V := FreeGr R (grGenPar R (BarGen I))) true x) := by
  have h1 : mR I r A (GrOperad.par (R := R) false x) = GrOperad.par (R := R) true (mR I r A x) :=
    mR_par hr true x
  have h2 : mR I r A (GrOperad.par (R := R) true x) = GrOperad.par (R := R) false (mR I r A x) :=
    mR_par hr false x
  rw [GrSpecies.tw_apply, GrSpecies.tw_apply, map_add, map_smul]
  show GrOperad.par (R := R) false (mR I r A x) + σ R true • GrOperad.par (R := R) true (mR I r A x)
    = -(mR I r A (GrOperad.par (R := R) false x)
      + σ R true • mR I r A (GrOperad.par (R := R) true x))
  rw [h1, h2, σ_true, neg_one_smul, neg_one_smul]
  abel

lemma nH_tw (x : FreeGr R (grGenPar R (BarGen I)) A) :
    GrSpecies.tw (R := R) (V := FreeGr R (mpar (I := I))) true (nH I A x)
      = nH I A (GrSpecies.tw (R := R) (V := FreeGr R (grGenPar R (BarGen I))) true x) := by
  rw [GrSpecies.tw_apply, GrSpecies.tw_apply, map_add, map_smul]
  exact congrArg₂ (· + σ R true • ·) (nH_par false x).symm (nH_par true x).symm

/-- **Marking every vertex commutes with the compositions.** -/
lemma nH_comp (i : A) (x : FreeGr R (grGenPar R (BarGen I)) A)
    (y : FreeGr R (grGenPar R (BarGen I)) B) :
    nH I _ (GrOperad.comp (R := R) i x y) = GrOperad.comp (R := R) i (nH I A x) (nH I B y) := by
  have h : (GrOperad.comp (R := R) (P := FreeGr R (grGenPar R (BarGen I))) (B := B) i).compr₂
        (nH I _)
      = ((GrOperad.comp (R := R) (P := FreeGr R (mpar (I := I))) (B := B) i).comp
          (nH I A)).compl₂ (nH I B) := by
    refine Finsupp.lhom_ext' fun s => LinearMap.ext_ring
      (Finsupp.lhom_ext' fun t => LinearMap.ext_ring ?_)
    show nH I _ (GrOperad.comp (R := R) i (𝔟 s) (𝔟 t))
      = GrOperad.comp (R := R) i (nH I A (𝔟 s)) (nH I B (𝔟 t))
    rw [comp_bas_eq, map_smul, nH_bas, nH_bas, nH_bas, comp_bas_eq, tpar_relabelR,
      FreeReg.relabelR_fst, apar_relabelR]
    exact congrArg _ (congrArg _ ((FreeReg.relabel hK).app_comp i s t))
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y

lemma mR_comp_bas (r : ∀ k, MT I k → MT I k) (i : A) {s : Reg (TreeOfArity (BarT I)) A}
    (hs : (treeOf s).isLeaf = false) (t : Reg (TreeOfArity (BarT I)) B) :
    mR I r _ (GrOperad.comp (R := R) i (𝔟 s) (𝔟 t))
      = GrOperad.comp (R := R) i (mR I r A (𝔟 s)) (nH I B (𝔟 t)) := by
  have hst : (treeOf (SetOperad.comp i s t)).isLeaf = false := by
    rw [treeOf_comp, isLeaf_graft_iff (rank_lt_arity s i), hs, Bool.false_and]
  rw [comp_bas_eq, map_smul, mR_bas r hst, mR_bas r hs, nH_bas, comp_bas_eq, tpar_relabelR,
    mrkR_fst, apar_mrkR, mrkR_comp r i s t hs]

/-- **Marking a composite**: `m(x ∘ᵢ y) = m(x) ∘ᵢ n(y)` for `x` without unit component. -/
lemma mR_comp (r : ∀ k, MT I k → MT I k) (i : A) {x : FreeGr R (grGenPar R (BarGen I)) A}
    (hx : unitCoeff (grGenPar R (BarGen I)) R A x = 0) (y : FreeGr R (grGenPar R (BarGen I)) B) :
    mR I r _ (GrOperad.comp (R := R) i x y) = GrOperad.comp (R := R) i (mR I r A x) (nH I B y) := by
  rw [eq_sum_nonleaf (x : Reg (TreeOfArity (BarT I)) A →₀ R) hx]
  simp only [map_sum, map_smul, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun s hs => congrArg _ ?_
  have hs' := (Finset.mem_filter.1 hs).2
  induction y using induction_bas with
  | zero => simp
  | add y y' hy hy' => simp only [map_add, hy, hy']
  | bas c t => simp only [map_smul, mR_comp_bas r i hs' t]

lemma mR_gen (r : ∀ k, MT I k → MT I k) {k : ℕ} (a : BarT I k) :
    mR I r (Fin k) (gen (R := R) (gp := grGenPar R (BarGen I)) a)
      = gen (R := R) (gp := mpar (I := I)) (r k (hK k a)) := by
  rw [FreeGr.gen, mR_bas r rfl, mrkR_std]
  rfl

lemma nH_gen {k : ℕ} (a : BarT I k) :
    nH I (Fin k) (gen (R := R) (gp := grGenPar R (BarGen I)) a)
      = gen (R := R) (gp := mpar (I := I)) (hK k a) := by
  rw [FreeGr.gen, nH_bas]
  exact congrArg _ (FreeReg.relabel_std hK a)

variable (I) in
/-- **Marking every vertex with the kind `h`**, as a morphism of graded operads. -/
noncomputable def nHom :
    GrOperadHom R (FreeGr R (grGenPar R (BarGen I))) (FreeGr R (mpar (I := I))) where
  app A _ _ := nH I A
  app_par b x := nH_par b x
  app_map e x := nH_map e x
  app_one := nH_bas SetOperad.one
  app_comp i x y := nH_comp i x y

@[simp] lemma nHom_app (x : FreeGr R (grGenPar R (BarGen I)) A) : (nHom I).app A x = nH I A x :=
  rfl

/-- **Induction on basis trees** for properties stable under scalars and relabellings: trivial
trees, generators, and composites of two trees with vertices. -/
theorem bas_induction {T : ℕ → Type v} {gp : ∀ k, T k → Bool}
    {motive : ∀ (X : Type) [Fintype X] [DecidableEq X], FreeGr R gp X → Prop}
    (hsmul : ∀ (X : Type) [Fintype X] [DecidableEq X] (c : R) (x : FreeGr R gp X),
      motive X x → motive X (c • x))
    (hmap : ∀ (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] (e : X ≃ Y)
      (x : FreeGr R gp X), motive X x → motive Y (GrOperad.map (R := R) e x))
    (hleaf : ∀ (X : Type) [Fintype X] [DecidableEq X] (t : Reg (TreeOfArity T) X),
      (treeOf t).isLeaf = true → motive X (SgnLin.bas (treeSgn gp) R t))
    (hcor : ∀ (k : ℕ) (a : T k), motive (Fin k) (gen (R := R) (gp := gp) a))
    (hcomp : ∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (r : A)
      (p : Reg (TreeOfArity T) A) (q : Reg (TreeOfArity T) B), (treeOf p).isLeaf = false →
      (treeOf q).isLeaf = false → motive A (SgnLin.bas (treeSgn gp) R p) →
      motive B (SgnLin.bas (treeSgn gp) R q) →
      motive _ (GrOperad.comp (R := R) r (SgnLin.bas (treeSgn gp) R p)
        (SgnLin.bas (treeSgn gp) R q)))
    (X : Type) [Fintype X] [DecidableEq X] (t : Reg (TreeOfArity T) X) :
    motive X (SgnLin.bas (treeSgn gp) R t) := by
  refine FreeGr.tree_induction (motive := fun X _ _ t => motive X (SgnLin.bas (treeSgn gp) R t))
    hleaf ?_ ?_ X t
  · intro X _ _ k g e
    rw [← SgnLin.map_bas]
    exact hmap _ _ e _ (hcor k g)
  · intro X A B _ _ _ _ _ _ r p q e hp hq ihp ihq
    rw [← SgnLin.map_bas]
    refine hmap _ _ e _ ?_
    have h := hsmul _ (σ R (Tree.tpar gp (treeOf q) && Tree.apar gp (treeOf p) (p.1.rank r))) _
      (hcomp A B r p q hp hq ihp ihq)
    rwa [comp_bas_eq, smul_smul, σ_mul_self, one_smul] at h

/-! ## The kinds of the vertex derivations -/

/-- **Turning a vertex of kind `h` into kind `e`**, the other kinds into `h`. -/
def gE (k : ℕ) (u : MT I k) : MT I k :=
  match u.1 with
  | .h => (.e, u.2)
  | _ => (.h, u.2)

/-- **Turning a vertex of kind `h` into kind `p`**, the other kinds into `h`. -/
def gP (k : ℕ) (u : MT I k) : MT I k :=
  match u.1 with
  | .h => (.p, u.2)
  | _ => (.h, u.2)

section Diff

variable (hI : ∀ {A : Type} [Fintype A] [DecidableEq A] {x : P A}, x ∈ I.sub A →
    DGOperad.d (R := R) x ∈ I.sub A)

/-- The internal differential on the decorations of the bar construction, `s a ↦ -s (∂ a)`. -/
noncomputable abbrev dB (k : ℕ) (a : BarT I k) : BarT I k := FreeGrL.genD (Bar.dGen I hI) k a

/-- **Applying `∂` at a marked vertex**: the decoration through `s a ↦ -s (∂ a)`, the kinds `e`
and `p` exchanged with their negatives. -/
noncomputable def gD (k : ℕ) (u : MT I k) : MT I k := (u.1.dk, dB hI k u.2)

lemma gE_par (k : ℕ) (u : MT I k) : mpar k (gE k u) = !mpar k u := by
  obtain ⟨κ, ⟨⟨w, b⟩, hw⟩⟩ := u
  cases κ <;> cases b <;> rfl

lemma gP_par (k : ℕ) (u : MT I k) : mpar k (gP k u) = !mpar k u := by
  obtain ⟨κ, ⟨⟨w, b⟩, hw⟩⟩ := u
  cases κ <;> cases b <;> rfl

lemma gD_par (k : ℕ) (u : MT I k) : mpar k (gD hI k u) = !mpar k u := by
  obtain ⟨κ, ⟨⟨w, b⟩, hw⟩⟩ := u
  cases κ <;> cases b <;> rfl

lemma dB_par (k : ℕ) (a : BarT I k) :
    grGenPar R (BarGen I) k (dB hI k a) = !grGenPar R (BarGen I) k a := rfl

/-- **The three vertex derivations**: `D = D_e - D_p + D_∂`. -/
noncomputable def vDs (A : Type) [Fintype A] [DecidableEq A] :
    FreeGr R (mpar (I := I)) A →ₗ[R] FreeGr R (mpar (I := I)) A :=
  vD gE mpar R A - vD gP mpar R A + vD (gD hI) mpar R A

lemma vDs_comp (i : A) (x : FreeGr R (mpar (I := I)) A) (y : FreeGr R (mpar (I := I)) B) :
    vDs hI _ (GrOperad.comp (R := R) i x y)
      = GrOperad.comp (R := R) i (vDs hI A x) y
        + GrOperad.comp (R := R) i (GrSpecies.tw (R := R) (V := FreeGr R (mpar (I := I))) true x)
            (vDs hI B y) := by
  simp only [vDs, LinearMap.add_apply, LinearMap.sub_apply, vD_comp gE_par, vD_comp gP_par,
    vD_comp (gD_par hI), map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  abel

lemma app_tw {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
    {Q' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w'}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q' A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q' A)] [GrOperad R Q']
    (φ : GrOperadHom R Q Q') (b : Bool) (x : Q A) :
    φ.app A (GrSpecies.tw (R := R) b x) = GrSpecies.tw (R := R) b (φ.app A x) := by
  rw [GrSpecies.tw_apply, GrSpecies.tw_apply, map_add, map_smul]
  exact congrArg₂ (· + σ R b • ·) (φ.app_par false x) (φ.app_par true x)

variable (ρ : OpRetract R P)

/-- **The three vertex derivations, along the evaluation**: a derivation along `ev`. -/
noncomputable def dV : GrDer (ev I ρ) true where
  app A _ _ := (ev I ρ).app A ∘ₗ vDs hI A
  app_par c x := by
    show (ev I ρ).app _ (vDs hI _ (GrOperad.par (R := R) c x))
      = GrOperad.par (R := R) (xor c true) ((ev I ρ).app _ (vDs hI _ x))
    have hv : ∀ (g : ∀ k, MT I k → MT I k), (∀ k u, mpar k (g k u) = !mpar k u) →
        vD g mpar R _ (GrOperad.par (R := R) c x)
          = GrOperad.par (R := R) (!c) (vD g mpar R _ x) := fun g hg => by
      rw [par_vD hg, Bool.not_not]
    rw [← (ev I ρ).app_par, Bool.xor_true]
    simp only [vDs, LinearMap.add_apply, LinearMap.sub_apply, hv gE gE_par, hv gP gP_par,
      hv (gD hI) (gD_par hI), map_add, map_sub]
  app_map σ' x := by
    show (ev I ρ).app _ (vDs hI _ (GrOperad.map (R := R) σ' x))
      = GrOperad.map (R := R) σ' ((ev I ρ).app _ (vDs hI _ x))
    rw [← (ev I ρ).app_map]
    simp only [vDs, LinearMap.add_apply, LinearMap.sub_apply, ← map_vD, map_add, map_sub]
  app_one := by
    show (ev I ρ).app Unit (vDs hI Unit (SgnLin.bas (treeSgn mpar) R SetOperad.one)) = 0
    simp only [vDs, LinearMap.add_apply, LinearMap.sub_apply,
      vD_bas_of_weight (x := (SetOperad.one : Reg (TreeOfArity (MT I)) Unit)) rfl, sub_zero,
      add_zero, map_zero]
  app_comp i x y := by
    show (ev I ρ).app _ (vDs hI _ (GrOperad.comp (R := R) i x y)) = _
    rw [vDs_comp, map_add, (ev I ρ).app_comp, (ev I ρ).app_comp, app_tw]
    rfl

omit hI in
lemma par_false_h : GrOperad.par (R := R) false ρ.h = 0 := by
  rw [← ρ.h_odd, GrOperad.par_par]
  rfl

omit hI in
lemma par_true_e : GrOperad.par (R := R) true ρ.e = 0 := by
  rw [← ρ.e_even, GrOperad.par_par]
  rfl

/-- **The differential of `P` along the evaluation of marked trees**: `∂ ∘ ev = ev ∘ D` with
`D = D_e - D_p + D_∂`, both being derivations along `ev` with the same values on the
generators. -/
theorem d_ev (y : FreeGr R (mpar (I := I)) A) :
    DGOperad.d (R := R) ((ev I ρ).app A y) = (ev I ρ).app A (vDs hI A y) := by
  have h : GrDer.compHom (DGOperad.toDer (R := R) (P := P)) (ev I ρ) = dV hI ρ :=
    FreeGr.der_ext fun k u => by
      show DGOperad.d (R := R) ((ev I ρ).app (Fin k) (gen u))
        = (ev I ρ).app (Fin k) (vDs hI (Fin k) (gen u))
      simp only [vDs, LinearMap.add_apply, LinearMap.sub_apply, vD_gen, map_add, map_sub, ev_gen]
      obtain ⟨κ, a⟩ := u
      have hd : (dB hI k a).val = -DGOperad.d (R := R) a.val := rfl
      cases κ
      · show DGOperad.d (R := R) (GrOperad.lcomp R ρ.h a.val)
          = GrOperad.lcomp R ρ.e a.val - a.val + GrOperad.lcomp R ρ.h (dB hI k a).val
        rw [DGOperad.d_lcomp, ρ.dh, ρ.h_odd, par_false_h, GrOperad.lcomp_sub,
          GrOperad.lcomp_one, hd, map_neg, zero_sub, GrOperad.lcomp_neg]
      · show DGOperad.d (R := R) (GrOperad.lcomp R ρ.e a.val)
          = GrOperad.lcomp R ρ.h a.val - GrOperad.lcomp R ρ.h a.val
            + -GrOperad.lcomp R ρ.e (dB hI k a).val
        rw [DGOperad.d_lcomp, ρ.de, ρ.e_even, par_true_e, hd, map_neg, sub_zero, sub_self,
          zero_add, neg_neg]
        simp [GrOperad.lcomp_apply]
      · show DGOperad.d (R := R) a.val
          = GrOperad.lcomp R ρ.h a.val - GrOperad.lcomp R ρ.h a.val + -(dB hI k a).val
        rw [hd, neg_neg, sub_self, zero_add]
      · show DGOperad.d (R := R) (-GrOperad.lcomp R ρ.e a.val)
          = GrOperad.lcomp R ρ.h a.val - GrOperad.lcomp R ρ.h a.val
            + GrOperad.lcomp R ρ.e (dB hI k a).val
        rw [map_neg, DGOperad.d_lcomp, ρ.de, ρ.e_even, par_true_e, hd, map_neg, sub_zero,
          sub_self, zero_add]
        simp [GrOperad.lcomp_apply]
      · show DGOperad.d (R := R) (-a.val)
          = GrOperad.lcomp R ρ.h a.val - GrOperad.lcomp R ρ.h a.val + (dB hI k a).val
        rw [hd, map_neg, sub_self, zero_add]
  exact congrArg (fun D : GrDer (ev I ρ) true => D.app A y) h

lemma d_ev' (y : FreeGr R (mpar (I := I)) A) :
    DGOperad.d (R := R) ((ev I ρ).app A y)
      = (ev I ρ).app A (vD gE mpar R A y) - (ev I ρ).app A (vD gP mpar R A y)
        + (ev I ρ).app A (vD (gD hI) mpar R A y) := by
  rw [d_ev hI ρ, vDs, LinearMap.add_apply, LinearMap.sub_apply, map_add, map_sub]

/-! ## The internal differential -/

lemma dB_par' : ∀ k (a : BarT I k),
    grGenPar R (BarGen I) k (dB hI k a) = !grGenPar R (BarGen I) k a := fun _ _ => rfl

/-- **Marking every vertex commutes with the internal differentials.** -/
lemma nH_vD (x : FreeGr R (grGenPar R (BarGen I)) A) :
    nH I A (vD (dB hI) (grGenPar R (BarGen I)) R A x) = vD (gD hI) mpar R A (nH I A x) := by
  have h : GrDer.homComp (nHom I) (vDer (dB hI) (grGenPar R (BarGen I)) R (dB_par' hI))
      = GrDer.compHom (vDer (gD hI) mpar R (gD_par hI)) (nHom I) :=
    FreeGr.der_ext fun k a => by
      show nH I (Fin k) (vD (dB hI) (grGenPar R (BarGen I)) R (Fin k) (gen a))
        = vD (gD hI) mpar R (Fin k) (nH I (Fin k) (gen a))
      rw [vD_gen, nH_gen, nH_gen, vD_gen]
      rfl
  exact congrArg (fun D : GrDer (nHom I) true => D.app A x) h

lemma unitCoeff_tw_bas {t : Reg (TreeOfArity (BarT I)) A} (ht : (treeOf t).isLeaf = false) :
    unitCoeff (grGenPar R (BarGen I)) R A
      (GrSpecies.tw (R := R) (V := FreeGr R (grGenPar R (BarGen I))) true
        (SgnLin.bas (treeSgn (grGenPar R (BarGen I))) R t)) = 0 := by
  rw [tw_bas, map_smul, unitCoeff_bas, if_neg (by rw [ht]; decide), smul_zero]

/-- **Applying `∂` at the vertices is `-v ∘ d_int`.** -/
theorem ev_vD_gD (x : FreeGr R (grGenPar R (BarGen I)) A) :
    (ev I ρ).app A (vD (gD hI) mpar R A (mR I gE A x))
      = -(ev I ρ).app A (mR I gE A (vD (dB hI) (grGenPar R (BarGen I)) R A x)) := by
  induction x using induction_bas with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]
  | bas c t =>
    simp only [map_smul]
    rw [← smul_neg]
    refine congrArg _ ?_
    refine bas_induction (motive := fun X _ _ x => (ev I ρ).app X (vD (gD hI) mpar R X
      (mR I gE X x)) = -(ev I ρ).app X (mR I gE X (vD (dB hI) (grGenPar R (BarGen I)) R X x)))
      ?_ ?_ ?_ ?_ ?_ A t
    · intro X _ _ c x hx
      simp only [map_smul, hx, smul_neg]
    · intro X Y _ _ _ _ e x hx
      rw [mR_map, ← map_vD, (ev I ρ).app_map, hx, ← map_vD, mR_map, (ev I ρ).app_map, map_neg]
    · intro X _ _ t ht
      rw [mR_bas_leaf gE ht, vD_bas_of_weight (by rw [Tree.eq_leaf_of_isLeaf ht]; rfl),
        map_zero, map_zero, map_zero, map_zero, neg_zero]
    · intro k a
      rw [mR_gen, vD_gen, vD_gen, mR_gen, ev_gen, ev_gen]
      rfl
    · intro A' B' _ _ _ _ r p q hp hq ihp _
      have hup : unitCoeff (grGenPar R (BarGen I)) R A'
          (SgnLin.bas (treeSgn (grGenPar R (BarGen I))) R p) = 0 := by
        rw [unitCoeff_bas, if_neg (by rw [hp]; decide)]
      rw [mR_comp_bas gE r hp q, vD_comp (gD_par hI), vD_comp (dB_par' hI)]
      simp only [map_add]
      rw [mR_comp gE r (unitCoeff_vD _) _, mR_comp gE r (unitCoeff_tw_bas hp) _,
        (ev I ρ).app_comp, (ev I ρ).app_comp, (ev I ρ).app_comp, (ev I ρ).app_comp,
        ihp, mR_tw gE_par, nH_vD]
      simp only [map_neg, LinearMap.neg_apply, neg_add]

end Diff

/-! ## Merging two vertices -/

section Merge

variable (ρ : OpRetract R P)

local notation "𝔪c" => mcomp (barMerge I) (grGenPar R (BarGen I)) R
local notation "gpB" => grGenPar R (BarGen I)

lemma map_inj {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q] (e : A ≃ B)
    {x y : Q A} (h : GrOperad.map (R := R) e x = GrOperad.map (R := R) e y) : x = y := by
  have h' := congrArg (GrOperad.map (R := R) e.symm) h
  rwa [← GrOperad.map_trans, ← GrOperad.map_trans, Equiv.self_trans_symm, GrOperad.map_refl,
    GrOperad.map_refl] at h'

lemma kval_smul (κ : Kind) (c : R) (x : P A) : kval ρ κ (c • x) = c • kval ρ κ x := by
  cases κ <;> simp [kval, smul_neg]

lemma kval_map (κ : Kind) (e : A ≃ B) (x : P A) :
    kval ρ κ (GrOperad.map (R := R) e x) = GrOperad.map (R := R) e (kval ρ κ x) := by
  cases κ <;> simp [kval, GrOperad.lcomp_map]

lemma kval_comp (κ : Kind) (i : A) (x : P A) (y : P B) :
    kval ρ κ (GrOperad.comp (R := R) i x y) = GrOperad.comp (R := R) i (kval ρ κ x) y := by
  cases κ <;> simp [kval, GrOperad.lcomp_comp]

lemma isLeaf_mgraft {E : ℕ → Type v} (μ : MergeFn E) {s : Tree E} (hs : s.isLeaf = false)
    (p : ℕ) (u : Tree E) : (s.mgraft μ p u).isLeaf = false := by
  cases s with
  | leaf => simp [Tree.isLeaf] at hs
  | node e f =>
    simp only [Tree.mgraft]
    split_ifs
    · cases u <;> rfl
    · rfl

/-- **A merge-composite has no unit component.** -/
lemma unitCoeff_mcomp (i : A) (x : FreeGr R gpB A) (y : FreeGr R gpB B) :
    unitCoeff gpB R _ (𝔪c i x y) = 0 := by
  induction x using induction_bas with
  | zero => simp
  | add x x' hx hx' => rw [map_add, LinearMap.add_apply, map_add, hx, hx', add_zero]
  | bas c s =>
    induction y using induction_bas with
    | zero => simp
    | add y y' hy hy' => rw [map_add, map_add, hy, hy', add_zero]
    | bas c' t =>
      rw [map_smul, map_smul, map_smul, LinearMap.smul_apply, map_smul, mcomp_bas]
      split_ifs with h
      · rw [map_smul, unitCoeff_bas, treeOf_mcompR, if_neg (by
          rw [isLeaf_mgraft _ h.1]; decide), smul_zero, smul_zero, smul_zero]
      · simp

lemma unitCoeff_bas_of {t : Reg (TreeOfArity (BarT I)) A} (ht : (treeOf t).isLeaf = false) :
    unitCoeff gpB R A (SgnLin.bas (treeSgn gpB) R t) = 0 := by
  rw [unitCoeff_bas, if_neg (by rw [ht]; decide)]

lemma mrkR_congr {r r' : ∀ k, MT I k → MT I k} (h : ∀ k a, r k (hK k a) = r' k (hK k a))
    (t : Reg (TreeOfArity (BarT I)) A) : mrkR r t = mrkR r' t :=
  reg_ext rfl (by
    rw [treeOf_mrkR, treeOf_mrkR]
    generalize treeOf t = T
    cases T with
    | leaf => rfl
    | node a f =>
      rw [Tree.relabel_node]
      exact congrArg (fun z => Tree.node z _) (h _ a))

lemma mR_congr {r r' : ∀ k, MT I k → MT I k} (h : ∀ k a, r k (hK k a) = r' k (hK k a)) :
    mR I r A = mR I r' A := by
  unfold mR
  congr 1
  funext t
  rw [mrkR_congr h t]

lemma mR_gE : mR I gE A = mR I (setK .e) A := mR_congr fun _ _ => rfl

lemma mR_gP : mR I gP A = mR I (setK .p) A := mR_congr fun _ _ => rfl

lemma mrkR_setK_h (t : Reg (TreeOfArity (BarT I)) A) :
    mrkR (setK .h) t = FreeReg.relabelR hK t :=
  reg_ext rfl (by
    rw [treeOf_mrkR, FreeReg.treeOf_relabelR]
    generalize treeOf t = T
    cases T with
    | leaf => rfl
    | node a f =>
      rw [Tree.relabel_node]
      rfl)

/-- On the trees with a vertex, marking every vertex with `h` is marking the root with `h`. -/
lemma nH_eq_mR {z : FreeGr R gpB A} (hz : unitCoeff gpB R A z = 0) :
    nH I A z = mR I (setK .h) A z := by
  rw [eq_sum_nonleaf (z : Reg (TreeOfArity (BarT I)) A →₀ R) hz]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [nH_bas, mR_bas _ (Finset.mem_filter.1 ht).2, mrkR_setK_h]

lemma tpar_std {k : ℕ} (a : BarT I k) :
    Tree.tpar gpB (treeOf (Reg.std (corolla a) : Reg (TreeOfArity (BarT I)) (Fin k))) = a.1.2 :=
  Tree.tpar_corolla gpB a

lemma ev_mR_gen (κ : Kind) {k : ℕ} (a : BarT I k) :
    (ev I ρ).app (Fin k) (mR I (setK κ) (Fin k) (gen (R := R) (gp := gpB) a))
      = kval ρ κ a.val := by
  rw [mR_gen, ev_gen]
  rfl

lemma ev_mR_tw_gen (κ : Kind) {k : ℕ} (a : BarT I k) :
    (ev I ρ).app (Fin k) (mR I (setK κ) (Fin k)
        (GrSpecies.tw (R := R) (V := FreeGr R gpB) true (gen (R := R) (gp := gpB) a)))
      = σ R a.1.2 • kval ρ κ a.val := by
  rw [FreeGr.gen, tw_bas, tpar_std, map_smul, map_smul, ← FreeGr.gen, ev_mR_gen]

/-- **Merging two generators**: `κ(s a ⊛ᵢ s b) = -(-1)^{|s a|} κ(a) ∘ᵢ b`. -/
lemma ev_mR_mcomp_gen (κ : Kind) {k l : ℕ} (a : BarT I k) (i : Fin k) (b : BarT I l) :
    (ev I ρ).app _ (mR I (setK κ) _ (𝔪c i (gen (R := R) (gp := gpB) a) (gen b)))
      = -GrOperad.comp (R := R) i
          ((ev I ρ).app _ (mR I (setK κ) _ (GrSpecies.tw (R := R) (V := FreeGr R gpB) true
            (gen (R := R) (gp := gpB) a))))
          ((ev I ρ).app _ (mR I (setK .p) _ (gen (R := R) (gp := gpB) b))) := by
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = k + l := ⟨k + l - 1, by have := i.2; omega⟩
  rw [mcomp_gen_bar a i b m hm, mR_map, (ev I ρ).app_map, ev_mR_gen,
    barMerge_val a b ⟨i.2, hm⟩, ev_mR_tw_gen, ev_mR_gen]
  unfold barVal
  rw [kval_smul, kval_map, kval_comp, map_smul, ← GrOperad.map_trans, Equiv.self_trans_symm,
    GrOperad.map_refl, LinearMap.map_smul₂, ← neg_smul]
  congr 1
  cases a.1.2 <;> simp [σ]

end Merge


section MergeInd

variable (ρ : OpRetract R P)

local notation "𝔪c" => mcomp (barMerge I) (grGenPar R (BarGen I)) R
local notation "gpB" => grGenPar R (BarGen I)

lemma tw_map' (b : Bool) (e : A ≃ B) (x : FreeGr R gpB A) :
    GrSpecies.tw (R := R) (V := FreeGr R gpB) b (GrOperad.map (R := R) e x)
      = GrOperad.map (R := R) e (GrSpecies.tw (R := R) (V := FreeGr R gpB) b x) :=
  (GrSpecies.map_tw b e x).symm

lemma par_bas' (t : Reg (TreeOfArity (BarT I)) A) :
    GrOperad.par (R := R) (Tree.tpar gpB (treeOf t)) (𝔟 t) = 𝔟 t :=
  SgnLin.par_bas t

lemma par_ev_nH_tw (t : Reg (TreeOfArity (BarT I)) A) :
    GrOperad.par (R := R) (Tree.tpar gpB (treeOf t))
        ((ev I ρ).app A (nH I A (GrSpecies.tw (R := R) (V := FreeGr R gpB) true (𝔟 t))))
      = (ev I ρ).app A (nH I A (GrSpecies.tw (R := R) (V := FreeGr R gpB) true (𝔟 t))) := by
  rw [← (ev I ρ).app_par, ← nH_par, tw_bas, map_smul, par_bas']

lemma par_ev_gen {k : ℕ} (u : MT I k) :
    GrOperad.par (R := R) (mpar k u) ((ev I ρ).app (Fin k) (gen (R := R) (gp := mpar) u))
      = (ev I ρ).app (Fin k) (gen (R := R) (gp := mpar) u) := by
  rw [ev_gen]
  exact par_mval ρ k u

/-- The merge lemma with a generator on the right. -/
lemma ev_mR_mcomp_right {l : ℕ} (b : BarT I l) (X : Type) [Fintype X] [DecidableEq X]
    (s : Reg (TreeOfArity (BarT I)) X) (i : X) (κ : Kind) :
    (ev I ρ).app _ (mR I (setK κ) _ (𝔪c i (𝔟 s) (gen (R := R) (gp := gpB) b)))
      = -GrOperad.comp (R := R) i
          ((ev I ρ).app X (mR I (setK κ) X (GrSpecies.tw (R := R) (V := FreeGr R gpB) true
            (𝔟 s))))
          ((ev I ρ).app (Fin l) (mR I (setK .p) (Fin l) (gen (R := R) (gp := gpB) b))) := by
  revert i κ
  refine bas_induction (motive := fun X _ _ x => ∀ (i : X) (κ : Kind),
    (ev I ρ).app _ (mR I (setK κ) _ (𝔪c i x (gen (R := R) (gp := gpB) b)))
      = -GrOperad.comp (R := R) i
          ((ev I ρ).app X (mR I (setK κ) X (GrSpecies.tw (R := R) (V := FreeGr R gpB) true x)))
          ((ev I ρ).app (Fin l) (mR I (setK .p) (Fin l) (gen (R := R) (gp := gpB) b))))
    ?_ ?_ ?_ ?_ ?_ X s
  · intro X _ _ c x hx i κ
    rw [map_smul, LinearMap.smul_apply, map_smul, map_smul, hx i κ, map_smul, map_smul,
      map_smul, LinearMap.map_smul₂, smul_neg]
  · intro X Y _ _ _ _ e x hx i κ
    obtain ⟨i0, rfl⟩ := e.surjective i
    have h := mcomp_map (μ := barMerge I) (gp := gpB) (R := R) e (Equiv.refl (Fin l)) i0 x
      (gen b)
    rw [GrOperad.map_refl] at h
    have hc := GrOperad.map_comp (R := R) e (Equiv.refl (Fin l)) i0
      ((ev I ρ).app X (mR I (setK κ) X (GrSpecies.tw (R := R) (V := FreeGr R gpB) true x)))
      ((ev I ρ).app (Fin l) (mR I (setK .p) (Fin l) (gen (R := R) (gp := gpB) b)))
    rw [GrOperad.map_refl] at hc
    rw [h, mR_map, (ev I ρ).app_map, hx i0 κ, tw_map', mR_map, (ev I ρ).app_map, ← hc, map_neg]
  · intro X _ _ t ht i κ
    rw [mcomp_leaf_left _ ht, map_zero, map_zero, tw_bas, map_smul, mR_bas_leaf _ ht,
      smul_zero, map_zero, LinearMap.map_zero₂, neg_zero]
  · intro k a i κ
    exact ev_mR_mcomp_gen ρ κ a i b
  · intro A' B' _ _ _ _ r p q hp hq ihp ihq i κ
    have hYp := par_ev_nH_tw ρ q
    have hZp : GrOperad.par (R := R) (!b.1.2)
        ((ev I ρ).app (Fin l) (mR I (setK .p) (Fin l) (gen (R := R) (gp := gpB) b)))
        = (ev I ρ).app (Fin l) (mR I (setK .p) (Fin l) (gen (R := R) (gp := gpB) b)) := by
      rw [mR_gen]
      exact par_ev_gen ρ (setK .p l (hK l b))
    have hgb : GrOperad.par (R := R) b.1.2 (gen (R := R) (gp := gpB) b)
        = gen (R := R) (gp := gpB) b := by
      have h := par_bas' (R := R) (I := I) (Reg.std (corolla b))
      rwa [tpar_std] at h
    rcases i with ⟨k, hk⟩ | b'
    · refine map_inj (R := R) (parEquiv (Ne.symm hk) B' (Fin l)) ?_
      rw [← (ev I ρ).app_map, ← mR_map,
        mcomp_comp_par (barMerge I) barMerge_odd (Ne.symm hk) (𝔟 p) (par_bas' q) hgb,
        map_smul, map_smul, mR_comp _ _ (unitCoeff_mcomp _ _ _), (ev I ρ).app_comp, ihp k κ,
        tw_comp', mR_comp _ _ (unitCoeff_tw_bas hp), (ev I ρ).app_comp,
        map_neg (GrOperad.map (R := R) (parEquiv (Ne.symm hk) B' (Fin l))),
        GrOperad.comp_assoc_par (Ne.symm hk) _ hYp hZp, tw_bas, tw_bas]
      simp only [map_neg, LinearMap.neg_apply, map_smul, LinearMap.smul_apply, smul_neg,
        smul_smul]
      congr 1
      cases Tree.tpar gpB (treeOf p) <;> cases Tree.tpar gpB (treeOf q) <;> cases b.1.2 <;>
        simp [σ]
    · refine map_inj (R := R) (seqEquiv r b' (Fin l)) ?_
      rw [← (ev I ρ).app_map, ← mR_map,
        mcomp_comp_inner (barMerge I) barMerge_odd r b' (𝔟 p) (𝔟 q) _ (unitCoeff_bas_of hq),
        mR_comp _ _ (unitCoeff_tw_bas hp), (ev I ρ).app_comp, nH_eq_mR (unitCoeff_mcomp _ _ _),
        ihq b' .h, ← nH_eq_mR (unitCoeff_tw_bas hq), tw_comp', mR_comp _ _ (unitCoeff_tw_bas hp),
        (ev I ρ).app_comp, map_neg (GrOperad.map (R := R) (seqEquiv r b' (Fin l))),
        GrOperad.comp_assoc_seq, map_neg]

/-- **The merge lemma**: the decorations at the two ends of an edge without `h` compose in `P` as
they merge in the bar construction, `κ(x ⊛ᵢ y) = -κ(x̃) ∘ᵢ y`, with `x̃` the sign twist of `x`
and `y` marked with `p` at its root. -/
theorem ev_mR_mcomp (κ : Kind) (i : A) (x : FreeGr R gpB A) (y : FreeGr R gpB B) :
    (ev I ρ).app _ (mR I (setK κ) _ (𝔪c i x y))
      = -GrOperad.comp (R := R) i
          ((ev I ρ).app A (mR I (setK κ) A (GrSpecies.tw (R := R) (V := FreeGr R gpB) true x)))
          ((ev I ρ).app B (mR I (setK .p) B y)) := by
  induction x using induction_bas with
  | zero => simp
  | add x x' hx hx' =>
    simp only [map_add, LinearMap.add_apply, hx, hx', neg_add]
  | bas c s =>
    simp only [map_smul, LinearMap.smul_apply]
    rw [← smul_neg]
    refine congrArg _ ?_
    induction y using induction_bas with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy', neg_add]
    | bas c' t =>
      simp only [map_smul]
      rw [← smul_neg]
      refine congrArg _ ?_
      revert s i
      refine bas_induction (motive := fun Y _ _ y => ∀ (i : A)
        (s : Reg (TreeOfArity (BarT I)) A), (ev I ρ).app _ (mR I (setK κ) _ (𝔪c i (𝔟 s) y))
          = -GrOperad.comp (R := R) i
            ((ev I ρ).app A (mR I (setK κ) A (GrSpecies.tw (R := R) (V := FreeGr R gpB) true
              (𝔟 s))))
            ((ev I ρ).app Y (mR I (setK .p) Y y))) ?_ ?_ ?_ ?_ ?_ B t
      · intro Y _ _ c y hy i s
        rw [map_smul, map_smul, map_smul, hy i s, map_smul, map_smul, map_smul, smul_neg]
      · intro Y Y' _ _ _ _ e y hy i s
        have h := mcomp_map (μ := barMerge I) (gp := gpB) (R := R) (Equiv.refl A) e i (𝔟 s) y
        rw [GrOperad.map_refl] at h
        have hc := GrOperad.map_comp (R := R) (Equiv.refl A) e i
          ((ev I ρ).app A (mR I (setK κ) A (GrSpecies.tw (R := R) (V := FreeGr R gpB) true
            (𝔟 s))))
          ((ev I ρ).app Y (mR I (setK .p) Y y))
        rw [GrOperad.map_refl] at hc
        rw [show i = (Equiv.refl A) i from rfl, h, mR_map, (ev I ρ).app_map, hy i s, mR_map,
          (ev I ρ).app_map, ← hc, map_neg]
      · intro Y _ _ t ht i s
        rw [mcomp_leaf_right _ ht, map_zero, map_zero, mR_bas_leaf _ ht, map_zero, map_zero,
          neg_zero]
      · intro l b i s
        exact ev_mR_mcomp_right ρ b A s i κ
      · intro B1 B2 _ _ _ _ j q1 q2 hq1 hq2 ihq1 _ i s
        rw [← comp_mcomp_outer (barMerge I) i j (𝔟 s) (𝔟 q1) (𝔟 q2) (unitCoeff_bas_of hq1),
          mR_map, (ev I ρ).app_map, mR_comp _ _ (unitCoeff_mcomp _ _ _), (ev I ρ).app_comp,
          ihq1 i s, mR_comp _ _ (unitCoeff_bas_of hq1), (ev I ρ).app_comp,
          ← GrOperad.comp_assoc_seq]
        simp only [LinearMap.neg_apply, map_neg]

end MergeInd

/-! ## The bar differential -/

section BarD

variable (ρ : OpRetract R P)

local notation "gpB" => grGenPar R (BarGen I)
local notation "𝔡" => barD (barMerge I) (grGenPar R (BarGen I)) R

lemma ev_mR_gE_mcomp (i : A) (x : FreeGr R gpB A) (y : FreeGr R gpB B) :
    (ev I ρ).app _ (mR I gE _ (mcomp (barMerge I) gpB R i x y))
      = -GrOperad.comp (R := R) i
          ((ev I ρ).app A (mR I gE A (GrSpecies.tw (R := R) (V := FreeGr R gpB) true x)))
          ((ev I ρ).app B (mR I (setK .p) B y)) := by
  rw [mR_gE, mR_gE]
  exact ev_mR_mcomp ρ .e i x y

lemma ev_nH_mcomp {p : Reg (TreeOfArity (BarT I)) A} (hp : (treeOf p).isLeaf = false) (i : A)
    (y : FreeGr R gpB B) :
    (ev I ρ).app _ (nH I _ (mcomp (barMerge I) gpB R i (SgnLin.bas (treeSgn gpB) R p) y))
      = -GrOperad.comp (R := R) i
          ((ev I ρ).app A (nH I A (GrSpecies.tw (R := R) (V := FreeGr R gpB) true
            (SgnLin.bas (treeSgn gpB) R p))))
          ((ev I ρ).app B (mR I (setK .p) B y)) := by
  rw [nH_eq_mR (unitCoeff_mcomp _ _ _), ev_mR_mcomp, nH_eq_mR (unitCoeff_tw_bas hp)]

lemma weight_std {k : ℕ} (a : BarT I k) :
    (treeOf (Reg.std (corolla a) : Reg (TreeOfArity (BarT I)) (Fin k))).weight = 1 := by
  show (Tree.node a (TreeOfArity.leaves k)).weight = 1
  rw [Tree.weight_node, weightF_leaves]

lemma barD_gen {k : ℕ} (a : BarT I k) : 𝔡 (Fin k) (gen (R := R) (gp := gpB) a) = 0 := by
  rw [FreeGr.gen, barD_bas, weight_std, Finset.Ico_self, Finset.sum_empty]

/-- **Turning the vertices into kind `p`, with every vertex of kind `h`**:
`D_p ∘ n = m_p - n ∘ d_B`. -/
theorem ev_vD_gP_nH (x : FreeGr R gpB A) :
    (ev I ρ).app A (vD gP mpar R A (nH I A x))
      = (ev I ρ).app A (mR I (setK .p) A x) - (ev I ρ).app A (nH I A (𝔡 A x)) := by
  induction x using induction_bas with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | bas c t =>
    simp only [map_smul, ← smul_sub]
    refine congrArg _ ?_
    refine bas_induction (motive := fun X _ _ x => (ev I ρ).app X (vD gP mpar R X (nH I X x))
      = (ev I ρ).app X (mR I (setK .p) X x) - (ev I ρ).app X (nH I X (𝔡 X x))) ?_ ?_ ?_ ?_ ?_ A t
    · intro X _ _ c x hx
      simp only [map_smul, hx, smul_sub]
    · intro X Y _ _ _ _ e x hx
      rw [nH_map, ← map_vD, (ev I ρ).app_map, hx, mR_map, ← map_barD, nH_map, (ev I ρ).app_map,
        (ev I ρ).app_map, map_sub]
    · intro X _ _ t ht
      rw [nH_bas, vD_bas_of_weight (by
          rw [FreeReg.treeOf_relabelR, Tree.eq_leaf_of_isLeaf ht]; rfl),
        mR_bas_leaf _ ht, barD_bas_of_isLeaf ht]
      simp
    · intro k a
      rw [nH_gen, vD_gen, barD_gen, map_zero, map_zero, sub_zero, mR_gen]
      rfl
    · intro A' B' _ _ _ _ r p q hp hq ihp ihq
      rw [nH_comp, vD_comp gP_par, map_add, (ev I ρ).app_comp, (ev I ρ).app_comp, ihp, ihq,
        nH_tw, mR_comp_bas _ r hp q, (ev I ρ).app_comp, barD_comp_bas barMerge_odd]
      simp only [map_add, map_smul, nH_comp, (ev I ρ).app_comp]
      rw [ev_nH_mcomp ρ hp, tw_bas]
      simp only [map_sub, LinearMap.sub_apply, LinearMap.smul_apply, map_smul]
      abel

end BarD

section BarDE

variable (ρ : OpRetract R P)

local notation "gpB" => grGenPar R (BarGen I)
local notation "𝔡" => barD (barMerge I) (grGenPar R (BarGen I)) R

/-- **The bar differential has no unit component.** -/
lemma unitCoeff_barD (x : FreeGr R gpB A) : unitCoeff gpB R A (𝔡 A x) = 0 := by
  induction x using induction_bas with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | bas c s =>
    rw [map_smul, map_smul, barD_bas, map_sum]
    refine (congrArg _ (Finset.sum_eq_zero fun k hk => ?_)).trans (smul_zero c)
    rw [Finset.mem_Ico] at hk
    rw [map_smul, unitCoeff_bas, if_neg, smul_zero]
    intro h
    have hw := Tree.weight_contr (barMerge I) hk.1 hk.2
    rw [← treeOf_contrR, Tree.eq_leaf_of_isLeaf h, Tree.weight_leaf] at hw
    omega

/-- **Turning the vertices into kind `p`, with the root of kind `e`**:
`D_p ∘ v = m_h + v ∘ d_B`, the first term the root turned into kind `h`. -/
theorem ev_vD_gP_mR (x : FreeGr R gpB A) :
    (ev I ρ).app A (vD gP mpar R A (mR I gE A x))
      = (ev I ρ).app A (mR I (setK .h) A x) + (ev I ρ).app A (mR I gE A (𝔡 A x)) := by
  induction x using induction_bas with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | bas c t =>
    simp only [map_smul, ← smul_add]
    refine congrArg _ ?_
    refine bas_induction (motive := fun X _ _ x => (ev I ρ).app X (vD gP mpar R X (mR I gE X x))
      = (ev I ρ).app X (mR I (setK .h) X x) + (ev I ρ).app X (mR I gE X (𝔡 X x))) ?_ ?_ ?_ ?_ ?_
      A t
    · intro X _ _ c x hx
      simp only [map_smul, hx, smul_add]
    · intro X Y _ _ _ _ e x hx
      rw [mR_map, ← map_vD, (ev I ρ).app_map, hx, mR_map, ← map_barD, mR_map, (ev I ρ).app_map,
        (ev I ρ).app_map, map_add]
    · intro X _ _ t ht
      rw [mR_bas_leaf _ ht, mR_bas_leaf _ ht, barD_bas_of_isLeaf ht]
      simp
    · intro k a
      rw [mR_gen, vD_gen, barD_gen, map_zero, map_zero, add_zero, mR_gen]
      rfl
    · intro A' B' _ _ _ _ r p q hp hq ihp _
      rw [mR_comp_bas _ r hp q, vD_comp gP_par, map_add, (ev I ρ).app_comp, (ev I ρ).app_comp,
        ihp, ev_vD_gP_nH, mR_tw gE_par, mR_comp_bas _ r hp q, (ev I ρ).app_comp,
        barD_comp_bas barMerge_odd]
      simp only [map_add, map_smul]
      rw [mR_comp _ _ (unitCoeff_barD _), mR_comp _ _ (unitCoeff_bas_of hp), ev_mR_gE_mcomp,
        tw_bas]
      simp only [map_sub, map_smul, map_neg, (ev I ρ).app_comp, LinearMap.add_apply,
        LinearMap.smul_apply, LinearMap.neg_apply]
      abel

end BarDE

/-! ## Cuts -/

section Cut

variable (ρ : OpRetract R P)

local notation "gpB" => grGenPar R (BarGen I)

variable (I) in
/-- **The van der Laan map on trees with homogeneous decorations**, as an invariant family of the
convolution operad: `ev` on the tree with its root of kind `e`. -/
noncomputable def vF : GrOperad.Inv R (ConvOp R (FreeGr R gpB) P) :=
  ⟨fun A _ _ => ConvOp.of ((ev I ρ).app A ∘ₗ mR I gE A), fun A B _ _ _ _ e => by
    show ConvOp.mapC e (ConvOp.of ((ev I ρ).app A ∘ₗ mR I gE A))
      = ConvOp.of ((ev I ρ).app B ∘ₗ mR I gE B)
    ext x
    rw [ConvOp.mapC_apply]
    show GrOperad.map (R := R) e ((ev I ρ).app A (mR I gE A (GrOperad.map (R := R) e.symm x)))
      = (ev I ρ).app B (mR I gE B x)
    rw [← (ev I ρ).app_map, ← mR_map, ← GrOperad.map_trans, Equiv.symm_trans_self,
      GrOperad.map_refl]⟩

lemma vF_apply (x : FreeGr R gpB A) :
    ConvOp.toLin ((vF I ρ).1 A) x = (ev I ρ).app A (mR I gE A x) := rfl

lemma isParC_vF (A : Type) [Fintype A] [DecidableEq A] : ConvOp.IsParC true ((vF I ρ).1 A) := by
  intro c x
  show (ev I ρ).app A (mR I gE A (GrOperad.par (R := R) c x))
    = GrOperad.par (R := R) (xor c true) ((ev I ρ).app A (mR I gE A x))
  have h := mR_par gE_par (!c) x
  rw [Bool.not_not] at h
  rw [h, (ev I ρ).app_par, Bool.xor_true]

lemma vF_leaf (A : Type) [Fintype A] [DecidableEq A] (x : Reg (TreeOfArity (BarT I)) A)
    (hx : (treeOf x).isLeaf = true) :
    ConvOp.toLin ((vF I ρ).1 A) (SgnLin.bas (treeSgn gpB) R x) = 0 := by
  rw [vF_apply, mR_bas_leaf _ hx, map_zero]

lemma relabelAtR_map {T : ℕ → Type v} (g : ∀ k, T k → T k) (e : A ≃ B)
    (x : Reg (TreeOfArity T) A) (k : ℕ) :
    relabelAtR g (SetOperad.map e x) k = SetOperad.map e (relabelAtR g x k) :=
  reg_ext rfl rfl

/-- **Turning the vertex of a factorization into kind `e`** is minus the term of the
factorization in the convolution square of the van der Laan map. -/
lemma ev_relabelAt_rep {A' B' : Type} [Fintype A'] [DecidableEq A'] [Fintype B']
    [DecidableEq B'] {i : A'} {p : Reg (TreeOfArity (BarT I)) A'}
    {q : Reg (TreeOfArity (BarT I)) B'} (e : Without A' i ⊕ B' ≃ A)
    (hp : (treeOf p).isLeaf = false) (hq : (treeOf q).isLeaf = false) :
    σ R (Tree.bpar mpar (treeOf (mrkR gE (SetOperad.map e (SetOperad.comp i p q)))) (vert i p)) •
        (ev I ρ).app A (SgnLin.bas (treeSgn mpar) R
          (relabelAtR gE (mrkR gE (SetOperad.map e (SetOperad.comp i p q))) (vert i p)))
      = -repW (vF I ρ) (vF I ρ) e p q := by
  have hmk : mrkR gE (SetOperad.map e (SetOperad.comp i p q))
      = SetOperad.map e (SetOperad.comp i (mrkR gE p) (FreeReg.relabelR hK q)) := by
    rw [mrkR_map, mrkR_comp gE i p q hp]
  have hq' : (treeOf (FreeReg.relabelR hK q)).isLeaf = false := by
    rw [FreeReg.treeOf_relabelR, isLeaf_relabel, hq]
  have hw := Tree.one_le_weight hq'
  have hvb : vert i p = (treeOf (mrkR gE p)).vb ((mrkR gE p).1.rank i) + 0 := by
    rw [treeOf_mrkR, Tree.vb_relabelAt, Tree.vb_relabel, mrkR_fst, Nat.add_zero]
  have hrel : relabelAtR gE (SetOperad.comp i (mrkR gE p) (FreeReg.relabelR hK q)) (vert i p)
      = SetOperad.comp i (mrkR gE p) (mrkR gE q) := by
    rw [hvb]
    exact relabelAtR_comp_inner gE i _ _ (k := 0) (by omega)
  have hr := rank_lt_arity (mrkR gE p) i
  have hx := Tree.bpar_vb_xor_apar mpar (treeOf (mrkR gE p)) ((mrkR gE p).1.rank i) hr
  rw [tpar_mrkR gE_par hp, apar_mrkR, mrkR_fst] at hx
  have hbp : Tree.bpar mpar (treeOf (mrkR gE (SetOperad.map e (SetOperad.comp i p q))))
      (vert i p) = xor (!Tree.tpar gpB (treeOf p)) (Tree.apar gpB (treeOf p) (p.1.rank i)) := by
    rw [hmk, treeOf_map, treeOf_comp, hvb, Tree.bpar_graft_inner mpar _ _ _ _ hr (by omega),
      Tree.bpar_zero, Bool.xor_false, mrkR_fst, ← hx, Bool.xor_assoc, Bool.xor_self,
      Bool.xor_false]
  rw [hbp, hmk, relabelAtR_map, hrel, ← SgnLin.map_bas, (ev I ρ).app_map, bas_comp, map_smul,
    (ev I ρ).app_comp, ← mR_bas gE hp, ← mR_bas gE hq, tpar_mrkR gE_par hq, apar_mrkR, mrkR_fst]
  unfold repW
  rw [vF_apply, vF_apply, tw_bas, map_smul, map_smul]
  simp only [map_smul, LinearMap.smul_apply, smul_smul, ← neg_smul]
  congr 1
  show _ = -(σ R (Tree.tpar gpB (treeOf q) && Tree.apar gpB (treeOf p) (p.1.rank i)) * _)
  cases Tree.tpar gpB (treeOf p) <;> cases Tree.tpar gpB (treeOf q) <;>
    cases Tree.apar gpB (treeOf p) (p.1.rank i) <;> simp [σ]

/-- **Turning the vertex at a cut into kind `e`**. -/
lemma ev_relabelAt_cut (t : Reg (TreeOfArity (BarT I)) A) {v : ℕ} (hv1 : 1 ≤ v)
    (hv : v < (treeOf t).weight) :
    σ R (Tree.bpar mpar (treeOf (mrkR gE t)) v) •
        (ev I ρ).app A (SgnLin.bas (treeSgn mpar) R (relabelAtR gE (mrkR gE t) v))
      = -starV (vF I ρ) (vF I ρ) t v := by
  obtain ⟨e, he⟩ := exists_rep t hv
  have hp : (treeOf (stdT ((treeOf t).cutV v).1)).isLeaf = false :=
    Tree.isLeaf_cutV_fst hv1 hv rfl
  have hq : (treeOf (stdT ((treeOf t).cutV v).2.1)).isLeaf = false := Tree.isLeaf_cutV _ _ hv
  have hvert : vert ⟨((treeOf t).cutV v).2.2, Tree.lt_arity_cutV _ v hv⟩
      (stdT ((treeOf t).cutV v).1) = v := by
    show (treeOf (stdT _)).vb ((stdT _).1.rank _) = v
    rw [treeOf_stdT, rank_stdT]
    exact Tree.vb_cutV _ _ hv
  rw [← hvert, starV_eq _ _ he hq, ← ev_relabelAt_rep ρ e hp hq, he]

end Cut

/-! ## The cut part of the differential -/

section CutSum

variable (ρ : OpRetract R P)

local notation "gpB" => grGenPar R (BarGen I)

lemma relabelAtR_mrkR_zero (t : Reg (TreeOfArity (BarT I)) A) :
    relabelAtR gE (mrkR gE t) 0 = mrkR (setK .h) t :=
  reg_ext rfl (by
    rw [treeOf_relabelAtR, treeOf_mrkR, treeOf_mrkR, relabelAt_relabelAt_zero]
    generalize treeOf t = T
    cases T with
    | leaf => rfl
    | node a f =>
      rw [Tree.relabel_node]
      rfl)

lemma weight_mrkR (r : ∀ k, MT I k → MT I k) (t : Reg (TreeOfArity (BarT I)) A) :
    (treeOf (mrkR r t)).weight = (treeOf t).weight := by
  rw [treeOf_mrkR, Tree.weight_relabelAt, Tree.weight_relabel]

/-- **Turning the vertices into kind `e`, with the root of kind `e`**: `D_e ∘ v = m_h - v ⋆ v` on a
tree without vertices without inputs, the first term the root turned into kind `h`. -/
theorem ev_vD_gE_mR (t : Reg (TreeOfArity (BarT I)) A) (ht : (treeOf t).NoNull) :
    (ev I ρ).app A (vD gE mpar R A (mR I gE A (SgnLin.bas (treeSgn gpB) R t)))
      = (ev I ρ).app A (mR I (setK .h) A (SgnLin.bas (treeSgn gpB) R t))
        - ConvOp.toLin ((GrOperad.Inv.star R _ (vF I ρ) (vF I ρ)).1 A)
            (SgnLin.bas (treeSgn gpB) R t) := by
  rw [star_bas (vF I ρ) (vF I ρ) (isParC_vF ρ) (vF_leaf ρ) (vF_leaf ρ)]
  by_cases hl : (treeOf t).isLeaf = true
  · rw [mR_bas_leaf _ hl, mR_bas_leaf _ hl, Tree.eq_leaf_of_isLeaf hl]
    simp
  have hl' : (treeOf t).isLeaf = false := by simpa using hl
  have hw := Tree.one_le_weight hl'
  rw [mR_bas _ hl', mR_bas _ hl', vD_bas, weight_mrkR, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (by omega), Tree.bpar_zero, σ_false, one_smul, map_add,
    relabelAtR_mrkR_zero, map_sum,
    Finset.filter_true_of_mem fun v hv => Tree.NoNull.arity_pos
      (Tree.NoNull.cutV ht (Finset.mem_Ico.1 hv).2).2,
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun v hv => ?_)
  rw [Finset.mem_Ico] at hv
  rw [map_smul, ev_relabelAt_cut ρ t hv.1 hv.2]

end CutSum

/-! ## Descent to the bar construction -/

section Descent

variable (ρ : OpRetract R P)

local notation "gpB" => grGenPar R (BarGen I)
local notation "𝒥" => GrOperadIdeal.span R (grLinRel R (BarGen I))

lemma ev_mR_comp_right (i : A) (x : FreeGr R gpB A) {y : FreeGr R gpB B}
    (hy1 : (ev I ρ).app B (nH I B y) = 0) (hy2 : (ev I ρ).app B (mR I gE B y) = 0) :
    (ev I ρ).app _ (mR I gE _ (GrOperad.comp (R := R) i x y)) = 0 := by
  induction x using induction_bas with
  | zero => simp
  | add x x' hx hx' => rw [map_add, LinearMap.add_apply, map_add, map_add, hx, hx', add_zero]
  | bas c s =>
    rw [map_smul, LinearMap.smul_apply, map_smul, map_smul]
    by_cases hs : (treeOf s).isLeaf = true
    · obtain ⟨E, hE⟩ := comp_leaf_bas (R := R) (gp := gpB) hs i y
      rw [hE, mR_map, (ev I ρ).app_map, hy2, map_zero, smul_zero]
    · rw [mR_comp _ i (unitCoeff_bas_of (by simpa using hs)) y, (ev I ρ).app_comp, hy1, map_zero,
        smul_zero]

variable (I) in
/-- **The operations killed by the van der Laan map**, with their marking by `h`: an ideal. -/
noncomputable def kerJ : GrOperadIdeal R (FreeGr R gpB) where
  sub A _ _ :=
    { carrier := {x | (ev I ρ).app A (nH I A x) = 0 ∧ (ev I ρ).app A (mR I gE A x) = 0 ∧
        unitCoeff gpB R A x = 0}
      add_mem' := fun ha hb => ⟨by rw [map_add, map_add, ha.1, hb.1, add_zero],
        by rw [map_add, map_add, ha.2.1, hb.2.1, add_zero],
        by rw [map_add, ha.2.2, hb.2.2, add_zero]⟩
      zero_mem' := ⟨by simp, by simp, by simp⟩
      smul_mem' := fun c x hx => ⟨by rw [map_smul, map_smul, hx.1, smul_zero],
        by rw [map_smul, map_smul, hx.2.1, smul_zero],
        by rw [map_smul, hx.2.2, smul_zero]⟩ }
  par_mem {A} _ _ b x hx := ⟨by rw [nH_par, (ev I ρ).app_par, hx.1, map_zero], by
      have h := mR_par gE_par (!b) x
      rw [Bool.not_not] at h
      rw [h, (ev I ρ).app_par, hx.2.1, map_zero],
    by rw [unitCoeff_par, hx.2.2]; split_ifs <;> rfl⟩
  map_mem e x hx := ⟨by rw [nH_map, (ev I ρ).app_map, hx.1, map_zero],
    by rw [mR_map, (ev I ρ).app_map, hx.2.1, map_zero], by rw [unitCoeff_map, hx.2.2]⟩
  comp_mem_left i x y hx := ⟨by rw [nH_comp, (ev I ρ).app_comp, hx.1, LinearMap.map_zero₂],
    by rw [mR_comp _ _ hx.2.2, (ev I ρ).app_comp, hx.2.1, LinearMap.map_zero₂],
    by rw [unitCoeff_comp, hx.2.2, zero_mul]⟩
  comp_mem_right i x y hy := ⟨by rw [nH_comp, (ev I ρ).app_comp, hy.1, map_zero],
    ev_mR_comp_right ρ i x hy.1 hy.2.1, by rw [unitCoeff_comp, hy.2.2, mul_zero]⟩

lemma kval_add (κ : Kind) (x y : P A) : kval ρ κ (x + y) = kval ρ κ x + kval ρ κ y := by
  cases κ <;> simp [kval] <;> abel

lemma ev_mR_lgen (r : ∀ k, MT I k → MT I k) {k : ℕ} (v : BarGen I (Fin k)) (b : Bool)
    (h : GrSpecies.par (R := R) b v = v) :
    (ev I ρ).app (Fin k) (mR I r (Fin k) (lgen v b h)) = mval ρ k (r k (hK k ⟨(v, b), h⟩)) := by
  rw [lgen, mR_gen, ev_gen]

lemma ev_nH_lgen {k : ℕ} (v : BarGen I (Fin k)) (b : Bool)
    (h : GrSpecies.par (R := R) b v = v) :
    (ev I ρ).app (Fin k) (nH I (Fin k) (lgen v b h)) = mval ρ k (hK k ⟨(v, b), h⟩) := by
  rw [lgen, nH_gen, ev_gen]

lemma unitCoeff_lgen {k : ℕ} (v : BarGen I (Fin k)) (b : Bool)
    (h : GrSpecies.par (R := R) b v = v) : unitCoeff gpB R (Fin k) (lgen v b h) = 0 := by
  rw [lgen, FreeGr.gen, unitCoeff_bas]
  exact if_neg Bool.false_ne_true

/-- **The linearity relations are killed.** -/
lemma rel_mem_kerJ (n : ℕ) : grLinRel R (BarGen I) n ⊆ (kerJ I ρ).sub (Fin n) := by
  have hval : ∀ (κ : Kind) {k : ℕ} (v : BarGen I (Fin k)) (b : Bool)
      (h : GrSpecies.par (R := R) b v = v),
      mval ρ k ((κ, ⟨(v, b), h⟩) : MT I k) = kval ρ κ (IdealSp.val I v) := fun _ _ _ _ _ => rfl
  rintro x ((⟨b, v, w, hv, hw, rfl⟩ | ⟨b, c, v, hv, rfl⟩) | ⟨b, τ, v, hv, rfl⟩)
  · refine ⟨?_, ?_, ?_⟩
    · rw [map_sub, map_sub, map_sub, map_sub, ev_nH_lgen, ev_nH_lgen, ev_nH_lgen]
      show kval ρ .h (IdealSp.val I (v + w)) - kval ρ .h (IdealSp.val I v)
        - kval ρ .h (IdealSp.val I w) = 0
      rw [show IdealSp.val I (v + w) = IdealSp.val I v + IdealSp.val I w from rfl, kval_add]
      abel
    · rw [map_sub, map_sub, map_sub, map_sub, ev_mR_lgen, ev_mR_lgen, ev_mR_lgen]
      show kval ρ .e (IdealSp.val I (v + w)) - kval ρ .e (IdealSp.val I v)
        - kval ρ .e (IdealSp.val I w) = 0
      rw [show IdealSp.val I (v + w) = IdealSp.val I v + IdealSp.val I w from rfl, kval_add]
      abel
    · rw [map_sub, map_sub, unitCoeff_lgen, unitCoeff_lgen, unitCoeff_lgen, sub_zero, sub_zero]
  · refine ⟨?_, ?_, ?_⟩
    · rw [map_sub, map_sub, map_smul, map_smul, ev_nH_lgen, ev_nH_lgen]
      show kval ρ .h (IdealSp.val I (c • v)) - c • kval ρ .h (IdealSp.val I v) = 0
      rw [show IdealSp.val I (c • v) = c • IdealSp.val I v from rfl, kval_smul, sub_self]
    · rw [map_sub, map_sub, map_smul, map_smul, ev_mR_lgen, ev_mR_lgen]
      show kval ρ .e (IdealSp.val I (c • v)) - c • kval ρ .e (IdealSp.val I v) = 0
      rw [show IdealSp.val I (c • v) = c • IdealSp.val I v from rfl, kval_smul, sub_self]
    · rw [map_sub, map_smul, unitCoeff_lgen, unitCoeff_lgen, smul_zero, sub_zero]
  · refine ⟨?_, ?_, ?_⟩
    · rw [map_sub, map_sub, nH_map, (ev I ρ).app_map, ev_nH_lgen, ev_nH_lgen]
      show GrOperad.map (R := R) τ (kval ρ .h (IdealSp.val I v))
        - kval ρ .h (IdealSp.val I (SymSpecies.map (R := R) τ v)) = 0
      rw [show IdealSp.val I (SymSpecies.map (R := R) τ v)
        = GrOperad.map (R := R) τ (IdealSp.val I v) from rfl, kval_map, sub_self]
    · rw [map_sub, map_sub, mR_map, (ev I ρ).app_map, ev_mR_lgen, ev_mR_lgen]
      show GrOperad.map (R := R) τ (kval ρ .e (IdealSp.val I v))
        - kval ρ .e (IdealSp.val I (SymSpecies.map (R := R) τ v)) = 0
      rw [show IdealSp.val I (SymSpecies.map (R := R) τ v)
        = GrOperad.map (R := R) τ (IdealSp.val I v) from rfl, kval_map, sub_self]
    · rw [map_sub, unitCoeff_map, unitCoeff_lgen, unitCoeff_lgen, sub_zero]

lemma span_le_kerJ : 𝒥 ≤ kerJ I ρ := GrOperadIdeal.span_le.2 (rel_mem_kerJ ρ)

end Descent

end VdL

/-! ## The van der Laan map on the bar construction -/

namespace Bar

open VdL

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [DGOperad R P]
  {I : GrOperadIdeal R P} (ρ : OpRetract R P)
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

local notation "𝒥" => GrOperadIdeal.span R (grLinRel R (BarGen I))
local notation "𝒞" => FreeGrL R (BarGen I)
local notation "gpB" => grGenPar R (BarGen I)
local notation "𝔟" => SgnLin.bas (treeSgn (grGenPar R (BarGen I))) R

variable (I) in
/-- **The van der Laan map** `B(P, I) → P`: a tree goes to the composite in `P` of its
decorations, with `h` on its internal edges and `e` at its root. -/
noncomputable def vdLL (A : Type) [Fintype A] [DecidableEq A] : 𝒞 A →ₗ[R] P A :=
  ((𝒥).sub A).liftQ ((ev I ρ).app A ∘ₗ mR I gE A) fun _ hx => (span_le_kerJ ρ A hx).2.1

lemma vdLL_proj (x : FreeGr R gpB A) : vdLL I ρ A ((𝒥).proj A x) = (ev I ρ).app A (mR I gE A x) :=
  rfl

lemma vdLL_map (e : A ≃ B) (X : 𝒞 A) :
    vdLL I ρ B (GrOperad.map (R := R) e X) = GrOperad.map (R := R) e (vdLL I ρ A X) := by
  obtain ⟨x, rfl⟩ := (𝒥).proj_surjective A X
  rw [← proj_map', vdLL_proj, vdLL_proj, mR_map, (ev I ρ).app_map]

lemma vdLL_par (c : Bool) (X : 𝒞 A) :
    vdLL I ρ A (GrOperad.par (R := R) c X) = GrOperad.par (R := R) (!c) (vdLL I ρ A X) := by
  obtain ⟨x, rfl⟩ := (𝒥).proj_surjective A X
  show (ev I ρ).app A (mR I gE A (GrOperad.par (R := R) c x)) = _
  have h := mR_par gE_par (!c) x
  rw [Bool.not_not] at h
  rw [h, (ev I ρ).app_par]
  rfl

lemma vdLL_one : vdLL I ρ Unit (GrOperad.one (R := R)) = 0 := by
  rw [← (𝒥).projHom.app_one]
  show (ev I ρ).app Unit (mR I gE Unit (SgnLin.bas (treeSgn gpB) R SetOperad.one)) = 0
  rw [mR_bas_leaf _ rfl, map_zero]

variable (I) in
/-- **The van der Laan map**, as an invariant family of the convolution operad. -/
noncomputable def vdL : GrOperad.Inv R (ConvOp R (BarCoop I) P) :=
  ⟨fun A _ _ => ConvOp.of (vdLL I ρ A), fun A B _ _ _ _ e => by
    show ConvOp.mapC e (ConvOp.of (vdLL I ρ A)) = ConvOp.of (vdLL I ρ B)
    ext X
    rw [ConvOp.mapC_apply]
    show GrOperad.map (R := R) e (vdLL I ρ A (GrOperad.map (R := R) e.symm X)) = vdLL I ρ B X
    rw [← vdLL_map, ← GrOperad.map_trans, Equiv.symm_trans_self, GrOperad.map_refl]⟩

lemma vdL_apply (X : 𝒞 A) : ConvOp.toLin ((vdL I ρ).1 A) X = vdLL I ρ A X := rfl

/-- **The van der Laan map is odd.** -/
lemma isPar_vdL : GrOperad.Inv.IsPar true (vdL I ρ) := by
  intro A _ _
  show ConvOp.parC true (ConvOp.of (vdLL I ρ A)) = ConvOp.of (vdLL I ρ A)
  rw [ConvOp.parC_eq_self_iff]
  intro c X
  rw [ConvOp.toLin_of, Bool.xor_true]
  exact vdLL_par ρ c X

/-- **The van der Laan map vanishes on the coaugmentation.** -/
lemma killsUnit_vdL : KillsUnit R (BarCoop I) P (vdL I ρ) := by
  intro A _ _ x hx
  show vdLL I ρ A x = 0
  refine Submodule.span_induction (p := fun x _ => vdLL I ρ A x = 0) ?_ (map_zero _) ?_ ?_ hx
  · rintro _ ⟨e, rfl⟩
    show vdLL I ρ A (GrOperad.map (R := R) e (GrOperad.one (R := R))) = 0
    rw [vdLL_map, vdLL_one, map_zero]
  · intro x y _ _ hx hy
    beta_reduce at hx hy ⊢
    rw [map_add, hx, hy, add_zero]
  · intro a x _ hx
    beta_reduce at hx ⊢
    rw [map_smul, hx, smul_zero]

lemma appHom_vdL : GrOperad.Inv.appHom (ConvOp.preHom (P := P) (projB I)) (vdL I ρ) = vF I ρ :=
  Subtype.ext (funext fun A => funext fun _ => funext fun _ => by
    rw [GrOperad.Inv.appHom_apply]
    ext x
    rw [ConvOp.preHom_app, LinearMap.comp_apply]
    rfl)

lemma star_vdL_proj (y : FreeGr R gpB A) :
    ConvOp.toLin ((GrOperad.Inv.star R _ (vdL I ρ) (vdL I ρ)).1 A) ((𝒥).proj A y)
      = ConvOp.toLin ((GrOperad.Inv.star R _ (vF I ρ) (vF I ρ)).1 A) y := by
  rw [← appHom_vdL, ← GrOperad.Inv.appHom_star]
  rfl

variable (hI : ∀ {A : Type} [Fintype A] [DecidableEq A] {x : P A}, x ∈ I.sub A →
    DGOperad.d (R := R) x ∈ I.sub A)

/-- **The Maurer–Cartan equation of the van der Laan map**, at an element: for the differential
`d_B + d_int` of the bar construction of the dg operad, `∂ (v X) + v (d X) + (v ⋆ v) X = 0`. -/
theorem vdL_mc (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0) (X : 𝒞 A) :
    DGOperad.d (R := R) (vdLL I ρ A X) + vdLL I ρ A (dTot hI A X)
      + ConvOp.toLin ((GrOperad.Inv.star R _ (vdL I ρ) (vdL I ρ)).1 A) X = 0 := by
  obtain ⟨x, rfl⟩ := (𝒥).proj_surjective A X
  have hV0 : ∀ v : BarGen I (Fin 0), v = 0 := fun v => IdealSp.ext I (hI0 _ (IdealSp.mem I v))
  have hbas : ∀ t : Reg (TreeOfArity (BarT I)) A,
      DGOperad.d (R := R) (vdLL I ρ A ((𝒥).proj A (𝔟 t)))
        + vdLL I ρ A (dTot hI A ((𝒥).proj A (𝔟 t)))
        + ConvOp.toLin ((GrOperad.Inv.star R _ (vdL I ρ) (vdL I ρ)).1 A)
            ((𝒥).proj A (𝔟 t)) = 0 := by
    intro t
    by_cases hn : (treeOf t).NoNull
    swap
    · rw [FreeGrL.proj_bas_eq_zero hV0 t hn]
      simp only [map_zero, zero_add]
      exact (ConvOp.toLin _).map_zero
    have e2 : vdLL I ρ A (dTot hI A ((𝒥).proj A (𝔟 t)))
        = (ev I ρ).app A (mR I gE A (barD (barMerge I) gpB R A (𝔟 t)))
          + (ev I ρ).app A (mR I gE A (vD (dB hI) gpB R A (𝔟 t))) := by
      rw [dTot, LinearMap.add_apply, d_proj, dInt_proj, ← map_add, vdLL_proj, map_add, map_add]
    have h1 := ev_vD_gE_mR ρ t hn
    have h2 := ev_vD_gP_mR ρ (𝔟 t)
    have h3 := ev_vD_gD hI ρ (𝔟 t)
    rw [vdLL_proj, e2, star_vdL_proj, d_ev' hI ρ]
    simp only [h1, h2, h3]
    abel
  have hS0 : ConvOp.toLin ((GrOperad.Inv.star R _ (vdL I ρ) (vdL I ρ)).1 A) (0 : 𝒞 A) = 0 :=
    (ConvOp.toLin _).map_zero
  have hSa : ∀ a b : 𝒞 A, ConvOp.toLin ((GrOperad.Inv.star R _ (vdL I ρ) (vdL I ρ)).1 A) (a + b)
      = ConvOp.toLin ((GrOperad.Inv.star R _ (vdL I ρ) (vdL I ρ)).1 A) a
        + ConvOp.toLin ((GrOperad.Inv.star R _ (vdL I ρ) (vdL I ρ)).1 A) b :=
    fun a b => (ConvOp.toLin _).map_add a b
  have hSs : ∀ (c : R) (a : 𝒞 A),
      ConvOp.toLin ((GrOperad.Inv.star R _ (vdL I ρ) (vdL I ρ)).1 A) (c • a)
        = c • ConvOp.toLin ((GrOperad.Inv.star R _ (vdL I ρ) (vdL I ρ)).1 A) a :=
    fun c a => (ConvOp.toLin _).map_smul c a
  induction x using induction_bas with
  | zero => simp only [map_zero, hS0, add_zero]
  | add x y hx hy =>
    have h := congrArg₂ (· + ·) hx hy
    simp only [add_zero] at h
    rw [← h]
    simp only [map_add, hSa]
    abel
  | bas c t =>
    simp only [map_smul, hSs, ← smul_add, hbas, smul_zero]

/-- **The van der Laan twisting morphism** `B(P, I) → P`, for the dg cooperad structure of the
bar construction of the dg operad. -/
noncomputable def vdLTw (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0) :
    letI : DGCooperad R (BarCoop I) := dgCooperad hI
    TwistingDG R (BarCoop I) P :=
  letI : DGCooperad R (BarCoop I) := dgCooperad hI
  ⟨vdL I ρ, isPar_vdL ρ, killsUnit_vdL ρ, Subtype.ext (funext fun A => funext fun _ =>
    funext fun _ => by
      ext X
      have htw : GrOperad.tw (R := R) true ((vdL I ρ).1 A) = -(vdL I ρ).1 A := by
        rw [GrOperad.tw_hom true (isPar_vdL ρ A), Bool.and_self, σ_true, neg_one_smul]
      show DGOperad.d (R := R) (ConvOp.toLin ((vdL I ρ).1 A) X)
          - ConvOp.toLin (GrOperad.tw (R := R) true ((vdL I ρ).1 A))
              (DGCooperad.d (R := R) X)
          + ConvOp.toLin ((GrOperad.Inv.star R _ (vdL I ρ) (vdL I ρ)).1 A) X = 0
      rw [htw, ConvOp.toLin_neg, LinearMap.neg_apply, sub_neg_eq_add]
      exact vdL_mc ρ hI hI0 X)⟩

/-- **The van der Laan map lands in the operations `x` with `e ∘ x = x`.** -/
theorem lcomp_vdLL (X : 𝒞 A) : GrOperad.lcomp R ρ.e (vdLL I ρ A X) = vdLL I ρ A X := by
  obtain ⟨x, rfl⟩ := (𝒥).proj_surjective A X
  rw [vdLL_proj]
  have key : ∀ y : FreeGr R gpB A, (ev I ρ).app A (mR I gE A y)
      = GrOperad.lcomp R ρ.e ((ev I ρ).app A (mR I (setK .p) A y)) := by
    intro y
    induction y using induction_bas with
    | zero => simp
    | add y y' hy hy' => rw [map_add, map_add, hy, hy', map_add, map_add, map_add]
    | bas c t =>
      rw [map_smul, map_smul, map_smul, map_smul, map_smul]
      refine congrArg _ ?_
      refine bas_induction (motive := fun X _ _ y => (ev I ρ).app X (mR I gE X y)
        = GrOperad.lcomp R ρ.e ((ev I ρ).app X (mR I (setK .p) X y))) ?_ ?_ ?_ ?_ ?_ A t
      · intro X _ _ c y hy
        rw [map_smul, map_smul, hy, map_smul, map_smul, map_smul]
      · intro X Y _ _ _ _ e y hy
        rw [mR_map, (ev I ρ).app_map, hy, mR_map, (ev I ρ).app_map, GrOperad.lcomp_map]
      · intro X _ _ t ht
        rw [mR_bas_leaf _ ht, mR_bas_leaf _ ht]
        simp
      · intro k a
        rw [mR_gen, ev_gen, ev_mR_gen]
        rfl
      · intro A' B' _ _ _ _ r p q hp _ ihp _
        rw [mR_comp_bas _ r hp q, (ev I ρ).app_comp, ihp, mR_comp_bas _ r hp q,
          (ev I ρ).app_comp, GrOperad.lcomp_comp]
  rw [key, GrOperad.lcomp_lcomp_eq, ρ.ee]

end Bar

end Operad
