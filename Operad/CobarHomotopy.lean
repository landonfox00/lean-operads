/-
# The contracting homotopy of the cobar construction of a cut cooperad

For the cobar construction `ΩC` of the cut cooperad `C = FreeGrL R V`, with its differential `d`
and the merge-composition `⊛` of the merge structure on its generators (`Cobar.mM`), **the
commutator `Ξ(x, y) = d (x ⊛ᵢ y) + d x ⊛ᵢ y + (-1)^{|x|} x ⊛ᵢ d y` is the composite of the parts
without unit component** (`Cobar.xiM_eq`), when there are no generators without inputs: on two
generators it is their composite (`Cobar.d_mM_ιL_bas`), and the laws of merge-composition
propagate it to all trees (`FreeGr.tree_induction`).
-/
import Operad.CobarMergeComm

universe u v

namespace Operad

open Sym GerBV TreeOfArity FreeGr
open scoped TensorProduct

namespace FreeGr

variable {T : ℕ → Type v}

/-- A forest of leaves has no vertex without inputs. -/
lemma noNullF_leaves : ∀ k : ℕ, (TreeOfArity.leaves (E := T) k).NoNullF
  | 0 => trivial
  | k + 1 => ⟨trivial, noNullF_leaves k⟩

/-- **Induction on labelled trees**: the trivial trees, the relabelled corollas, and the relabelled
composites of two trees with vertices. -/
theorem tree_induction
    {motive : ∀ (X : Type) [Fintype X] [DecidableEq X], Reg (TreeOfArity T) X → Prop}
    (hleaf : ∀ (X : Type) [Fintype X] [DecidableEq X] (x : Reg (TreeOfArity T) X),
      (treeOf x).isLeaf = true → motive X x)
    (hcor : ∀ (X : Type) [Fintype X] [DecidableEq X] (k : ℕ) (g : T k) (e : Fin k ≃ X),
      motive X (SetOperad.map e (Reg.std (corolla g))))
    (hcomp : ∀ (X A B : Type) [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Fintype B]
      [DecidableEq B] (r : A) (p : Reg (TreeOfArity T) A) (q : Reg (TreeOfArity T) B)
      (e : Without A r ⊕ B ≃ X), (treeOf p).isLeaf = false → (treeOf q).isLeaf = false →
        motive A p → motive B q → motive X (SetOperad.map e (SetOperad.comp r p q)))
    (X : Type) [Fintype X] [DecidableEq X] (x : Reg (TreeOfArity T) X) : motive X x := by
  suffices h : ∀ n, ∀ (X : Type) [Fintype X] [DecidableEq X] (x : Reg (TreeOfArity T) X),
      (treeOf x).weight = n → motive X x from h _ X x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X _ _ x hx
    by_cases hl : (treeOf x).isLeaf = true
    · exact hleaf X x hl
    have hl' : (treeOf x).isLeaf = false := by simpa using hl
    by_cases h1 : n = 1
    · obtain ⟨k, g, hg⟩ := eq_corolla_of_nVert (x := x) (by rw [nVert_eq, hx, h1])
      obtain ⟨e, he⟩ := exists_map_eq (x := Reg.std (corolla g)) (y := x) hg.symm
      rw [← he]
      exact hcor X k g e
    have h2 : 1 < (treeOf x).weight := by
      have := Tree.one_le_weight hl'
      omega
    obtain ⟨e, he⟩ := exists_rep x h2
    have hq := Tree.isLeaf_cutV _ _ h2
    have hp := Tree.isLeaf_cutV_fst le_rfl h2 rfl
    have hw := weight_rep he
    rw [treeOf_stdT, treeOf_stdT] at hw
    have w1 := Tree.one_le_weight hp
    have w2 := Tree.one_le_weight hq
    rw [← he]
    exact hcomp X _ _ _ _ _ e hp hq (ih _ (by simp only [treeOf_stdT]; omega) _ _ rfl)
      (ih _ (by simp only [treeOf_stdT]; omega) _ _ rfl)

end FreeGr

namespace FreeGrL

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

local notation "𝒥" => GrOperadIdeal.span R (grLinRel R V)

/-- **The unit coefficient is multiplicative.** -/
lemma unitCoeffL_comp (i : A) (X : FreeGrL R V A) (Y : FreeGrL R V B) :
    unitCoeffL R V _ (GrOperad.comp (R := R) i X Y) = unitCoeffL R V A X * unitCoeffL R V B Y := by
  obtain ⟨x, rfl⟩ := (𝒥).proj_surjective A X
  obtain ⟨y, rfl⟩ := (𝒥).proj_surjective B Y
  exact unitCoeff_comp i x y

lemma unitCoeffL_tw (e : Bool) (X : FreeGrL R V A) :
    unitCoeffL R V A (GrOperad.tw (R := R) e X) = unitCoeffL R V A X := by
  rw [GrOperad.tw_apply, map_add, map_smul, unitCoeffL_par, unitCoeffL_par, if_neg (by decide),
    if_pos rfl, smul_zero, add_zero]

/-- **A composite with a factor without unit component** has none. -/
lemma secC_comp {i : A} {X : FreeGrL R V A} (hX : unitCoeffL R V A X = 0) (Y : FreeGrL R V B) :
    secC R V _ (GrOperad.comp (R := R) i X Y) = GrOperad.comp (R := R) i X Y :=
  secC_of_unitCoeff (by rw [unitCoeffL_comp, hX, zero_mul])

/-! ### Basis elements -/

local notation "𝔟" => SgnLin.bas (treeSgn (grGenPar R V)) R

lemma proj_bas_map (e : A ≃ B) (x : Reg (TreeOfArity (GrGen R V)) A) :
    (𝒥).proj B (𝔟 (SetOperad.map e x)) = GrOperad.map (R := R) e ((𝒥).proj A (𝔟 x)) := by
  rw [← SgnLin.map_bas]
  rfl

/-- The class of a composite tree: the composite of the classes, with the sign of the composite. -/
lemma proj_bas_comp (r : A) (p : Reg (TreeOfArity (GrGen R V)) A)
    (q : Reg (TreeOfArity (GrGen R V)) B) :
    (𝒥).proj _ (𝔟 (SetOperad.comp r p q))
      = σ R (cSgn (grGenPar R V) r p q) •
          GrOperad.comp (R := R) r ((𝒥).proj A (𝔟 p)) ((𝒥).proj B (𝔟 q)) := by
  have h1 : GrOperad.comp (R := R) r ((𝒥).proj A (𝔟 p)) ((𝒥).proj B (𝔟 q))
      = σ R (cSgn (grGenPar R V) r p q) • (𝒥).proj _ (𝔟 (SetOperad.comp r p q)) := by
    show (𝒥).proj _ (GrOperad.comp (R := R) r _ _) = _
    rw [comp_bas_eq, map_smul]
  rw [h1, smul_smul, show σ R (cSgn (grGenPar R V) r p q) * σ R (cSgn (grGenPar R V) r p q) = 1
    by cases cSgn (grGenPar R V) r p q <;> simp, one_smul]

lemma proj_bas_one :
    (𝒥).proj Unit (𝔟 (SetOperad.one : Reg (TreeOfArity (GrGen R V)) Unit))
      = GrOperad.one (R := R) (P := FreeGrL R V) := rfl

/-- The class of a corolla is its generator. -/
lemma proj_bas_corolla {k : ℕ} (g : GrGen R V k) :
    (𝒥).proj (Fin k) (𝔟 (Reg.std (corolla g))) = (ι R V).app (Fin k) g.1.1 :=
  (ι_app_hom g.2).symm

/-- The class of a trivial tree is a relabelled unit. -/
lemma proj_bas_leaf {x : Reg (TreeOfArity (GrGen R V)) A} (hx : (treeOf x).isLeaf = true) :
    ∃ e : Unit ≃ A, (𝒥).proj A (𝔟 x) = GrOperad.map (R := R) e (GrOperad.one (R := R)) := by
  obtain ⟨e, rfl⟩ := eq_map_one_of_isLeaf hx
  exact ⟨e, proj_bas_map e _⟩

/-- **A tree with a vertex without inputs vanishes** when there are no generators without inputs. -/
theorem proj_bas_eq_zero (hV0 : ∀ v : V (Fin 0), v = 0) (x : Reg (TreeOfArity (GrGen R V)) A)
    (hx : ¬ (treeOf x).NoNull) : (𝒥).proj A (𝔟 x) = 0 := by
  revert hx
  refine tree_induction (motive := fun A _ _ x => ¬ (treeOf x).NoNull → (𝒥).proj A (𝔟 x) = 0)
    ?_ ?_ ?_ A x
  · intro X _ _ x hl hx
    rw [Tree.eq_leaf_of_isLeaf hl] at hx
    exact absurd Tree.noNull_leaf hx
  · intro X _ _ k g e hx
    rw [proj_bas_map, proj_bas_corolla]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [hV0 g.1.1, map_zero, map_zero]
    · exact absurd (show (corolla g).1.NoNull from ⟨hk, noNullF_leaves k⟩) hx
  · intro X A B _ _ _ _ _ _ r p q e _ _ hp hq hx
    rw [proj_bas_map, proj_bas_comp]
    rcases not_and_or.1 (fun h => hx (by rw [treeOf_map]; exact (noNull_comp r p q).2 h)) with h | h
    · rw [hp h, LinearMap.map_zero₂, smul_zero, map_zero]
    · rw [hq h, map_zero, smul_zero, map_zero]

end FreeGrL

namespace MergeSp

variable {R : Type u} [CommRing R] {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)] [GrSpecies R W]
  (M : MergeSp R W) {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

local notation "𝒥" => GrOperadIdeal.span R (grLinRel R W)

/-- **Merge-composition adds the parities, plus one.** -/
theorem par_mc {a b : Bool} (i : A) {X : FreeGrL R W A} {Y : FreeGrL R W B}
    (hX : GrOperad.par (R := R) a X = X) (hY : GrOperad.par (R := R) b Y = Y) :
    GrOperad.par (R := R) (!(xor a b)) (M.mc i X Y) = M.mc i X Y := by
  obtain ⟨x, rfl⟩ := (𝒥).proj_surjective A X
  obtain ⟨y, rfl⟩ := (𝒥).proj_surjective B Y
  rw [← hX, ← hY, ← proj_par', ← proj_par', mc_proj, ← proj_par', par_mcomp M.fn M.fn_odd,
    if_pos rfl]

/-- **The sign twist of a merge-composite**: `(-1)^{|x ⊛ y|} x ⊛ y = -((-1)^{|x|} x) ⊛ ((-1)^{|y|} y)`. -/
theorem tw_mc (i : A) (X : FreeGrL R W A) (Y : FreeGrL R W B) :
    GrOperad.tw (R := R) true (M.mc i X Y)
      = -M.mc i (GrOperad.tw (R := R) true X) (GrOperad.tw (R := R) true Y) := by
  have key : ∀ a b : Bool, GrOperad.tw (R := R) true
      (M.mc i (GrOperad.par (R := R) a X) (GrOperad.par (R := R) b Y))
      = -M.mc i (GrOperad.tw (R := R) true (GrOperad.par (R := R) a X))
          (GrOperad.tw (R := R) true (GrOperad.par (R := R) b Y)) := by
    intro a b
    rw [GrOperad.tw_hom true (M.par_mc i (GrOperad.par_par_self a X)
        (GrOperad.par_par_self b Y)),
      GrOperad.tw_hom true (GrOperad.par_par_self a X),
      GrOperad.tw_hom true (GrOperad.par_par_self b Y), map_smul, LinearMap.map_smul₂,
      smul_smul, ← neg_smul]
    congr 1
    cases a <;> cases b <;> simp
  conv_lhs => rw [← GrOperad.par_add (R := R) X, ← GrOperad.par_add (R := R) Y]
  conv_rhs => rw [← GrOperad.par_add (R := R) X, ← GrOperad.par_add (R := R) Y]
  simp only [map_add, LinearMap.add_apply, key, neg_add]

end MergeSp

section Helpers

variable {R : Type u} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

lemma map_add₃ (f : M →ₗ[R] N) (a b c : M) : f (a + b + c) = f a + f b + f c := by
  rw [map_add, map_add]

/-- A linear map out of a free module vanishes as soon as it vanishes on the basis elements. -/
lemma lin_eq_zero_of_single {α : Type*} (F : (α →₀ R) →ₗ[R] M)
    (h : ∀ a, F (Finsupp.single a 1) = 0) (x : α →₀ R) : F x = 0 := by
  have hF : F = 0 := Finsupp.lhom_ext' fun a => LinearMap.ext_ring (h a)
  rw [hF, LinearMap.zero_apply]

/-- Two bilinear maps after linear maps out of free modules agree as soon as they agree on the
basis elements. -/
lemma bilin_ext_single {α β : Type*} {P : Type*} [AddCommGroup P] [Module R P]
    (F G : M →ₗ[R] N →ₗ[R] P) (f : (α →₀ R) →ₗ[R] M) (g : (β →₀ R) →ₗ[R] N)
    (h : ∀ a b, F (f (Finsupp.single a 1)) (g (Finsupp.single b 1))
      = G (f (Finsupp.single a 1)) (g (Finsupp.single b 1)))
    (x : α →₀ R) (y : β →₀ R) : F (f x) (g y) = G (f x) (g y) := by
  have hF : F.compl₁₂ f g = G.compl₁₂ f g :=
    Finsupp.lhom_ext' fun a => LinearMap.ext_ring
      (Finsupp.lhom_ext' fun b => LinearMap.ext_ring (h a b))
  exact LinearMap.congr_fun₂ hF x y

end Helpers

section Generators

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {A B D X : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype D]
  [DecidableEq D] [Fintype X] [DecidableEq X]

local notation "𝒞" => FreeGrL R V
local notation "𝒥" => GrOperadIdeal.span R (grLinRel R V)
local notation "𝒥Ω" => GrOperadIdeal.span R (grLinRel R (CobarGen R 𝒞))
local notation "𝔟" => SgnLin.bas (treeSgn (grGenPar R V)) R
local notation "𝔅" => SgnLin.bas (treeSgn (grGenPar R (CobarGen R 𝒞))) R

namespace Cobar

variable (R V) in
/-- **The commutator of the cobar differential and the merge**:
`Ξ(x, y) = d (x ⊛ᵢ y) + d x ⊛ᵢ y + (-1)^{|x|} x ⊛ᵢ d y`. -/
noncomputable def xiM (i : A) :
    CobarGr R 𝒞 A →ₗ[R] CobarGr R 𝒞 B →ₗ[R] CobarGr R 𝒞 (Without A i ⊕ B) :=
  (mM R V i).compr₂ ((Cobar.d R 𝒞).app _) + (mM R V i).comp ((Cobar.d R 𝒞).app A)
    + ((mM R V i).comp (GrOperad.tw (R := R) true)).compl₂ ((Cobar.d R 𝒞).app B)

lemma xiM_apply (i : A) (X : CobarGr R 𝒞 A) (Y : CobarGr R 𝒞 B) :
    xiM R V i X Y = (Cobar.d R 𝒞).app _ (mM R V i X Y) + mM R V i ((Cobar.d R 𝒞).app A X) Y
      + mM R V i (GrOperad.tw (R := R) true X) ((Cobar.d R 𝒞).app B Y) := rfl

/-- The cobar differential anticommutes with the sign twist. -/
lemma d_tw (X : CobarGr R 𝒞 A) :
    (Cobar.d R 𝒞).app A (GrOperad.tw (R := R) true X)
      = -GrOperad.tw (R := R) true ((Cobar.d R 𝒞).app A X) := by
  exact (GrDer.app_tw (Cobar.d R 𝒞) true X).trans (neg_one_smul R _)

/-- **The Leibniz rule of the cobar differential.** -/
lemma d_comp (j : A) (W : CobarGr R 𝒞 A) (Q : CobarGr R 𝒞 B) :
    (Cobar.d R 𝒞).app _ (GrOperad.comp (R := R) j W Q)
      = GrOperad.comp (R := R) j ((Cobar.d R 𝒞).app A W) Q
        + GrOperad.comp (R := R) j (GrOperad.tw (R := R) true W) ((Cobar.d R 𝒞).app B Q) :=
  (Cobar.d R 𝒞).app_comp j W Q

lemma d_unit (e : Unit ≃ A) :
    (Cobar.d R 𝒞).app A (GrOperad.map (R := R) e (GrOperad.one (R := R) (P := CobarGr R 𝒞))) = 0 := by
  rw [GrDer.app_map, GrDer.app_one, map_zero]

lemma tw_unit (e : Unit ≃ A) :
    GrOperad.tw (R := R) true (GrOperad.map (R := R) e (GrOperad.one (R := R) (P := CobarGr R 𝒞)))
      = GrOperad.map (R := R) e (GrOperad.one (R := R) (P := CobarGr R 𝒞)) := by
  rw [← GrOperad.map_tw, GrOperad.tw_one]

/-- **The commutator commutes with relabelling the inner operation.** -/
lemma xiM_map_right {B' : Type} [Fintype B'] [DecidableEq B'] (e : B ≃ B') (i : A)
    (X : CobarGr R 𝒞 A) (Y : CobarGr R 𝒞 B) :
    xiM R V i X (GrOperad.map (R := R) e Y)
      = GrOperad.map (R := R) (compEquiv (Equiv.refl A) e i) (xiM R V i X Y) := by
  have h1 := (cobarMerge R V).mc_map_right e i X Y
  have h2 := (cobarMerge R V).mc_map_right e i ((Cobar.d R 𝒞).app A X) Y
  have h3 := (congrArg (mM R V i (GrOperad.tw (R := R) true X)) ((Cobar.d R 𝒞).app_map e Y)).trans
    ((cobarMerge R V).mc_map_right e i (GrOperad.tw (R := R) true X) ((Cobar.d R 𝒞).app B Y))
  have h4 := (congrArg ((Cobar.d R 𝒞).app _) h1).trans ((Cobar.d R 𝒞).app_map _ _)
  exact (congrArg₂ (· + ·) (congrArg₂ (· + ·) h4 h2) h3).trans (map_add₃ _ _ _ _).symm

/-- **The commutator commutes with relabelling the outer operation.** -/
lemma xiM_map_left {A' : Type} [Fintype A'] [DecidableEq A'] (e : A ≃ A') (i : A)
    (X : CobarGr R 𝒞 A) (Y : CobarGr R 𝒞 B) :
    xiM R V (e i) (GrOperad.map (R := R) e X) Y
      = GrOperad.map (R := R) (compEquiv e (Equiv.refl B) i) (xiM R V i X Y) := by
  have h1 := (cobarMerge R V).mc_map_left e i X Y
  have h2 := (congrArg (fun z => mM R V (e i) z Y) ((Cobar.d R 𝒞).app_map e X)).trans
    ((cobarMerge R V).mc_map_left e i ((Cobar.d R 𝒞).app A X) Y)
  have h3 := (congrArg (fun z => mM R V (e i) z ((Cobar.d R 𝒞).app B Y))
    (GrOperad.map_tw true e X).symm).trans
    ((cobarMerge R V).mc_map_left e i (GrOperad.tw (R := R) true X) ((Cobar.d R 𝒞).app B Y))
  have h4 := (congrArg ((Cobar.d R 𝒞).app _) h1).trans ((Cobar.d R 𝒞).app_map _ _)
  exact (congrArg₂ (· + ·) (congrArg₂ (· + ·) h4 h2) h3).trans (map_add₃ _ _ _ _).symm

lemma xiM_eq_of_left {i : A} {X : CobarGr R 𝒞 A} (hX : X = 0) (Y : CobarGr R 𝒞 B) :
    xiM R V i X Y = GrOperad.comp (R := R) i X Y := by
  subst hX
  exact (LinearMap.map_zero₂ (xiM R V i) Y).trans (LinearMap.map_zero₂ _ Y).symm

lemma xiM_eq_of_right {i : A} (X : CobarGr R 𝒞 A) {Y : CobarGr R 𝒞 B} (hY : Y = 0) :
    xiM R V i X Y = GrOperad.comp (R := R) i X Y := by
  subst hY
  exact (map_zero (xiM R V i X)).trans (map_zero _).symm

/-- The generator of a trivial tree vanishes. -/
lemma ιL_bas_leaf {x : Reg (TreeOfArity (GrGen R V)) A} (hx : (treeOf x).isLeaf = true) :
    Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 x)) = 0 := by
  obtain ⟨e, rfl⟩ := eq_map_one_of_isLeaf hx
  rw [← SgnLin.map_bas]
  exact Cobar.ιL_unitSpan R 𝒞 (GrCooperad.map_one_mem e)

/-- The generator of a tree with a vertex without inputs vanishes, when there are no generators
without inputs. -/
lemma ιL_bas_null (hV0 : ∀ v : V (Fin 0), v = 0) {x : Reg (TreeOfArity (GrGen R V)) A}
    (hx : ¬ (treeOf x).NoNull) : Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 x)) = 0 :=
  (congrArg (Cobar.ιL R 𝒞 A) (FreeGrL.proj_bas_eq_zero hV0 x hx)).trans (map_zero _)

/-- **The commutator on two generators** is their composite, when there are no generators
without inputs. -/
theorem xiM_ιL (hV0 : ∀ v : V (Fin 0), v = 0) (i : A) (y : FreeGr R (grGenPar R V) A)
    (y' : FreeGr R (grGenPar R V) B) :
    xiM R V i (Cobar.ιL R 𝒞 A ((𝒥).proj A y)) (Cobar.ιL R 𝒞 B ((𝒥).proj B y'))
      = GrOperad.comp (R := R) i (Cobar.ιL R 𝒞 A ((𝒥).proj A y))
          (Cobar.ιL R 𝒞 B ((𝒥).proj B y')) := by
  have key : ∀ (s : Reg (TreeOfArity (GrGen R V)) A) (t : Reg (TreeOfArity (GrGen R V)) B),
      xiM R V i (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 s))) (Cobar.ιL R 𝒞 B ((𝒥).proj B (𝔟 t)))
        = GrOperad.comp (R := R) i (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 s)))
            (Cobar.ιL R 𝒞 B ((𝒥).proj B (𝔟 t))) := by
    intro s t
    by_cases hs : (treeOf s).isLeaf = true
    · exact xiM_eq_of_left (ιL_bas_leaf hs) _
    by_cases ht : (treeOf t).isLeaf = true
    · exact xiM_eq_of_right _ (ιL_bas_leaf ht)
    by_cases hns : (treeOf s).NoNull
    swap
    · exact xiM_eq_of_left (ιL_bas_null hV0 hns) _
    by_cases hnt : (treeOf t).NoNull
    swap
    · exact xiM_eq_of_right _ (ιL_bas_null hV0 hnt)
    exact (xiM_apply i _ _).trans
      (d_mM_ιL_bas i s t (by simpa using hs) (by simpa using ht) hns hnt)
  exact bilin_ext_single (xiM R V i) (GrOperad.comp (R := R) (P := CobarGr R 𝒞) i)
    ((Cobar.ιL R 𝒞 A).comp ((𝒥).proj A)) ((Cobar.ιL R 𝒞 B).comp ((𝒥).proj B)) key y y'

/-! ### The commutator on units and composites -/

/-- The commutator vanishes on a relabelled unit on the right. -/
lemma xiM_unit_right (e : Unit ≃ B) (i : A) (X : CobarGr R 𝒞 A) :
    xiM R V i X (GrOperad.map (R := R) e (GrOperad.one (R := R) (P := CobarGr R 𝒞))) = 0 := by
  have h1 := (cobarMerge R V).mc_unit_right e i X
  have h2 := (cobarMerge R V).mc_unit_right e i ((Cobar.d R 𝒞).app A X)
  have h3 := (congrArg (mM R V i (GrOperad.tw (R := R) true X)) (d_unit e)).trans
    (map_zero (mM R V i (GrOperad.tw (R := R) true X)))
  refine (xiM_apply i X _).trans ((congrArg₂ (· + ·) (congrArg₂ (· + ·)
    ((congrArg ((Cobar.d R 𝒞).app _) h1).trans (map_zero _)) h2) h3).trans ?_)
  simp only [add_zero]

/-- The commutator vanishes on a relabelled unit on the left. -/
lemma xiM_unit_left (e : Unit ≃ A) (i : A) (Y : CobarGr R 𝒞 B) :
    xiM R V i (GrOperad.map (R := R) e (GrOperad.one (R := R) (P := CobarGr R 𝒞))) Y = 0 := by
  have h1 := (cobarMerge R V).mc_unit_left e i Y
  have h2 := (congrArg (fun z => mM R V i z Y) (d_unit e)).trans
    (LinearMap.map_zero₂ (mM R V i) Y)
  have h3 := (congrArg (fun z => mM R V i z ((Cobar.d R 𝒞).app B Y)) (tw_unit e)).trans
    ((cobarMerge R V).mc_unit_left e i ((Cobar.d R 𝒞).app B Y))
  refine (xiM_apply i _ Y).trans ((congrArg₂ (· + ·) (congrArg₂ (· + ·)
    ((congrArg ((Cobar.d R 𝒞).app _) h1).trans (map_zero _)) h2) h3).trans ?_)
  simp only [add_zero]

/-- The algebra of the commutator of a composite, merged at the outer factor. -/
lemma alg_outer {M N P P' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [AddCommGroup P'] [Module R P'] (S : P →ₗ[R] P')
    (c : M →ₗ[R] N →ₗ[R] P) (a b e t f : M) (q q' : N) (h : t = -f) :
    S (c a q + c t q') + S (c b q) + (S (c e q) + S (c f q')) = S (c (a + b + e) q) := by
  subst h
  simp only [map_add, LinearMap.add_apply, map_neg, LinearMap.neg_apply]
  abel

/-- **The commutator with a composite, merged into its outer factor**:
`Ξ(x, y ∘ᵣ z) = Ξ(x, y) ∘ᵣ z`, for `y` and `d y` without unit component. -/
lemma xiM_comp_outer (i : A) (r : B) (X : CobarGr R 𝒞 A) {P : CobarGr R 𝒞 B}
    (hP : FreeGrL.unitCoeffL R (CobarGen R 𝒞) B P = 0)
    (hdP : FreeGrL.unitCoeffL R (CobarGen R 𝒞) B ((Cobar.d R 𝒞).app B P) = 0)
    (Q : CobarGr R 𝒞 D) :
    xiM R V i X (GrOperad.comp (R := R) r P Q)
      = GrOperad.map (R := R) (seqEquiv i r D)
          (GrOperad.comp (R := R) (Sum.inr r) (xiM R V i X P) Q) := by
  have htP : FreeGrL.unitCoeffL R (CobarGen R 𝒞) B (GrOperad.tw (R := R) true P) = 0 := by
    rw [FreeGrL.unitCoeffL_tw, hP]
  have o1 := (cobarMerge R V).comp_mc_outer i r X hP Q
  have o2 := (cobarMerge R V).comp_mc_outer i r ((Cobar.d R 𝒞).app A X) hP Q
  have o3 := (cobarMerge R V).comp_mc_outer i r (GrOperad.tw (R := R) true X) hdP Q
  have o4 := (cobarMerge R V).comp_mc_outer i r (GrOperad.tw (R := R) true X) htP
    ((Cobar.d R 𝒞).app D Q)
  have dl : (Cobar.d R 𝒞).app _ (GrOperad.comp (R := R) r P Q)
      = GrOperad.comp (R := R) r ((Cobar.d R 𝒞).app B P) Q
        + GrOperad.comp (R := R) r (GrOperad.tw (R := R) true P) ((Cobar.d R 𝒞).app D Q) :=
    d_comp r P Q
  have dl2 : (Cobar.d R 𝒞).app _ (GrOperad.comp (R := R) (Sum.inr r) (mM R V i X P) Q)
      = GrOperad.comp (R := R) (Sum.inr r) ((Cobar.d R 𝒞).app _ (mM R V i X P)) Q
        + GrOperad.comp (R := R) (Sum.inr r) (GrOperad.tw (R := R) true (mM R V i X P))
            ((Cobar.d R 𝒞).app D Q) :=
    d_comp _ _ _
  have tm := (cobarMerge R V).tw_mc i X P
  have hA := (congrArg ((Cobar.d R 𝒞).app _) o1.symm).trans (((Cobar.d R 𝒞).app_map _ _).trans
    (congrArg (GrOperad.map (R := R) (seqEquiv i r D)) dl2))
  have hC := (congrArg (mM R V i (GrOperad.tw (R := R) true X)) dl).trans
    ((map_add _ _ _).trans (congrArg₂ (· + ·) o3.symm o4.symm))
  refine (xiM_apply i X _).trans ((congrArg₂ (· + ·) (congrArg₂ (· + ·) hA o2.symm) hC).trans ?_)
  refine (alg_outer _ _ _ _ _ _ _ _ _ tm).trans ?_
  exact congrArg (fun z => GrOperad.map (R := R) (seqEquiv i r D)
    (GrOperad.comp (R := R) (Sum.inr r) z Q)) (xiM_apply i X P).symm

/-- The algebra of the commutator of a composite, merged at the inner factor. -/
lemma alg_inner {M N P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (c : M →ₗ[R] N →ₗ[R] P) (a a' p p' : M) (m dm x y : N)
    (ha : a = -a') (hp : p' = p) :
    c a m + c p' dm + (c a' m + c p' x) + c p' y = c p (dm + x + y) := by
  subst ha hp
  simp only [map_add, map_neg, LinearMap.neg_apply]
  abel

/-- **The commutator with a composite, merging into its inner factor**:
`Ξ(x ∘ᵣ y, z) = x ∘ᵣ Ξ(y, z)`, for `y` and `d y` without unit component. -/
lemma xiM_comp_inner (r : A) (w : B) (P : CobarGr R 𝒞 A) {Q : CobarGr R 𝒞 B}
    (hQ : FreeGrL.unitCoeffL R (CobarGen R 𝒞) B Q = 0)
    (hdQ : FreeGrL.unitCoeffL R (CobarGen R 𝒞) B ((Cobar.d R 𝒞).app B Q) = 0)
    (Z : CobarGr R 𝒞 D) :
    GrOperad.map (R := R) (seqEquiv r w D) (xiM R V (Sum.inr w) (GrOperad.comp (R := R) r P Q) Z)
      = GrOperad.comp (R := R) r P (xiM R V w Q Z) := by
  have htQ : FreeGrL.unitCoeffL R (CobarGen R 𝒞) B (GrOperad.tw (R := R) true Q) = 0 := by
    rw [FreeGrL.unitCoeffL_tw, hQ]
  have i1 := (cobarMerge R V).mc_comp_inner r w P hQ Z
  have i2 := (cobarMerge R V).mc_comp_inner r w ((Cobar.d R 𝒞).app A P) hQ Z
  have i3 := (cobarMerge R V).mc_comp_inner r w (GrOperad.tw (R := R) true P) hdQ Z
  have i4 := (cobarMerge R V).mc_comp_inner r w (GrOperad.tw (R := R) true P) htQ
    ((Cobar.d R 𝒞).app D Z)
  have dl : (Cobar.d R 𝒞).app _ (GrOperad.comp (R := R) r P Q)
      = GrOperad.comp (R := R) r ((Cobar.d R 𝒞).app A P) Q
        + GrOperad.comp (R := R) r (GrOperad.tw (R := R) true P) ((Cobar.d R 𝒞).app B Q) :=
    d_comp r P Q
  have dl2 : (Cobar.d R 𝒞).app _ (GrOperad.comp (R := R) r (GrOperad.tw (R := R) true P)
      (mM R V w Q Z))
      = GrOperad.comp (R := R) r ((Cobar.d R 𝒞).app A (GrOperad.tw (R := R) true P))
          (mM R V w Q Z)
        + GrOperad.comp (R := R) r (GrOperad.tw (R := R) true (GrOperad.tw (R := R) true P))
            ((Cobar.d R 𝒞).app _ (mM R V w Q Z)) :=
    d_comp _ _ _
  have h1 := ((Cobar.d R 𝒞).app_map _ _).symm.trans
    ((congrArg ((Cobar.d R 𝒞).app _) i1).trans dl2)
  have h2 := (congrArg (fun z => GrOperad.map (R := R) (seqEquiv r w D)
    (mM R V (Sum.inr w) z Z)) dl).trans ((congrArg (GrOperad.map (R := R) (seqEquiv r w D))
      (LinearMap.map_add₂ _ _ _ _)).trans ((map_add _ _ _).trans (congrArg₂ (· + ·) i2 i3)))
  have h3 := (congrArg (fun z => GrOperad.map (R := R) (seqEquiv r w D)
    (mM R V (Sum.inr w) z ((Cobar.d R 𝒞).app D Z))) (GrOperad.tw_comp true r P Q)).trans i4
  refine (congrArg (GrOperad.map (R := R) (seqEquiv r w D)) (xiM_apply _ _ _)).trans
    ((map_add₃ _ _ _ _).trans ((congrArg₂ (· + ·) (congrArg₂ (· + ·) h1 h2) h3).trans ?_))
  refine (alg_inner _ _ _ _ _ _ _ _ _ (d_tw P) (GrOperad.tw_tw true P)).trans ?_
  exact congrArg (GrOperad.comp (R := R) r P) (xiM_apply w Q Z).symm

/-- The algebra of the commutator of a composite, merged beside its inner factor. -/
lemma alg_par {M N P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (c : M →ₗ[R] N →ₗ[R] P) (a b e W : M) (Q dQ : N)
    (s s₁ s₂ tz tq : R) (h₁ : s₁ = s * tz) (h₂ : s₂ * tq = s) :
    s • (c a Q + c (-(tz • W)) dQ) + (s • c b Q + s₁ • c W dQ) + s₂ • c e (tq • Q)
      = s • c (a + b + e) Q := by
  subst h₁ h₂
  simp only [map_add, map_neg, map_smul, LinearMap.add_apply, LinearMap.neg_apply,
    LinearMap.smul_apply, smul_add, smul_neg, smul_smul]
  abel

/-- **The commutator with a composite, merging beside its inner factor**:
`Ξ(x ∘ᵣ y, z) = (-1)^{|y||z|} Ξ(x, z) ∘ᵣ y`, for homogeneous `y`, `z`. -/
lemma xiM_comp_par {r u : A} (hru : r ≠ u) (P : CobarGr R 𝒞 A) {q z : Bool}
    {Q : CobarGr R 𝒞 B} {Z : CobarGr R 𝒞 D} (hQ : GrOperad.par (R := R) q Q = Q)
    (hZ : GrOperad.par (R := R) z Z = Z) :
    GrOperad.map (R := R) (parEquiv hru B D)
        (xiM R V (Sum.inl ⟨u, Ne.symm hru⟩) (GrOperad.comp (R := R) r P Q) Z)
      = σ R (q && z) • GrOperad.comp (R := R) (Sum.inl ⟨r, hru⟩) (xiM R V u P Z) Q := by
  have hdQ : GrOperad.par (R := R) (!q) ((Cobar.d R 𝒞).app B Q) = (Cobar.d R 𝒞).app B Q := by
    have h := ((congrArg ((Cobar.d R 𝒞).app B) hQ).symm.trans ((Cobar.d R 𝒞).app_par q Q)).symm
    rwa [Bool.xor_true] at h
  have hdZ : GrOperad.par (R := R) (!z) ((Cobar.d R 𝒞).app D Z) = (Cobar.d R 𝒞).app D Z := by
    have h := ((congrArg ((Cobar.d R 𝒞).app D) hZ).symm.trans ((Cobar.d R 𝒞).app_par z Z)).symm
    rwa [Bool.xor_true] at h
  have htQ : GrOperad.par (R := R) q (GrOperad.tw (R := R) true Q)
      = GrOperad.tw (R := R) true Q :=
    (GrOperad.par_tw true q Q).trans (congrArg (GrOperad.tw (R := R) true) hQ)
  have p1 := (cobarMerge R V).mc_comp_par hru P hQ hZ
  have p2 := (cobarMerge R V).mc_comp_par hru ((Cobar.d R 𝒞).app A P) hQ hZ
  have p3 := (cobarMerge R V).mc_comp_par hru (GrOperad.tw (R := R) true P) hdQ hZ
  have p4 := (cobarMerge R V).mc_comp_par hru (GrOperad.tw (R := R) true P) htQ hdZ
  have dl : (Cobar.d R 𝒞).app _ (GrOperad.comp (R := R) r P Q)
      = GrOperad.comp (R := R) r ((Cobar.d R 𝒞).app A P) Q
        + GrOperad.comp (R := R) r (GrOperad.tw (R := R) true P) ((Cobar.d R 𝒞).app B Q) :=
    d_comp r P Q
  have dl2 : (Cobar.d R 𝒞).app _ (GrOperad.comp (R := R) (Sum.inl ⟨r, hru⟩ : Without A u ⊕ D) (mM R V u P Z) Q)
      = GrOperad.comp (R := R) (Sum.inl ⟨r, hru⟩ : Without A u ⊕ D) ((Cobar.d R 𝒞).app _ (mM R V u P Z)) Q
        + GrOperad.comp (R := R) (Sum.inl ⟨r, hru⟩ : Without A u ⊕ D) (GrOperad.tw (R := R) true (mM R V u P Z))
            ((Cobar.d R 𝒞).app B Q) :=
    d_comp _ _ _
  have tm : GrOperad.tw (R := R) true (mM R V u P Z)
      = -(σ R (true && z) • mM R V u (GrOperad.tw (R := R) true P) Z) :=
    ((cobarMerge R V).tw_mc u P Z).trans (congrArg Neg.neg
      ((congrArg (mM R V u (GrOperad.tw (R := R) true P)) (GrOperad.tw_hom true hZ)).trans
        (map_smul _ _ _)))
  have h1 := ((Cobar.d R 𝒞).app_map _ _).symm.trans
    ((congrArg ((Cobar.d R 𝒞).app _) p1).trans ((map_smul ((Cobar.d R 𝒞).app _)
      (σ R (q && z)) _).trans
      (congrArg (fun x => σ R (q && z) • x) (dl2.trans (congrArg (fun x =>
        GrOperad.comp (R := R) (Sum.inl ⟨r, hru⟩ : Without A u ⊕ D) ((Cobar.d R 𝒞).app _ (mM R V u P Z)) Q
          + GrOperad.comp (R := R) (Sum.inl ⟨r, hru⟩ : Without A u ⊕ D) x ((Cobar.d R 𝒞).app B Q)) tm)))))
  have h2 := (congrArg (fun x => GrOperad.map (R := R) (parEquiv hru B D)
    (mM R V (Sum.inl ⟨u, Ne.symm hru⟩ : Without A r ⊕ B) x Z)) dl).trans ((congrArg (GrOperad.map (R := R)
      (parEquiv hru B D)) (LinearMap.map_add₂ _ _ _ _)).trans
        ((map_add (GrOperad.map (R := R) (parEquiv hru B D)) _ _).trans
        (congrArg₂ (· + ·) p2 p3)))
  have h3 := (congrArg (fun x => GrOperad.map (R := R) (parEquiv hru B D)
    (mM R V (Sum.inl ⟨u, Ne.symm hru⟩ : Without A r ⊕ B) x ((Cobar.d R 𝒞).app D Z)))
      (GrOperad.tw_comp true r P Q)).trans (p4.trans (congrArg (fun x => σ R (q && !z) •
        GrOperad.comp (R := R) (Sum.inl ⟨r, hru⟩ : Without A u ⊕ D)
          (mM R V u (GrOperad.tw (R := R) true P) ((Cobar.d R 𝒞).app D Z)) x)
        (GrOperad.tw_hom true hQ)))
  refine (congrArg (GrOperad.map (R := R) (parEquiv hru B D)) (xiM_apply _ _ _)).trans
    ((map_add₃ _ _ _ _).trans ((congrArg₂ (· + ·) (congrArg₂ (· + ·) h1 h2) h3).trans ?_))
  refine (alg_par _ _ _ _ _ _ _ _ _ _ _ _ (by cases q <;> cases z <;> simp)
    (by cases q <;> cases z <;> simp)).trans ?_
  exact congrArg (fun x => σ R (q && z) • GrOperad.comp (R := R) (Sum.inl ⟨r, hru⟩ : Without A u ⊕ D) x Q)
    (xiM_apply u P Z).symm

/-! ### Unit components -/

/-- **Every generator of the cobar construction is the generator of an element of the cut
cooperad**, represented by a combination of trees. -/
lemma exists_ιL_eq (v : CobarGen R 𝒞 A) :
    ∃ y : FreeGr R (grGenPar R V) A,
      Cobar.ιL R 𝒞 A ((𝒥).proj A y) = (FreeGrL.ι R (CobarGen R 𝒞)).app A v := by
  obtain ⟨c, hc⟩ := GrCooperad.Red.proj_surjective (R := R) (C := 𝒞) A
    ((GrSpecies.Shift.of (R := R) (V := GrCooperad.Red R 𝒞) A).symm v)
  obtain ⟨y, rfl⟩ := (𝒥).proj_surjective A c
  refine ⟨y, (Cobar.ιL_apply R 𝒞 _).trans (congrArg ((FreeGrL.ι R (CobarGen R 𝒞)).app A) ?_)⟩
  rw [hc]
  exact LinearEquiv.apply_symm_apply _ v

/-- The terms of the convolution square at the vertices have no unit component. -/
lemma unitCoeffL_starI (t : Reg (TreeOfArity (GrGen R V)) X) {v : ℕ}
    (hv : v ∈ Finset.Ico 1 (treeOf t).weight) :
    FreeGrL.unitCoeffL R (CobarGen R 𝒞) X (starI R V t v) = 0 := by
  rw [Finset.mem_Ico] at hv
  obtain ⟨e, he⟩ := exists_rep t hv.2
  have hst := starI_eq (R := R) (V := V) he (Tree.isLeaf_cutV _ _ hv.2)
  have hvert : vert ⟨((treeOf t).cutV v).2.2, Tree.lt_arity_cutV _ v hv.2⟩
      (stdT ((treeOf t).cutV v).1) = v := by
    show (treeOf (stdT _)).vb ((stdT _).1.rank _) = v
    rw [treeOf_stdT, rank_stdT]
    exact Tree.vb_cutV _ _ hv.2
  rw [hvert] at hst
  rw [hst]
  unfold repI
  rw [FreeGrL.unitCoeffL_map, map_smul, FreeGrL.unitCoeffL_comp, unitCoeffL_ιL, zero_mul,
    smul_zero]

/-- **The cobar differential of a generator has no unit component**, when there are no
generators without inputs. -/
lemma unitCoeffL_d_ιL (hV0 : ∀ v : V (Fin 0), v = 0) (y : FreeGr R (grGenPar R V) A) :
    FreeGrL.unitCoeffL R (CobarGen R 𝒞) A
      ((Cobar.d R 𝒞).app A (Cobar.ιL R 𝒞 A ((𝒥).proj A y))) = 0 := by
  refine lin_eq_zero_of_single ((FreeGrL.unitCoeffL R (CobarGen R 𝒞) A).comp
    (((Cobar.d R 𝒞).app A).comp ((Cobar.ιL R 𝒞 A).comp ((𝒥).proj A)))) (fun t => ?_) y
  show FreeGrL.unitCoeffL R (CobarGen R 𝒞) A
    ((Cobar.d R 𝒞).app A (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t)))) = 0
  by_cases ht : (treeOf t).isLeaf = true
  · rw [ιL_bas_leaf ht, map_zero, map_zero]
  by_cases hn : (treeOf t).NoNull
  · rw [d_ιL_bas t hn, map_neg, map_sum, Finset.sum_eq_zero fun v hv => unitCoeffL_starI t hv,
      neg_zero]
  · rw [ιL_bas_null hV0 hn, map_zero, map_zero]

lemma uc_d_map {A' : Type} [Fintype A'] [DecidableEq A'] (e : A ≃ A') (W : CobarGr R 𝒞 A) :
    FreeGrL.unitCoeffL R (CobarGen R 𝒞) A' ((Cobar.d R 𝒞).app A' (GrOperad.map (R := R) e W))
      = FreeGrL.unitCoeffL R (CobarGen R 𝒞) A ((Cobar.d R 𝒞).app A W) := by
  rw [GrDer.app_map, FreeGrL.unitCoeffL_map]

lemma uc_d_smul (c : R) (W : CobarGr R 𝒞 A) :
    FreeGrL.unitCoeffL R (CobarGen R 𝒞) A ((Cobar.d R 𝒞).app A (c • W))
      = c • FreeGrL.unitCoeffL R (CobarGen R 𝒞) A ((Cobar.d R 𝒞).app A W) := by
  rw [map_smul, map_smul]

lemma uc_d_comp (r : A) {P : CobarGr R 𝒞 A} {Q : CobarGr R 𝒞 B}
    (hp : FreeGrL.unitCoeffL R (CobarGen R 𝒞) A ((Cobar.d R 𝒞).app A P) = 0)
    (hq : FreeGrL.unitCoeffL R (CobarGen R 𝒞) B ((Cobar.d R 𝒞).app B Q) = 0) :
    FreeGrL.unitCoeffL R (CobarGen R 𝒞) _ ((Cobar.d R 𝒞).app _ (GrOperad.comp (R := R) r P Q))
      = 0 := by
  refine (congrArg (FreeGrL.unitCoeffL R (CobarGen R 𝒞) _) (d_comp r P Q)).trans
    ((map_add _ _ _).trans ((congrArg₂ (· + ·) (FreeGrL.unitCoeffL_comp r _ _)
      (FreeGrL.unitCoeffL_comp r _ _)).trans ?_))
  exact (congrArg₂ (fun a b => a * FreeGrL.unitCoeffL R (CobarGen R 𝒞) B Q
    + FreeGrL.unitCoeffL R (CobarGen R 𝒞) A (GrOperad.tw (R := R) true P) * b) hp hq).trans
      (by simp only [zero_mul, mul_zero, add_zero])

/-- **The cobar differential of a tree has no unit component**, when there are no generators
without inputs. -/
lemma unitCoeffL_d_bas (hV0 : ∀ v : V (Fin 0), v = 0)
    (x : Reg (TreeOfArity (GrGen R (CobarGen R 𝒞))) A) :
    FreeGrL.unitCoeffL R (CobarGen R 𝒞) A ((Cobar.d R 𝒞).app A ((𝒥Ω).proj A (𝔅 x))) = 0 := by
  refine tree_induction (motive := fun A _ _ x => FreeGrL.unitCoeffL R (CobarGen R 𝒞) A
    ((Cobar.d R 𝒞).app A ((𝒥Ω).proj A (𝔅 x))) = 0) ?_ ?_ ?_ A x
  · intro X _ _ x hl
    obtain ⟨e, he⟩ := FreeGrL.proj_bas_leaf hl
    exact (congrArg (fun z => FreeGrL.unitCoeffL R (CobarGen R 𝒞) X ((Cobar.d R 𝒞).app X z))
      he).trans ((congrArg (FreeGrL.unitCoeffL R (CobarGen R 𝒞) X) (d_unit e)).trans
        (map_zero _))
  · intro X _ _ k g e
    obtain ⟨y, hy⟩ := exists_ιL_eq (R := R) (V := V) g.1.1
    have hZ : (𝒥Ω).proj X (𝔅 (SetOperad.map e (Reg.std (corolla g))))
        = GrOperad.map (R := R) e (Cobar.ιL R 𝒞 (Fin k) ((𝒥).proj (Fin k) y)) :=
      (FreeGrL.proj_bas_map e _).trans (congrArg (GrOperad.map (R := R) e)
        ((FreeGrL.proj_bas_corolla g).trans hy.symm))
    exact (congrArg (fun z => FreeGrL.unitCoeffL R (CobarGen R 𝒞) X ((Cobar.d R 𝒞).app X z))
      hZ).trans ((uc_d_map e _).trans (unitCoeffL_d_ιL hV0 y))
  · intro X A B _ _ _ _ _ _ r p q e _ _ hp hq
    have hX : (𝒥Ω).proj X (𝔅 (SetOperad.map e (SetOperad.comp r p q)))
        = GrOperad.map (R := R) e (σ R (cSgn (grGenPar R (CobarGen R 𝒞)) r p q) •
            GrOperad.comp (R := R) r ((𝒥Ω).proj A (𝔅 p)) ((𝒥Ω).proj B (𝔅 q))) :=
      (FreeGrL.proj_bas_map e _).trans (congrArg (GrOperad.map (R := R) e)
        (FreeGrL.proj_bas_comp r p q))
    exact (congrArg (fun z => FreeGrL.unitCoeffL R (CobarGen R 𝒞) X ((Cobar.d R 𝒞).app X z))
      hX).trans ((uc_d_map e _).trans ((uc_d_smul _ _).trans
        ((congrArg _ (uc_d_comp r hp hq)).trans (smul_zero _))))

/-- **The cobar differential has no unit component**, when there are no generators without
inputs. -/
theorem unitCoeffL_d (hV0 : ∀ v : V (Fin 0), v = 0) (Y : CobarGr R 𝒞 A) :
    FreeGrL.unitCoeffL R (CobarGen R 𝒞) A ((Cobar.d R 𝒞).app A Y) = 0 := by
  obtain ⟨y, rfl⟩ := (𝒥Ω).proj_surjective A Y
  exact lin_eq_zero_of_single ((FreeGrL.unitCoeffL R (CobarGen R 𝒞) A).comp
    (((Cobar.d R 𝒞).app A).comp ((𝒥Ω).proj A))) (fun x => unitCoeffL_d_bas hV0 x) y

end Cobar

end Generators

end Operad
