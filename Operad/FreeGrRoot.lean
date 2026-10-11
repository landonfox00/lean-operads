/-
# The root decomposition of a free graded operad

Let `T(W)` be the free graded operad on a graded linear species `W` (`FreeGrL R W`), augmented by
the coefficient of the unit tree (`FreeGrL.aug`). **The root decomposition**
`ρ : T(W) → W ∘ T(W)` (`FreeGrL.root`) writes a tree as its root vertex with the subtrees above
it. It is the second component of the morphism of graded operads
`T(W) → T(W) ⋉ (W ∘ T(W))` (`FreeGrL.rootHom`) sending a generator `w` to `(w, w ⊗ (1, …, 1))`
(`GrComposite.corolla`), so that

  `ρ (x ∘ᵢ y) = ρ(x) ◁ᵢ y + ε(x) ρ(y)`, `ρ(1) = 0`, `ρ(w) = w ⊗ (1, …, 1)`

(`FreeGrL.root_comp`, `FreeGrL.root_one`, `FreeGrL.root_ι`).
-/
import Operad.GrRoot
import Operad.CobarHomotopy

universe u v w

namespace Operad

open Function Sym GerBV

variable {R : Type u} [CommRing R]
  {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)] [GrSpecies R W]

/-! ## Corollas -/

namespace GrComposite

variable {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrOperad R C]
  {S : Type} [Fintype S] [DecidableEq S] {A : Type} [Fintype A] [DecidableEq A]

/-- **The generator `w ⊗ (1, …, 1)`**: the units composed at every input of `w`. -/
abbrev corGen (L : LinOrd A) (w : W A) (e : A ≃ S) : GrCompGen W C S :=
  ⟨A, fun _ => Unit, L, w, fun _ => GrOperad.one (R := R), (Equiv.sigmaPUnit A).trans e⟩

omit [DecidableEq A] in
lemma rsg_false (L L' : LinOrd A) : GrEnd.rsg R L L' (fun _ => false) = 1 := by
  unfold GrEnd.rsg
  simp

omit [Fintype S] [DecidableEq S] in
/-- The order of the units is immaterial. -/
lemma mk_corGen_reorder (L L' : LinOrd A) (w : W A) (e : A ≃ S) [Fintype S] [DecidableEq S] :
    mk R (corGen (C := C) (R := R) L w e) = mk R (corGen (C := C) (R := R) L' w e) := by
  rw [mk_reorder (corGen (C := C) (R := R) L w e) L' (fun _ => false)
    (fun _ => GrOperad.par_one), rsg_false, one_smul]

/-- **Relabelling the inputs of the outer operation of a corolla.** -/
lemma mk_corGen_outer {B : Type} [Fintype B] [DecidableEq B] (σ : A ≃ B) (L : LinOrd B)
    (L' : LinOrd A) (w : W A) (e : B ≃ S) :
    mk R (corGen (C := C) (R := R) L (SymSpecies.map (R := R) σ w) e)
      = mk R (corGen (C := C) (R := R) L' w (σ.trans e)) := by
  rw [mk_outer (corGen (C := C) (R := R) L (SymSpecies.map (R := R) σ w) e) σ w]
  refine Eq.trans ?_ (mk_corGen_reorder (C := C) (R := R) (LinOrd.map σ.symm L) L' w _)
  congr 2

/-- A linear order on a finite type. -/
noncomputable def ordOf (A : Type) [Fintype A] : LinOrd A :=
  LinOrd.map (Fintype.equivFin A).symm (LinOrd.std _)

variable (R C) in
/-- **The corolla** `w ⊗ (1, …, 1)` of `W ∘ C`. -/
noncomputable def corolla (A : Type) [Fintype A] [DecidableEq A] : W A →ₗ[R] GrComposite R W C A :=
  mkM (corGen (C := C) (R := R) (ordOf A) 0 (Equiv.refl A))

lemma corolla_apply (w : W A) :
    corolla R C A w = mk R (corGen (C := C) (R := R) (ordOf A) w (Equiv.refl A)) := rfl

lemma map_corolla {B : Type} [Fintype B] [DecidableEq B] (σ : A ≃ B) (w : W A) :
    map σ (corolla R C A w) = corolla R C B (SymSpecies.map (R := R) σ w) := by
  rw [corolla_apply, corolla_apply, map_mk, mk_corGen_outer σ _ (ordOf A)]
  rfl

lemma par_corolla (b : Bool) (w : W A) :
    par R W C b (corolla R C A w) = corolla R C A (GrSpecies.par (R := R) b w) := by
  rw [corolla_apply, par_mk, parFun_of_hy b _ (c := fun _ => false) (fun _ => GrOperad.par_one),
    Fintype.sum_bool]
  have ht : GrEnd.tot (fun _ : A => false) = false := by
    unfold GrEnd.tot
    simp
  cases b <;> simp [ht] <;> rfl

variable (R W C) in
/-- **The corollas**, a morphism of graded linear species `W → W ∘ C`. -/
noncomputable def corollaHom : GrSpeciesHom R W (GrComposite R W C) where
  app A _ _ := corolla R C A
  app_map σ w := (map_corolla σ w).symm
  app_par b w := (par_corolla b w).symm

end GrComposite

/-! ## The augmentation of a free graded operad -/

namespace FreeGrL

local notation "𝒥" => GrOperadIdeal.span R (grLinRel R W)

open TreeOfArity FreeGr in
/-- The unit coefficient vanishes outside the arities of one element. -/
lemma unitCoeffL_eq_zero {A : Type} [Fintype A] [DecidableEq A] (h : IsEmpty (Unit ≃ A))
    (x : FreeGrL R W A) : unitCoeffL R W A x = 0 := by
  obtain ⟨x, rfl⟩ := (𝒥).proj_surjective A x
  have h0 := Lin.induction₁ (S := Reg (TreeOfArity (GrGen R W)))
    (FreeGr.unitCoeff (grGenPar R W) R A) 0 (fun t => ?_) x
  · simpa using h0
  show FreeGr.unitCoeff (grGenPar R W) R A (SgnLin.bas (treeSgn (grGenPar R W)) R t) = 0
  rw [FreeGr.unitCoeff_bas, if_neg]
  intro hl
  have h1 := treeOf_arity t
  rw [Tree.eq_leaf_of_isLeaf hl, Tree.arity_leaf] at h1
  exact h.false (Fintype.equivOfCardEq (by rw [Fintype.card_unit, ← t.2.2, ← h1]))

variable (R W) in
/-- **The augmentation of a free graded operad**: the coefficient of the unit tree. -/
noncomputable def aug : GrAug R (FreeGrL R W) where
  u := unitCoeffL R W
  u_map σ x := unitCoeffL_map σ x
  u_par x := by rw [unitCoeffL_par, if_pos rfl]
  u_one := unitCoeffL_one
  u_comp i x y := unitCoeffL_comp i x y
  u_eq_zero h x := unitCoeffL_eq_zero h x

@[simp] lemma aug_u {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R W A) :
    (aug R W).u A x = unitCoeffL R W A x := rfl

/-! ## The root decomposition -/

open GrComposite

/-- The square-zero extension of the free graded operad by `W ∘ T(W)`. -/
local notation "𝒬" => SqExt R W (FreeGrL R W) (aug R W)

variable (R W) in
/-- The values on the generators: `w ↦ (w, w ⊗ (1, …, 1))`. -/
noncomputable def rootGen : GrSpeciesHom R W 𝒬 where
  app A _ _ := ((ι R W).app A).prod (corolla R (FreeGrL R W) A)
  app_map σ w := Prod.ext ((ι R W).app_map σ w) (map_corolla σ w).symm
  app_par b w := Prod.ext ((ι R W).app_par b w) (par_corolla b w).symm

variable (R W) in
/-- **The morphism `T(W) → T(W) ⋉ (W ∘ T(W))`** extending `w ↦ (w, w ⊗ (1, …, 1))`. -/
noncomputable def rootHom : GrOperadHom R (FreeGrL R W) 𝒬 := homEquiv.symm (rootGen R W)

lemma fst_rootHom {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R W A) :
    SqExt.fst ((rootHom R W).app A x) = x := by
  have h : (SqExt.fstHom R W (FreeGrL R W) (aug R W)).comp (rootHom R W) = GrOperadHom.id R _ :=
    hom_ext fun A _ _ w => by
      rw [GrOperadHom.comp_app, rootHom, homEquiv_symm_ι]
      rfl
  exact congrArg (fun φ : GrOperadHom R (FreeGrL R W) (FreeGrL R W) => φ.app A x) h

variable (R W) in
/-- **The root decomposition** `ρ : T(W) → W ∘ T(W)`: a tree is its root vertex with the subtrees
above it. -/
noncomputable def root (A : Type) [Fintype A] [DecidableEq A] :
    FreeGrL R W A →ₗ[R] GrComposite R W (FreeGrL R W) A :=
  SqExt.snd ∘ₗ (rootHom R W).app A

lemma rootHom_app {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R W A) :
    (rootHom R W).app A x = SqExt.mk x (root R W A x) :=
  SqExt.ext (fst_rootHom x) rfl

/-- **The root decomposition of a generator** is its corolla. -/
@[simp] lemma root_ι {A : Type} [Fintype A] [DecidableEq A] (w : W A) :
    root R W A ((ι R W).app A w) = corolla R (FreeGrL R W) A w := by
  show SqExt.snd ((rootHom R W).app A _) = _
  rw [rootHom, homEquiv_symm_ι]
  rfl

/-- The unit has no root vertex. -/
@[simp] lemma root_one : root R W Unit (GrOperad.one (R := R)) = 0 := by
  show SqExt.snd ((rootHom R W).app Unit _) = _
  rw [(rootHom R W).app_one]
  rfl

/-- **The root decomposition of a composite**: `ρ (x ∘ᵢ y) = ρ(x) ◁ᵢ y + ε(x) ρ(y)`. -/
lemma root_comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (x : FreeGrL R W A) (y : FreeGrL R W B) :
    root R W _ (GrOperad.comp (R := R) i x y)
      = act R W i y (root R W A x) + lact R W (aug R W) i x (root R W B y) := by
  show SqExt.snd ((rootHom R W).app _ _) = _
  rw [(rootHom R W).app_comp, rootHom_app, rootHom_app]
  rfl

lemma root_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (σ : A ≃ B)
    (x : FreeGrL R W A) :
    root R W B (GrOperad.map (R := R) σ x) = GrComposite.map σ (root R W A x) := by
  show SqExt.snd ((rootHom R W).app _ _) = _
  rw [(rootHom R W).app_map, rootHom_app]
  rfl

lemma root_par {A : Type} [Fintype A] [DecidableEq A] (b : Bool) (x : FreeGrL R W A) :
    root R W A (GrOperad.par (R := R) b x)
      = GrComposite.par R W (FreeGrL R W) b (root R W A x) := by
  show SqExt.snd ((rootHom R W).app _ _) = _
  rw [(rootHom R W).app_par, rootHom_app]
  rfl

end FreeGrL

end Operad
