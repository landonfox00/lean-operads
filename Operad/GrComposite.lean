/-
# The composition product of graded linear species

For graded linear species `M` and `N`, the **graded composite** `M ∘ N` has, at a finite type `S`,
the classes `⟨L; m; y; e⟩` of an operation `m ∈ M A`, an operation `y a ∈ N (B a)` at every input
`a` of `m`, a linear order `L` of the inputs of `m`, and a naming `e : (Σ a, B a) ≃ S` of the
inputs (`Operad.GrComposite`). It stands for the tensor `m ⊗ y a₁ ⊗ ⋯ ⊗ y aₖ`, the inputs of `m`
read in the order `L`: up to linearity in `m`, multilinearity in `y`, relabelling of the inputs of
`m` (transporting the order) and of each `y a`, and **reordering with the Koszul sign**
`⟨L; m; y⟩ = ± ⟨L'; m; y⟩` for homogeneous `y`, a sign for each pair of odd inner operations that
the two orders read in opposite positions (`GrEnd.rsg`).

* `GrComposite.lift`, `GrComposite.hom_ext`, `GrComposite.induction_on`: **linear maps out of a
  composite** are the functions on generators respecting the relations, and agree when they agree
  on generators.
* Relabelling the inputs makes `M ∘ N` a linear species (`GrComposite.instSymSpecies`), and the
  parities `|m| + ∑ₐ |y a|` make it **a graded linear species** (`GrComposite.instGrSpecies`).
* **Functoriality** in morphisms of species, the second one preserving parities
  (`GrComposite.map₂`).
* **An endomorphism `g` of parity `q` of `N` acting at the inner operations**, as a derivation with
  the Koszul signs (`GrComposite.leafMap`): `g` at one inner operation, after the sign twist of the
  outer operation and of the inner operations read before it. Changing the order of the inner
  operations changes these signs as it changes the reordering signs (`GrComposite.rsg_update_mul`).
  It commutes with relabelling and shifts parities by `q` (`GrComposite.leafMap_map`,
  `GrComposite.par_leafMap`).
-/
import Operad.GradedEnd
import Operad.FreeGrDer

universe u v w x

namespace Operad

open Function Sym GerBV

/-! ## Generators and relations -/

/-- **A generator of the graded composite** `M ∘ N` at `S`: an operation `m` with inputs `A`, an
order `L` of `A`, an operation `y a` with inputs `B a` at every input `a` of `m`, and the naming
`e` of the inputs. -/
structure GrCompGen (M : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    (N : (A : Type) → [Fintype A] → [DecidableEq A] → Type w) (S : Type) where
  /-- The inputs of the outer operation. -/
  A : Type
  [instFintypeA : Fintype A]
  [instDecEqA : DecidableEq A]
  /-- The inputs of the inner operations. -/
  B : A → Type
  [instFintypeB : ∀ a, Fintype (B a)]
  [instDecEqB : ∀ a, DecidableEq (B a)]
  /-- The order in which the inner operations are read. -/
  L : LinOrd A
  /-- The outer operation. -/
  m : M A
  /-- The inner operations. -/
  y : ∀ a, N (B a)
  /-- The naming of the inputs. -/
  e : (Σ a, B a) ≃ S

attribute [instance] GrCompGen.instFintypeA GrCompGen.instDecEqA GrCompGen.instFintypeB
  GrCompGen.instDecEqB

/-- **Relabelling the inputs** of a generator. -/
def GrCompGen.relabel {M : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
    {N : (A : Type) → [Fintype A] → [DecidableEq A] → Type w} {S S' : Type}
    (g : GrCompGen M N S) (f : S ≃ S') : GrCompGen M N S' :=
  { g with e := g.e.trans f }

/-! ## Reordering signs with one parity changed -/

namespace GrComposite

/-- The order relation, as a Boolean decided classically. -/
noncomputable def ltB {A : Type} (L : LinOrd A) (a b : A) : Bool :=
  @decide (L.lt a b) (Classical.propDecidable _)

lemma ltB_eq_true {A : Type} (L : LinOrd A) (a b : A) : ltB L a b = true ↔ L.lt a b :=
  @decide_eq_true_iff _ (Classical.propDecidable _)

@[simp] lemma ltB_self {A : Type} (L : LinOrd A) (a : A) : ltB L a a = false := by
  rw [Bool.eq_false_iff, ne_eq, ltB_eq_true]
  exact L.irrefl a

section Rsg

variable {R : Type u} [CommRing R] {A : Type} [Fintype A] [DecidableEq A]

open Classical in
/-- **Changing the parity of one input** changes the reordering sign by the signs of the pairs it
forms with the inputs it passes. -/
lemma rsg_update (L L' : LinOrd A) (c : A → Bool) (j : A) (q : Bool) :
    GrEnd.rsg R L L' (update c j (xor (c j) q))
      = GrEnd.rsg R L L' c * ((∏ b, if L.lt j b ∧ L'.lt b j then σ R (q && c b) else 1)
          * ∏ a, if L.lt a j ∧ L'.lt j a then σ R (q && c a) else 1) := by
  unfold GrEnd.rsg
  have hF : ∀ a b, (if L.lt a b ∧ L'.lt b a then σ R (update c j (xor (c j) q) a
      && update c j (xor (c j) q) b) else 1)
      = (if L.lt a b ∧ L'.lt b a then σ R (c a && c b) else 1)
        * ((if (L.lt a b ∧ L'.lt b a) ∧ a = j then σ R (q && c b) else 1)
          * (if (L.lt a b ∧ L'.lt b a) ∧ b = j then σ R (q && c a) else 1)) := by
    intro a b
    by_cases hab : L.lt a b ∧ L'.lt b a
    · have hne : a ≠ b := fun h => L.irrefl a (h ▸ hab.1)
      simp only [hab, true_and, if_true]
      by_cases ha : a = j
      · subst ha
        have hb : b ≠ a := Ne.symm hne
        simp only [update_self, update_of_ne hb, if_true, if_neg hb, mul_one]
        rw [GrEnd.σ_xor_and]
      · by_cases hb : b = j
        · subst hb
          simp only [update_self, update_of_ne ha, if_neg ha, if_true, one_mul]
          rw [GrEnd.σ_and_xor, Bool.and_comm (c a) q]
        · simp only [update_of_ne ha, update_of_ne hb, if_neg ha, if_neg hb, mul_one]
    · simp only [hab, false_and, if_false, mul_one]
  simp only [hF, Finset.prod_mul_distrib]
  congr 1
  congr 1
  · rw [Finset.prod_eq_single j]
    · simp only [and_true]
    · intro a _ ha
      refine Finset.prod_eq_one fun b _ => ?_
      simp only [ha, and_false, if_false]
    · intro h
      exact absurd (Finset.mem_univ j) h
  · refine Finset.prod_congr rfl fun a _ => ?_
    rw [Finset.prod_eq_single j]
    · simp only [and_true]
    · intro b _ hb
      simp only [hb, and_false, if_false]
    · intro h
      exact absurd (Finset.mem_univ j) h

open Classical in
/-- **The Koszul signs of an odd map at the input `j`** in two orders, and the reordering signs
before and after it acts. -/
lemma rsg_update_mul (L L' : LinOrd A) (c : A → Bool) (j : A) (q : Bool) :
    (∏ a, if ltB L a j then σ R (q && c a) else 1) * GrEnd.rsg R L L' (update c j (xor (c j) q))
      = GrEnd.rsg R L L' c * ∏ a, if ltB L' a j then σ R (q && c a) else 1 := by
  simp only [ltB_eq_true]
  rw [rsg_update, ← Finset.prod_mul_distrib, mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun a _ => ?_
  have hs : σ R (q && c a) * σ R (q && c a) = 1 := σ_mul_self R _
  by_cases haj : a = j
  · subst haj
    simp only [L.irrefl, L'.irrefl, and_false, if_false, mul_one]
  rcases L.total a j haj with h1 | h1 <;> rcases L'.total a j haj with h2 | h2 <;>
    simp only [h1, h2, GrEnd.lt_asymm _ h1, GrEnd.lt_asymm _ h2, and_true, and_false, if_true,
      if_false, mul_one, one_mul, hs]

omit [Fintype A] in
lemma tot_update [Fintype A] (c : A → Bool) (j : A) (v : Bool) :
    GrEnd.tot (update c j v) = xor (xor (GrEnd.tot c) (c j)) v := by
  unfold GrEnd.tot
  have h1 : ∑ x, (update c j v x).toNat = v.toNat + ∑ x ∈ Finset.univ.erase j, (c x).toNat := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), update_self]
    congr 1
    exact Finset.sum_congr rfl fun x hx => by rw [update_of_ne (Finset.ne_of_mem_erase hx)]
  have h2 : ∑ x, (c x).toNat = (c j).toNat + ∑ x ∈ Finset.univ.erase j, (c x).toNat :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
  rw [h1, h2, Nat.bodd_add, Nat.bodd_add, GrEnd.bodd_toNat, GrEnd.bodd_toNat]
  cases v <;> cases c j <;> simp

end Rsg

end GrComposite


/-! ## Odd maps at an input, with their Koszul signs -/

namespace GrComposite

section LeafLin

variable {R : Type u} [CommRing R]
  {N : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N A)] [GrSpecies R N] {q : Bool}

/-- The map applied at the input `a` when an endomorphism `gm` of parity `q` acts at the input
`j`: `gm` at `j`, the sign twist at the inputs read before `j`, the identity elsewhere. -/
noncomputable def leafLin (gm : GrSpEnd R N q) {A : Type} [DecidableEq A] (L : LinOrd A) (j : A)
    {B : A → Type} [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (a : A) :
    N (B a) →ₗ[R] N (B a) :=
  if a = j then gm.app (B a) else if ltB L a j then GrSpecies.tw (R := R) (V := N) q
    else LinearMap.id

lemma leafLin_update (gm : GrSpEnd R N q) {A : Type} [DecidableEq A] (L : LinOrd A) (j : A)
    {B : A → Type} [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (y : ∀ a, N (B a)) (a : A)
    (z : N (B a)) :
    (fun a' => leafLin gm L j a' (update y a z a'))
      = update (fun a' => leafLin gm L j a' (y a')) a (leafLin gm L j a z) :=
  funext fun a' => apply_update (fun a' => ⇑(leafLin (R := R) gm L j (B := B) a')) y a z a'

lemma leafLin_hom (gm : GrSpEnd R N q) {A : Type} [DecidableEq A] (L : LinOrd A) (j : A)
    {B : A → Type} [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (y : ∀ a, N (B a))
    (c : A → Bool) (hy : ∀ a, GrSpecies.par (R := R) (V := N) (c a) (y a) = y a) (a : A) :
    leafLin gm L j a (y a) = (if ltB L a j then σ R (q && c a) else 1)
      • update y j (gm.app _ (y j)) a := by
  unfold leafLin
  by_cases haj : a = j
  · subst haj
    simp only [if_true, ltB_self, Bool.false_eq_true, if_false, update_self, one_smul]
  · simp only [if_neg haj, update_of_ne haj]
    split_ifs
    · exact GrSpecies.tw_hom (R := R) (V := N) q (hy a)
    · rw [one_smul, LinearMap.id_apply]

end LeafLin

end GrComposite

variable {R : Type u} [CommRing R]
  {M : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M A)] [GrSpecies R M]
  {N : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N A)] [GrSpecies R N]

variable (R M N) in
/-- **The relations of the graded composite**: linearity in the outer operation, multilinearity
in the inner ones, relabelling the inputs of the outer operation and of the inner ones, and
reordering homogeneous inner operations with the Koszul sign. -/
inductive GrCompRel (S : Type) : (GrCompGen M N S →₀ R) → Prop
  | add_m (g : GrCompGen M N S) (m' : M g.A) :
      GrCompRel S (Finsupp.single { g with m := g.m + m' } 1 - Finsupp.single g 1
        - Finsupp.single { g with m := m' } 1)
  | smul_m (g : GrCompGen M N S) (c : R) :
      GrCompRel S (Finsupp.single { g with m := c • g.m } 1 - c • Finsupp.single g 1)
  | add_y (g : GrCompGen M N S) (a : g.A) (z z' : N (g.B a)) :
      GrCompRel S (Finsupp.single { g with y := update g.y a (z + z') } 1
        - Finsupp.single { g with y := update g.y a z } 1
        - Finsupp.single { g with y := update g.y a z' } 1)
  | smul_y (g : GrCompGen M N S) (a : g.A) (c : R) (z : N (g.B a)) :
      GrCompRel S (Finsupp.single { g with y := update g.y a (c • z) } 1
        - c • Finsupp.single { g with y := update g.y a z } 1)
  | outer (g : GrCompGen M N S) {A : Type} [Fintype A] [DecidableEq A] (σ : A ≃ g.A) (m : M A) :
      GrCompRel S (Finsupp.single { g with m := SymSpecies.map (R := R) σ m } 1
        - Finsupp.single ⟨A, fun a => g.B (σ a), LinOrd.map σ.symm g.L, m, fun a => g.y (σ a),
            (Equiv.sigmaCongrLeft σ).trans g.e⟩ 1)
  | inner (g : GrCompGen M N S) {B : g.A → Type} [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
      (τ : ∀ a, g.B a ≃ B a) :
      GrCompRel S (Finsupp.single ⟨g.A, B, g.L, g.m, fun a => SymSpecies.map (R := R) (τ a) (g.y a),
          (Equiv.sigmaCongrRight τ).symm.trans g.e⟩ 1 - Finsupp.single g 1)
  | reorder (g : GrCompGen M N S) (L' : LinOrd g.A) (c : g.A → Bool)
      (hy : ∀ a, GrSpecies.par (R := R) (c a) (g.y a) = g.y a) :
      GrCompRel S (Finsupp.single g 1 - GrEnd.rsg R g.L L' c • Finsupp.single { g with L := L' } 1)

variable (R M N) in
/-- **The graded composite** `M ∘ N` of graded linear species, at a finite type `S`. -/
@[nolint unusedArguments]
def GrComposite (S : Type) [Fintype S] [DecidableEq S] : Type (max 1 u v w) :=
  (GrCompGen M N S →₀ R) ⧸ Submodule.span R {x | GrCompRel R M N S x}

namespace GrComposite

variable {S : Type} [Fintype S] [DecidableEq S]

noncomputable instance instAddCommGroup : AddCommGroup (GrComposite R M N S) :=
  Submodule.Quotient.addCommGroup _

noncomputable instance instModule : Module R (GrComposite R M N S) :=
  Submodule.Quotient.module _

variable (R) in
/-- **The class of a generator.** -/
noncomputable def mk (g : GrCompGen M N S) : GrComposite R M N S :=
  (Submodule.Quotient.mk (Finsupp.single g 1) :
    (GrCompGen M N S →₀ R) ⧸ Submodule.span R {x | GrCompRel R M N S x})

omit [Fintype S] [DecidableEq S] in
lemma mk_rel {x : GrCompGen M N S →₀ R} (hx : GrCompRel R M N S x) :
    (Submodule.Quotient.mk x :
      (GrCompGen M N S →₀ R) ⧸ Submodule.span R {x | GrCompRel R M N S x}) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span hx)

lemma mk_add_m (g : GrCompGen M N S) (m' : M g.A) :
    mk R { g with m := g.m + m' } = mk R g + mk R { g with m := m' } := by
  have h := mk_rel (GrCompRel.add_m (R := R) g m')
  rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub, sub_sub, sub_eq_zero] at h
  exact h

lemma mk_smul_m (g : GrCompGen M N S) (c : R) : mk R { g with m := c • g.m } = c • mk R g := by
  have h := mk_rel (GrCompRel.smul_m g c)
  rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, sub_eq_zero] at h
  exact h

lemma mk_add_y (g : GrCompGen M N S) (a : g.A) (z z' : N (g.B a)) :
    mk R { g with y := update g.y a (z + z') }
      = mk R { g with y := update g.y a z } + mk R { g with y := update g.y a z' } := by
  have h := mk_rel (GrCompRel.add_y (R := R) g a z z')
  rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub, sub_sub, sub_eq_zero] at h
  exact h

lemma mk_smul_y (g : GrCompGen M N S) (a : g.A) (c : R) (z : N (g.B a)) :
    mk R { g with y := update g.y a (c • z) } = c • mk R { g with y := update g.y a z } := by
  have h := mk_rel (GrCompRel.smul_y g a c z)
  rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, sub_eq_zero] at h
  exact h

/-- **Relabelling the inputs of the outer operation.** -/
lemma mk_outer (g : GrCompGen M N S) {A : Type} [Fintype A] [DecidableEq A] (σ : A ≃ g.A)
    (m : M A) :
    mk R { g with m := SymSpecies.map (R := R) σ m }
      = mk R ⟨A, fun a => g.B (σ a), LinOrd.map σ.symm g.L, m, fun a => g.y (σ a),
          (Equiv.sigmaCongrLeft σ).trans g.e⟩ := by
  have h := mk_rel (GrCompRel.outer (R := R) g σ m)
  rw [Submodule.Quotient.mk_sub, sub_eq_zero] at h
  exact h

/-- **Relabelling the inputs of the inner operations.** -/
lemma mk_inner (g : GrCompGen M N S) {B : g.A → Type} [∀ a, Fintype (B a)]
    [∀ a, DecidableEq (B a)] (τ : ∀ a, g.B a ≃ B a) :
    mk R ⟨g.A, B, g.L, g.m, fun a => SymSpecies.map (R := R) (τ a) (g.y a),
        (Equiv.sigmaCongrRight τ).symm.trans g.e⟩ = mk R g := by
  have h := mk_rel (GrCompRel.inner (R := R) g τ)
  rw [Submodule.Quotient.mk_sub, sub_eq_zero] at h
  exact h

/-- **Reordering homogeneous inner operations** costs the Koszul sign. -/
lemma mk_reorder (g : GrCompGen M N S) (L' : LinOrd g.A) (c : g.A → Bool)
    (hy : ∀ a, GrSpecies.par (R := R) (c a) (g.y a) = g.y a) :
    mk R g = GrEnd.rsg R g.L L' c • mk R { g with L := L' } := by
  have h := mk_rel (GrCompRel.reorder (R := R) g L' c hy)
  rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, sub_eq_zero] at h
  exact h

/-- **A generator is linear in its outer operation.** -/
noncomputable def mkM (g : GrCompGen M N S) : M g.A →ₗ[R] GrComposite R M N S where
  toFun m := mk R { g with m := m }
  map_add' m m' := mk_add_m { g with m := m } m'
  map_smul' c m := mk_smul_m { g with m := m } c

lemma mkM_apply (g : GrCompGen M N S) (m : M g.A) : mkM g m = mk R { g with m := m } := rfl

/-- **A generator is multilinear in its inner operations.** -/
noncomputable def mkY (g : GrCompGen M N S) :
    MultilinearMap R (fun a => N (g.B a)) (GrComposite R M N S) where
  toFun y := mk R { g with y := y }
  map_update_add' := by
    intro d y a z z'
    obtain rfl : d = g.instDecEqA := Subsingleton.elim _ _
    exact mk_add_y { g with y := y } a z z'
  map_update_smul' := by
    intro d y a c z
    obtain rfl : d = g.instDecEqA := Subsingleton.elim _ _
    exact mk_smul_y { g with y := y } a c z

lemma mkY_apply (g : GrCompGen M N S) (y : ∀ a, N (g.B a)) :
    mkY g y = mk R { g with y := y } := rfl

end GrComposite

lemma Finsupp.lift_single'' {X W : Type*} [AddCommGroup W] [Module R W] (F : X → W) (x : X)
    (c : R) : Finsupp.lift W R X F (Finsupp.single x c) = c • F x := by
  rw [Finsupp.lift_apply, Finsupp.sum_single_index]
  rw [zero_smul]

variable (R) in
/-- **The functions on generators respecting the relations of the graded composite**: they define
the linear maps out of it. -/
structure GrCompGen.Respects {S : Type} {W : Type x} [AddCommGroup W] [Module R W]
    (F : GrCompGen M N S → W) : Prop where
  add_m (g : GrCompGen M N S) (m' : M g.A) : F { g with m := g.m + m' } = F g + F { g with m := m' }
  smul_m (g : GrCompGen M N S) (c : R) : F { g with m := c • g.m } = c • F g
  add_y (g : GrCompGen M N S) (a : g.A) (z z' : N (g.B a)) :
    F { g with y := update g.y a (z + z') }
      = F { g with y := update g.y a z } + F { g with y := update g.y a z' }
  smul_y (g : GrCompGen M N S) (a : g.A) (c : R) (z : N (g.B a)) :
    F { g with y := update g.y a (c • z) } = c • F { g with y := update g.y a z }
  outer (g : GrCompGen M N S) {A : Type} [Fintype A] [DecidableEq A] (σ : A ≃ g.A) (m : M A) :
    F { g with m := SymSpecies.map (R := R) σ m }
      = F ⟨A, fun a => g.B (σ a), LinOrd.map σ.symm g.L, m, fun a => g.y (σ a),
          (Equiv.sigmaCongrLeft σ).trans g.e⟩
  inner (g : GrCompGen M N S) {B : g.A → Type} [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    (τ : ∀ a, g.B a ≃ B a) :
    F ⟨g.A, B, g.L, g.m, fun a => SymSpecies.map (R := R) (τ a) (g.y a),
        (Equiv.sigmaCongrRight τ).symm.trans g.e⟩ = F g
  reorder (g : GrCompGen M N S) (L' : LinOrd g.A) (c : g.A → Bool)
    (hy : ∀ a, GrSpecies.par (R := R) (c a) (g.y a) = g.y a) :
    F g = GrEnd.rsg R g.L L' c • F { g with L := L' }

namespace GrComposite

variable {S : Type} [Fintype S] [DecidableEq S] {W : Type x} [AddCommGroup W] [Module R W]

/-- **The linear map out of a graded composite** with given values on generators. -/
noncomputable def lift (F : GrCompGen M N S → W) (hF : GrCompGen.Respects R F) :
    GrComposite R M N S →ₗ[R] W :=
  Submodule.liftQ (Submodule.span R {x | GrCompRel R M N S x}) (Finsupp.lift W R _ F) <|
    Submodule.span_le.2 fun x hx => by
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      cases hx with
      | add_m g m' =>
        simp only [map_sub, Finsupp.lift_single'', one_smul, hF.add_m]
        abel
      | smul_m g c => simp only [map_sub, map_smul, Finsupp.lift_single'', one_smul, hF.smul_m,
          sub_self]
      | add_y g a z z' =>
        simp only [map_sub, Finsupp.lift_single'', one_smul, hF.add_y]
        abel
      | smul_y g a c z => simp only [map_sub, map_smul, Finsupp.lift_single'', one_smul,
          hF.smul_y, sub_self]
      | outer g σ m => simp only [map_sub, Finsupp.lift_single'', one_smul, hF.outer, sub_self]
      | inner g τ => simp only [map_sub, Finsupp.lift_single'', one_smul, hF.inner, sub_self]
      | reorder g L' c hy =>
        simp only [map_sub, map_smul, Finsupp.lift_single'', one_smul]
        rw [← hF.reorder g L' c hy, sub_self]

@[simp] lemma lift_mk (F : GrCompGen M N S → W) (hF : GrCompGen.Respects R F)
    (g : GrCompGen M N S) : lift F hF (mk R g) = F g := by
  show Submodule.liftQ _ _ _ (Submodule.Quotient.mk (Finsupp.single g 1)) = F g
  rw [Submodule.liftQ_apply, Finsupp.lift_single'', one_smul]

/-- **Linear maps out of a graded composite agree when they agree on generators.** -/
theorem hom_ext {φ ψ : GrComposite R M N S →ₗ[R] W} (h : ∀ g, φ (mk R g) = ψ (mk R g)) :
    φ = ψ :=
  Submodule.linearMap_qext _ (Finsupp.lhom_ext' fun g => LinearMap.ext_ring (h g))

omit [Fintype S] [DecidableEq S] in
/-- **Induction on a graded composite**: a property closed under linear combinations holds as soon
as it holds on generators. -/
@[elab_as_elim]
theorem induction_on [Fintype S] [DecidableEq S] {P : GrComposite R M N S → Prop}
    (z : GrComposite R M N S) (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (c : R) x, P x → P (c • x)) (hmk : ∀ g, P (mk R g)) : P z := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective
    (Submodule.span R {x | GrCompRel R M N S x}) z
  induction x using Finsupp.induction_linear with
  | zero => exact h0
  | add x y hx hy => exact hadd _ _ hx hy
  | single g c =>
    rw [← mul_one c, ← smul_eq_mul, ← Finsupp.smul_single, Submodule.Quotient.mk_smul]
    exact hsmul c _ (hmk g)

/-! ### Relabelling -/

/-- **Relabelling the inputs of a graded composite.** -/
noncomputable def map {S' : Type} [Fintype S'] [DecidableEq S'] (f : S ≃ S') :
    GrComposite R M N S →ₗ[R] GrComposite R M N S' :=
  lift (fun g => mk R (g.relabel f))
    { add_m := fun g m' => mk_add_m (g.relabel f) m'
      smul_m := fun g c => mk_smul_m (g.relabel f) c
      add_y := fun g a z z' => mk_add_y (g.relabel f) a z z'
      smul_y := fun g a c z => mk_smul_y (g.relabel f) a c z
      outer := @fun g _ _ _ σ m => mk_outer (g.relabel f) σ m
      inner := @fun g _ _ _ τ => mk_inner (g.relabel f) τ
      reorder := fun g L' c hy => mk_reorder (g.relabel f) L' c hy }

@[simp] lemma map_mk {S' : Type} [Fintype S'] [DecidableEq S'] (f : S ≃ S')
    (g : GrCompGen M N S) : map f (mk R g) = mk R (g.relabel f) :=
  lift_mk _ _ g

/-- **The graded composite is a linear species.** -/
noncomputable instance instSymSpecies : SymSpecies R (GrComposite R M N) where
  map f := map f
  map_refl := @fun A _ _ x => by
    have h : map (R := R) (M := M) (N := N) (Equiv.refl A) = LinearMap.id :=
      hom_ext fun g => by rw [map_mk]; rfl
    exact LinearMap.congr_fun h x
  map_trans := @fun A B C _ _ _ _ _ _ f f' x => by
    have h : map (R := R) (M := M) (N := N) (f.trans f') = (map f').comp (map f) :=
      hom_ext fun g => by rw [map_mk, LinearMap.comp_apply, map_mk, map_mk]; rfl
    exact LinearMap.congr_fun h x

lemma symSpecies_map_mk {S' : Type} [Fintype S'] [DecidableEq S'] (f : S ≃ S')
    (g : GrCompGen M N S) :
    SymSpecies.map (R := R) (V := GrComposite R M N) f (mk R g) = mk R (g.relabel f) :=
  map_mk f g

end GrComposite

/-! ## Parities -/

namespace GrComposite

variable {S : Type} [Fintype S] [DecidableEq S]

/-- The generator with its operations replaced by their parts of parities `p` and `c`. -/
abbrev parGen (g : GrCompGen M N S) (p : Bool) (c : g.A → Bool) : GrCompGen M N S :=
  { g with m := GrSpecies.par (R := R) p g.m, y := fun a => GrSpecies.par (R := R) (c a) (g.y a) }

variable (R) in
/-- The part of parity `b` of a generator: the outer operation and the inner ones split into
homogeneous parts, keeping those of total parity `b`. -/
noncomputable def parFun (b : Bool) (g : GrCompGen M N S) : GrComposite R M N S :=
  ∑ p : Bool, ∑ c : g.A → Bool, if xor p (GrEnd.tot c) = b then mk R (parGen (R := R) g p c) else 0

lemma mk_zero_m (g : GrCompGen M N S) : mk R { g with m := (0 : M g.A) } = 0 := by
  rw [← mkM_apply, map_zero]

lemma mk_zero_y (g : GrCompGen M N S) (a : g.A) :
    mk R { g with y := update g.y a (0 : N (g.B a)) } = 0 := by
  have h := mk_smul_y (R := R) g a 0 (0 : N (g.B a))
  rw [zero_smul, zero_smul] at h
  exact h

lemma mk_of_y_eq_zero (g : GrCompGen M N S) {a : g.A} (h : g.y a = 0) : mk R g = 0 := by
  have := mk_zero_y (R := R) g a
  rwa [show update g.y a (0 : N (g.B a)) = g.y from by rw [← h, update_eq_self]] at this

/-- **A generator is the sum of its homogeneous parts.** -/
lemma mk_eq_sum (g : GrCompGen M N S) :
    mk R g = ∑ p : Bool, ∑ c : g.A → Bool, mk R (parGen (R := R) g p c) := by
  have hm : mk R g = ∑ p : Bool, mk R { g with m := GrSpecies.par (R := R) p g.m } := by
    rw [Fintype.sum_bool, ← mk_add_m, add_comm, GrSpecies.par_add]
  rw [hm]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := (mkY (R := R) { g with m := GrSpecies.par (R := R) p g.m }).map_sum
    (fun a b => GrSpecies.par (R := R) b (g.y a))
  simp only [mkY_apply, Fintype.sum_bool] at this
  rw [show (fun a => GrSpecies.par (R := R) true (g.y a) + GrSpecies.par (R := R) false (g.y a))
    = g.y from funext fun a => by rw [add_comm, GrSpecies.par_add]] at this
  exact this

/-- **The part of parity `b` of a homogeneous generator.** -/
lemma parFun_hom (b : Bool) (g : GrCompGen M N S) {p : Bool} {c : g.A → Bool}
    (hm : GrSpecies.par (R := R) p g.m = g.m)
    (hy : ∀ a, GrSpecies.par (R := R) (c a) (g.y a) = g.y a) :
    parFun R b g = if xor p (GrEnd.tot c) = b then mk R g else 0 := by
  unfold parFun
  rw [Finset.sum_eq_single p, Finset.sum_eq_single c]
  · have : parGen (R := R) g p c = g := by
      cases g
      simp only [parGen] at hm hy ⊢
      rw [hm, show (fun a => _) = _ from funext hy]
    rw [this]
  · intro c' _ hc'
    obtain ⟨a, ha⟩ : ∃ a, c' a ≠ c a := by
      by_contra h
      exact hc' (funext fun a => by_contra fun h' => h ⟨a, h'⟩)
    split_ifs
    · refine mk_of_y_eq_zero _ (a := a) ?_
      show GrSpecies.par (R := R) (c' a) (g.y a) = 0
      rw [← hy a, GrSpecies.par_par, if_neg ha]
    · rfl
  · intro h
    exact absurd (Finset.mem_univ c) h
  · intro p' _ hp'
    refine Finset.sum_eq_zero fun c' _ => ?_
    split_ifs
    · have h0 : GrSpecies.par (R := R) p' g.m = 0 := by rw [← hm, GrSpecies.par_par, if_neg hp']
      calc mk R (parGen (R := R) g p' c')
          = mkM (parGen (R := R) g p' c') (GrSpecies.par (R := R) p' g.m) := rfl
        _ = 0 := by rw [h0, map_zero]
    · rfl
  · intro h
    exact absurd (Finset.mem_univ p) h

lemma par_update (c : Bool) {A : Type} [DecidableEq A] {B : A → Type} [∀ a, Fintype (B a)]
    [∀ a, DecidableEq (B a)] (cs : A → Bool) (y : ∀ a, N (B a)) (a : A) (v : N (B a)) :
    (fun a' => GrSpecies.par (R := R) (cs a') (update y a v a'))
      = update (fun a' => GrSpecies.par (R := R) (cs a') (y a')) a (GrSpecies.par (R := R) (cs a) v)
    := by
  have := c
  funext a'
  exact apply_update (fun a' => ⇑(GrSpecies.par (R := R) (V := N) (A := B a') (cs a'))) y a v a'

/-- The part of parity `b` of a generator whose inner operations are homogeneous. -/
lemma parFun_of_hy (b : Bool) (g : GrCompGen M N S) {c : g.A → Bool}
    (hy : ∀ a, GrSpecies.par (R := R) (c a) (g.y a) = g.y a) :
    parFun R b g = ∑ p : Bool,
      if xor p (GrEnd.tot c) = b then mk R { g with m := GrSpecies.par (R := R) p g.m } else 0 := by
  unfold parFun
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_eq_single c]
  · have : parGen (R := R) g p c = { g with m := GrSpecies.par (R := R) p g.m } := by
      simp only [parGen, hy]
    rw [this]
  · intro c' _ hc'
    obtain ⟨a, ha⟩ : ∃ a, c' a ≠ c a := by
      by_contra h
      exact hc' (funext fun a => by_contra fun h' => h ⟨a, h'⟩)
    split_ifs
    · refine mk_of_y_eq_zero _ (a := a) ?_
      show GrSpecies.par (R := R) (c' a) (g.y a) = 0
      rw [← hy a, GrSpecies.par_par, if_neg ha]
    · rfl
  · intro h
    exact absurd (Finset.mem_univ c) h

lemma parFun_respects (b : Bool) :
    GrCompGen.Respects R (parFun (M := M) (N := N) (S := S) R b) where
  add_m g m' := by
    simp only [parFun, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · show mkM (parGen (R := R) g p c) (GrSpecies.par (R := R) p (g.m + m'))
        = mkM (parGen (R := R) g p c) (GrSpecies.par (R := R) p g.m)
          + mkM (parGen (R := R) g p c) (GrSpecies.par (R := R) p m')
      rw [map_add, map_add]
    · rw [add_zero]
  smul_m g a := by
    simp only [parFun, Finset.smul_sum, smul_ite, smul_zero]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · show mkM (parGen (R := R) g p c) (GrSpecies.par (R := R) p (a • g.m))
        = a • mkM (parGen (R := R) g p c) (GrSpecies.par (R := R) p g.m)
      rw [map_smul, map_smul]
    · rfl
  add_y g a z z' := by
    simp only [parFun, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · show mkY { g with m := GrSpecies.par (R := R) p g.m }
          (fun a' => GrSpecies.par (R := R) (c a') (update g.y a (z + z') a'))
        = mkY { g with m := GrSpecies.par (R := R) p g.m }
            (fun a' => GrSpecies.par (R := R) (c a') (update g.y a z a'))
          + mkY { g with m := GrSpecies.par (R := R) p g.m }
            (fun a' => GrSpecies.par (R := R) (c a') (update g.y a z' a'))
      rw [par_update (R := R) b, par_update (R := R) b, par_update (R := R) b, map_add,
        MultilinearMap.map_update_add]
    · rw [add_zero]
  smul_y g a x z := by
    simp only [parFun, Finset.smul_sum, smul_ite, smul_zero]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · show mkY { g with m := GrSpecies.par (R := R) p g.m }
          (fun a' => GrSpecies.par (R := R) (c a') (update g.y a (x • z) a'))
        = x • mkY { g with m := GrSpecies.par (R := R) p g.m }
            (fun a' => GrSpecies.par (R := R) (c a') (update g.y a z a'))
      rw [par_update (R := R) b, par_update (R := R) b, map_smul,
        MultilinearMap.map_update_smul]
    · rfl
  outer := @fun g A _ _ σ m => by
    unfold parFun
    refine Finset.sum_congr rfl fun p _ => ?_
    refine Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl Bool)) _ _ fun c => ?_
    have ht : GrEnd.tot (Equiv.arrowCongr σ.symm (Equiv.refl Bool) c) = GrEnd.tot c := by
      show GrEnd.tot (fun a => c (σ a)) = GrEnd.tot c
      exact GrEnd.tot_comp_equiv σ c
    rw [ht]
    split_ifs
    · show mkM (parGen (R := R) g p c) (GrSpecies.par (R := R) p (SymSpecies.map (R := R) σ m)) = _
      rw [← GrSpecies.map_par (R := R) (V := M)]
      exact mk_outer (parGen (R := R) g p c) σ (GrSpecies.par (R := R) p m)
    · rfl
  inner := @fun g B _ _ τ => by
    unfold parFun
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · show mk R ⟨g.A, B, g.L, GrSpecies.par (R := R) p g.m,
          fun a => GrSpecies.par (R := R) (c a) (SymSpecies.map (R := R) (τ a) (g.y a)),
          (Equiv.sigmaCongrRight τ).symm.trans g.e⟩ = mk R (parGen (R := R) g p c)
      simp only [← GrSpecies.map_par]
      exact mk_inner (parGen (R := R) g p c) τ
    · rfl
  reorder g L' c hy := by
    rw [parFun_of_hy b g hy, parFun_of_hy (g := { g with L := L' }) b hy, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [smul_ite, smul_zero]
    split_ifs
    · exact mk_reorder { g with m := GrSpecies.par (R := R) p g.m } L' c hy
    · rfl

variable (R M N) in
/-- **The parity projections of the graded composite.** -/
noncomputable def par (b : Bool) : GrComposite R M N S →ₗ[R] GrComposite R M N S :=
  lift (parFun R b) (parFun_respects b)

@[simp] lemma par_mk (b : Bool) (g : GrCompGen M N S) : par R M N b (mk R g) = parFun R b g :=
  lift_mk _ _ g

lemma par_parGen (b p : Bool) (g : GrCompGen M N S) (c : g.A → Bool) :
    par R M N b (mk R (parGen (R := R) g p c))
      = if xor p (GrEnd.tot c) = b then mk R (parGen (R := R) g p c) else 0 := by
  have h1 : GrSpecies.par (R := R) p (GrSpecies.par (R := R) p g.m)
      = GrSpecies.par (R := R) p g.m := by rw [GrSpecies.par_par, if_pos rfl]
  have h2 : ∀ a, GrSpecies.par (R := R) (c a) (GrSpecies.par (R := R) (c a) (g.y a))
      = GrSpecies.par (R := R) (c a) (g.y a) := fun a => by rw [GrSpecies.par_par, if_pos rfl]
  rw [par_mk]
  exact parFun_hom (g := parGen (R := R) g p c) b (p := p) (c := c) h1 h2

/-- **The graded composite is a graded linear species.** -/
noncomputable instance instGrSpecies : GrSpecies R (GrComposite R M N) where
  toSymSpecies := instSymSpecies
  par b := par R M N b
  par_add := @fun A _ _ x => by
    have h : par R M N (S := A) false + par R M N true = LinearMap.id := hom_ext fun g => by
      rw [LinearMap.add_apply, par_mk, par_mk, LinearMap.id_apply, mk_eq_sum (R := R) g]
      simp only [parFun, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun c _ => ?_
      cases xor p (GrEnd.tot c) <;> simp
    exact LinearMap.congr_fun h x
  par_par := @fun A _ _ b b' x => by
    have h : (par R M N (S := A) b).comp (par R M N b')
        = if b = b' then par R M N b' else 0 := hom_ext fun g => by
      rw [LinearMap.comp_apply, par_mk]
      unfold parFun
      simp only [map_sum, apply_ite (par R M N b), map_zero, par_parGen]
      split_ifs with hb
      · subst hb
        rw [par_mk]
        unfold parFun
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun c _ => ?_
        split_ifs <;> rfl
      · rw [LinearMap.zero_apply]
        refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun c _ => ?_
        split_ifs with h1 h2
        · exact absurd (h2.symm.trans h1) hb
        · rfl
        · rfl
    have := LinearMap.congr_fun h x
    rw [LinearMap.comp_apply] at this
    rw [this]
    split_ifs <;> rfl
  map_par := @fun A B _ _ _ _ f b x => by
    have h : (map (R := R) (M := M) (N := N) f).comp (par R M N b)
        = (par R M N b).comp (map f) := hom_ext fun g => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, par_mk, map_mk, par_mk]
      unfold parFun
      simp only [map_sum, apply_ite (map (R := R) (M := M) (N := N) f), map_zero, map_mk]
      rfl
    exact LinearMap.congr_fun h x

lemma grSpecies_par_mk (b : Bool) (g : GrCompGen M N S) :
    GrSpecies.par (R := R) (V := GrComposite R M N) b (mk R g) = parFun R b g :=
  par_mk b g

end GrComposite

/-! ## Functoriality -/

namespace GrComposite

variable {M' : (A : Type) → [Fintype A] → [DecidableEq A] → Type x}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M' A)] [GrSpecies R M']
  {N' : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N' A)] [GrSpecies R N']
  {S : Type} [Fintype S] [DecidableEq S]

/-- The identity of a linear species. -/
def idSpHom : SymSpeciesHom R M M where
  app _ _ _ := LinearMap.id
  app_map _ _ := rfl

@[simp] lemma idSpHom_app {A : Type} [Fintype A] [DecidableEq A] (m : M A) :
    (idSpHom (R := R) (M := M)).app A m = m := rfl

/-- A generator, with its operations replaced by their images. -/
abbrev genMap₂ (φ : SymSpeciesHom R M M') (ψ : GrSpeciesHom R N N') (g : GrCompGen M N S) :
    GrCompGen M' N' S :=
  ⟨g.A, g.B, g.L, φ.app _ g.m, fun a => ψ.app _ (g.y a), g.e⟩

lemma app_update (ψ : GrSpeciesHom R N N') {A : Type} [DecidableEq A] {B : A → Type}
    [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (y : ∀ a, N (B a)) (a : A) (z : N (B a)) :
    (fun a' => ψ.app _ (update y a z a')) = update (fun a' => ψ.app _ (y a')) a (ψ.app _ z) :=
  funext fun a' => apply_update (fun a' => ⇑(ψ.app (B a'))) y a z a'

/-- The components of the graded composite of morphisms of species. -/
noncomputable def map₂App (φ : SymSpeciesHom R M M') (ψ : GrSpeciesHom R N N') (S : Type)
    [Fintype S] [DecidableEq S] : GrComposite R M N S →ₗ[R] GrComposite R M' N' S :=
  lift (fun g => mk R (genMap₂ φ ψ g))
    { add_m := fun g m' => by
        show mk R ⟨g.A, g.B, g.L, φ.app _ (g.m + m'), _, g.e⟩ = _
        rw [map_add]
        exact mk_add_m (genMap₂ φ ψ g) (φ.app _ m')
      smul_m := fun g c => by
        show mk R ⟨g.A, g.B, g.L, φ.app _ (c • g.m), _, g.e⟩ = _
        rw [map_smul]
        exact mk_smul_m (genMap₂ φ ψ g) c
      add_y := fun g a z z' => by
        show mk R ⟨g.A, g.B, g.L, φ.app _ g.m, fun a' => ψ.app _ (update g.y a (z + z') a'), g.e⟩
          = mk R ⟨g.A, g.B, g.L, φ.app _ g.m, fun a' => ψ.app _ (update g.y a z a'), g.e⟩
            + mk R ⟨g.A, g.B, g.L, φ.app _ g.m, fun a' => ψ.app _ (update g.y a z' a'), g.e⟩
        rw [app_update ψ g.y a, app_update ψ g.y a,
          app_update ψ g.y a, map_add]
        exact mk_add_y (genMap₂ φ ψ g) a _ _
      smul_y := fun g a c z => by
        show mk R ⟨g.A, g.B, g.L, φ.app _ g.m, fun a' => ψ.app _ (update g.y a (c • z) a'), g.e⟩
          = c • mk R ⟨g.A, g.B, g.L, φ.app _ g.m, fun a' => ψ.app _ (update g.y a z a'), g.e⟩
        rw [app_update ψ g.y a, app_update ψ g.y a,
          map_smul]
        exact mk_smul_y (genMap₂ φ ψ g) a c _
      outer := @fun g _ _ _ σ m => by
        show mk R ⟨g.A, g.B, g.L, φ.app _ (SymSpecies.map (R := R) σ m), _, g.e⟩ = _
        rw [φ.app_map]
        exact mk_outer (genMap₂ φ ψ g) σ (φ.app _ m)
      inner := @fun g _ _ _ τ => by
        show mk R ⟨g.A, _, g.L, φ.app _ g.m,
          fun a => ψ.app _ (SymSpecies.map (R := R) (τ a) (g.y a)), _⟩ = _
        simp only [ψ.app_map]
        exact mk_inner (genMap₂ φ ψ g) τ
      reorder := fun g L' c hy => mk_reorder (genMap₂ φ ψ g) L' c fun a => by
        show GrSpecies.par (R := R) (c a) (ψ.app _ (g.y a)) = ψ.app _ (g.y a)
        rw [← ψ.app_par, hy] }

lemma map₂App_mk (φ : SymSpeciesHom R M M') (ψ : GrSpeciesHom R N N') (g : GrCompGen M N S) :
    map₂App φ ψ S (mk R g) = mk R (genMap₂ φ ψ g) :=
  lift_mk _ _ g

/-- **The graded composite of morphisms of species**, the second one preserving parities. -/
noncomputable def map₂ (φ : SymSpeciesHom R M M') (ψ : GrSpeciesHom R N N') :
    SymSpeciesHom R (GrComposite R M N) (GrComposite R M' N') where
  app S _ _ := map₂App φ ψ S
  app_map f x := by
    have h := hom_ext (φ := (map₂App φ ψ _).comp (map f)) (ψ := (map f).comp (map₂App φ ψ _))
      fun g => by
        simp only [LinearMap.comp_apply, map_mk, map₂App_mk]
        rfl
    exact LinearMap.congr_fun h x

@[simp] lemma map₂_mk (φ : SymSpeciesHom R M M') (ψ : GrSpeciesHom R N N') (g : GrCompGen M N S) :
    (map₂ φ ψ).app S (mk R g) = mk R (genMap₂ φ ψ g) :=
  map₂App_mk φ ψ g

end GrComposite

/-! ## Odd maps at the inner operations -/

namespace GrComposite

variable {S : Type} [Fintype S] [DecidableEq S] {q : Bool}

/-- The generator with an endomorphism acting at the input `j`, with its Koszul sign. -/
noncomputable abbrev leafGen (gm : GrSpEnd R N q) (g : GrCompGen M N S) (j : g.A) :
    GrCompGen M N S :=
  ⟨g.A, g.B, g.L, GrSpecies.tw (R := R) q g.m, fun a => leafLin gm g.L j a (g.y a), g.e⟩

variable (R) in
/-- An endomorphism acting at each inner operation in turn, with its Koszul sign. -/
noncomputable def leafFun (gm : GrSpEnd R N q) (g : GrCompGen M N S) : GrComposite R M N S :=
  ∑ j : g.A, mk R (leafGen gm g j)

lemma leafFun_respects (gm : GrSpEnd R N q) :
    GrCompGen.Respects R (leafFun (M := M) (S := S) R gm) where
  add_m g m' := by
    simp only [leafFun, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    show mkM (leafGen gm g j) (GrSpecies.tw (R := R) q (g.m + m'))
      = mkM (leafGen gm g j) (GrSpecies.tw (R := R) q g.m)
        + mkM (leafGen gm g j) (GrSpecies.tw (R := R) q m')
    rw [map_add, map_add]
  smul_m g a := by
    simp only [leafFun, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show mkM (leafGen gm g j) (GrSpecies.tw (R := R) q (a • g.m))
      = a • mkM (leafGen gm g j) (GrSpecies.tw (R := R) q g.m)
    rw [map_smul, map_smul]
  add_y g a z z' := by
    simp only [leafFun, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    show mkY (leafGen gm g j) (fun a' => leafLin gm g.L j a' (update g.y a (z + z') a'))
      = mkY (leafGen gm g j) (fun a' => leafLin gm g.L j a' (update g.y a z a'))
        + mkY (leafGen gm g j) (fun a' => leafLin gm g.L j a' (update g.y a z' a'))
    rw [leafLin_update, leafLin_update, leafLin_update, map_add, MultilinearMap.map_update_add]
  smul_y g a x z := by
    simp only [leafFun, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show mkY (leafGen gm g j) (fun a' => leafLin gm g.L j a' (update g.y a (x • z) a'))
      = x • mkY (leafGen gm g j) (fun a' => leafLin gm g.L j a' (update g.y a z a'))
    rw [leafLin_update, leafLin_update, map_smul, MultilinearMap.map_update_smul]
  outer := @fun g A _ _ σ' m => by
    unfold leafFun
    refine (Fintype.sum_equiv σ'.symm _ _ fun j => ?_)
    have hj : j = σ' (σ'.symm j) := (σ'.apply_symm_apply j).symm
    show mkM (leafGen gm g j) (GrSpecies.tw (R := R) q (SymSpecies.map (R := R) σ' m)) = _
    rw [← GrSpecies.map_tw (R := R) (V := M)]
    refine (mk_outer (leafGen gm g j) σ' (GrSpecies.tw (R := R) q m)).trans ?_
    congr 2
    funext a'
    show leafLin gm g.L j (σ' a') (g.y (σ' a'))
      = leafLin gm (LinOrd.map σ'.symm g.L) (σ'.symm j) (B := fun a => g.B (σ' a)) a'
          (g.y (σ' a'))
    conv_lhs => rw [hj]
    unfold leafLin ltB
    simp only [σ'.injective.eq_iff]
    rfl
  inner := @fun g B _ _ τ => by
    unfold leafFun
    refine Finset.sum_congr rfl fun j _ => ?_
    have h : ∀ a, leafLin gm g.L j a (SymSpecies.map (R := R) (τ a) (g.y a))
        = SymSpecies.map (R := R) (τ a) (leafLin gm g.L j a (g.y a)) := fun a => by
      unfold leafLin
      split_ifs
      · exact gm.app_map (τ a) (g.y a)
      · exact (GrSpecies.map_tw (R := R) (V := N) q (τ a) (g.y a)).symm
      · rfl
    show mk R ⟨g.A, B, g.L, GrSpecies.tw (R := R) q g.m,
      fun a => leafLin gm g.L j a (SymSpecies.map (R := R) (τ a) (g.y a)), _⟩ = _
    simp only [h]
    exact mk_inner (leafGen gm g j) τ
  reorder g L' c hy := by
    unfold leafFun
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hy' : ∀ a, GrSpecies.par (R := R) (update c j (xor (c j) q) a)
        (update g.y j (gm.app _ (g.y j)) a) = update g.y j (gm.app _ (g.y j)) a := by
      intro a
      by_cases haj : a = j
      · subst haj
        simp only [update_self]
        rw [← gm.app_par, hy]
      · simp only [update_of_ne haj, hy]
    have hL : ∀ L₀ : LinOrd g.A, mk R ⟨g.A, g.B, L₀, GrSpecies.tw (R := R) q g.m,
        fun a => leafLin gm L₀ j a (g.y a), g.e⟩
        = (∏ a, if ltB L₀ a j then σ R (q && c a) else 1)
          • mk R ⟨g.A, g.B, L₀, GrSpecies.tw (R := R) q g.m, update g.y j (gm.app _ (g.y j)), g.e⟩
      := fun L₀ => by
      have := (mkY (R := R) ⟨g.A, g.B, L₀, GrSpecies.tw (R := R) q g.m, g.y, g.e⟩).map_smul_univ
        (fun a => if ltB L₀ a j then σ R (q && c a) else 1) (update g.y j (gm.app _ (g.y j)))
      simp only [mkY_apply] at this
      rw [← this]
      congr 2
      funext a
      exact leafLin_hom gm L₀ j g.y c hy a
    show mk R (leafGen gm g j) = GrEnd.rsg R g.L L' c • mk R (leafGen gm { g with L := L' } j)
    rw [hL g.L, hL L', mk_reorder ⟨g.A, g.B, g.L, GrSpecies.tw (R := R) q g.m,
      update g.y j (gm.app _ (g.y j)), g.e⟩ L' _ hy', smul_smul, smul_smul]
    congr 1
    exact rsg_update_mul g.L L' c j q

variable (R M) in
/-- **An endomorphism of parity `q` acting at the inner operations**, as a derivation with the
Koszul signs: `(1 ∘' g)(m ⊗ y₁ ⊗ ⋯ ⊗ yₖ) = ∑ⱼ ± m ⊗ y₁ ⊗ ⋯ ⊗ g yⱼ ⊗ ⋯ ⊗ yₖ`. -/
noncomputable def leafMap (gm : GrSpEnd R N q) : GrComposite R M N S →ₗ[R] GrComposite R M N S :=
  lift (leafFun R gm) (leafFun_respects gm)

@[simp] lemma leafMap_mk (gm : GrSpEnd R N q) (g : GrCompGen M N S) :
    leafMap R M gm (mk R g) = leafFun R gm g :=
  lift_mk _ _ g

end GrComposite

namespace GrComposite

variable {S : Type} [Fintype S] [DecidableEq S] {q : Bool}

lemma leafMap_map {S' : Type} [Fintype S'] [DecidableEq S'] (gm : GrSpEnd R N q) (f : S ≃ S')
    (x : GrComposite R M N S) : map f (leafMap R M gm x) = leafMap R M gm (map f x) := by
  have h : (map (R := R) (M := M) (N := N) f).comp (leafMap R M gm)
      = (leafMap R M gm).comp (map f) := hom_ext fun g => by
    simp only [LinearMap.comp_apply, leafMap_mk, map_mk, leafFun, map_sum]
    rfl
  exact LinearMap.congr_fun h x

omit [Fintype S] [DecidableEq S] in
lemma leafGen_hom (gm : GrSpEnd R N q) (g : GrCompGen M N S) (j : g.A) {p : Bool}
    {c : g.A → Bool} (hm : GrSpecies.par (R := R) p g.m = g.m)
    (hy : ∀ a, GrSpecies.par (R := R) (c a) (g.y a) = g.y a) :
    GrSpecies.par (R := R) p (leafGen gm g j).m = (leafGen gm g j).m ∧
      ∀ a, GrSpecies.par (R := R) (update c j (xor (c j) q) a) ((leafGen gm g j).y a)
        = (leafGen gm g j).y a := by
  refine ⟨?_, fun a => ?_⟩
  · show GrSpecies.par (R := R) p (GrSpecies.tw (R := R) q g.m) = GrSpecies.tw (R := R) q g.m
    rw [GrSpecies.par_tw, hm]
  · show GrSpecies.par (R := R) _ (leafLin gm g.L j a (g.y a)) = leafLin gm g.L j a (g.y a)
    unfold leafLin
    by_cases haj : a = j
    · subst haj
      simp only [if_true, update_self]
      rw [← gm.app_par, hy]
    · simp only [if_neg haj, update_of_ne haj]
      split_ifs
      · rw [GrSpecies.par_tw, hy]
      · exact hy a

/-- **An odd map at the inner operations shifts parities.** -/
lemma par_leafMap (gm : GrSpEnd R N q) (b : Bool) (x : GrComposite R M N S) :
    par R M N b (leafMap R M gm x) = leafMap R M gm (par R M N (xor b q) x) := by
  have h : (par R M N (S := S) b).comp (leafMap R M gm)
      = (leafMap R M gm).comp (par R M N (xor b q)) := hom_ext fun g => by
    simp only [LinearMap.comp_apply]
    rw [mk_eq_sum (R := R) g]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun c _ => ?_
    have hm : GrSpecies.par (R := R) p (parGen (R := R) g p c).m = (parGen (R := R) g p c).m := by
      show GrSpecies.par (R := R) p (GrSpecies.par (R := R) p g.m) = _
      rw [GrSpecies.par_par, if_pos rfl]
    have hy : ∀ a, GrSpecies.par (R := R) (c a) ((parGen (R := R) g p c).y a)
        = (parGen (R := R) g p c).y a := fun a => by
      show GrSpecies.par (R := R) (c a) (GrSpecies.par (R := R) (c a) (g.y a)) = _
      rw [GrSpecies.par_par, if_pos rfl]
    rw [par_mk, parFun_hom _ _ hm hy, leafMap_mk, leafFun, map_sum]
    have : ∀ j, par R M N b (mk R (leafGen gm (parGen (R := R) g p c) j))
        = if xor p (xor (GrEnd.tot c) q) = b
          then mk R (leafGen gm (parGen (R := R) g p c) j) else 0 := fun j => by
      obtain ⟨h1, h2⟩ := leafGen_hom gm (parGen (R := R) g p c) j hm hy
      rw [par_mk, parFun_hom _ _ h1 h2, tot_update]
      congr 2
      cases c j <;> cases q <;> simp
    simp only [this]
    split_ifs with h1 h2 h2
    · rw [leafMap_mk]
      rfl
    · exact absurd (by rw [← h1]; cases b <;> cases q <;> simp) h2
    · exact absurd (by rw [← Bool.xor_assoc, h2, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]) h1
    · rw [map_zero]
      exact Finset.sum_const_zero
  exact LinearMap.congr_fun h x

end GrComposite

end Operad
