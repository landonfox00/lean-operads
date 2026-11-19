/-
# Square-zero extensions of graded operads and the product of invariant families

A **square-zero extension** `Q̂ → Q` of graded operads, split as graded linear species
(`SqZeroExt`): inclusions `inc, eps : Q → Q̂` of the two summands, the projection `fst : Q̂ → Q`,
a morphism of graded operads, and `snd : Q̂ → Q`, with `eps Q` an ideal of square zero on which
`inc Q` acts through the compositions of `Q`. The composite `inc x ∘ᵢ inc y` is
`inc (x ∘ᵢ y) + eps (ω (x, y))`: the extension has a cochain `ω = snd (inc - ∘ inc -)`.

For invariant families of `Q`, with their product `⋆` (`Operad.InvPreLie`):

* **The cochain of the extension on two families** (`SqZeroExt.res`):
  `res (q, q') = snd (inc q ⋆ inc q')`, so `inc q ⋆ inc q' = inc (q ⋆ q') + eps (res (q, q'))`
  (`SqZeroExt.star_inc_inc`).
* **Cocycles.** For an odd family `α` with `α ⋆ α = 0`, `res (α, α)` commutes with `α`, so
  `[α, res (α, α)] = 0` (`SqZeroExt.bracket_res`): the associativity of `⋆` on odd families in
  `Q̂`, applied to `inc α`.
* **Coboundaries.** For a morphism of graded operads `F : Q → Q̂` with `fst ∘ F = 1`, and
  `ψ = snd ∘ F`, `res (α, α) = -[α, ψ α]` (`SqZeroExt.res_eq_neg_bracket`): `F α` is
  `inc α + eps (ψ α)` and its square vanishes.

**Convolution operads.** Composing with a morphism of graded linear species is a morphism of
graded linear species of convolution operads (`ConvOp.postSp`), and a square-zero extension
`Q̂ → Q` gives one of convolution operads `Hom(C, Q̂) → Hom(C, Q)` (`SqZeroExt.conv`). Its cochain
on two invariant families is their product along the cochain `ω` of `Q̂ → Q`
(`SqZeroExt.cochain`, `SqZeroExt.res_conv_apply`): `res (f, g) X` is the sum over the nonempty
subsets `T` of `X` of the convolutions `ω ∘ (f ⊗ g) ∘ Δ_T` (`ConvOp.bilC`, the convolution of a
bilinear map with two linear maps).

**The deformed operad.** For a two-cocycle `ω` of a symmetric operad `P`
(`Operad.Deformation`), the deformed operad `P_ω → P` is a square-zero extension, in even parity
(`SqZeroExt.ofCocycle`).
-/
import Operad.InvLie
import Operad.Deformation
import Operad.GrFreeEven

universe u v w x

namespace Operad

open Sym GerBV
open scoped TensorProduct

/-! ## Morphisms of species on invariant families -/

namespace GrOperad.Inv

variable {R : Type u} [CommRing R] {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
  {Q' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q' A)] [GrOperad R Q']

/-- **A morphism of graded linear species acts on the invariant families.** -/
def appSp (L : GrSpeciesHom R Q Q') : Inv R Q →ₗ[R] Inv R Q' where
  toFun q := ⟨fun A _ _ => L.app A (q.1 A), fun A B _ _ _ _ e => by
    show GrOperad.map (R := R) e (L.app A (q.1 A)) = L.app B (q.1 B)
    rw [← q.2 A B e]
    exact (L.app_map e (q.1 A)).symm⟩
  map_add' q q' := Subtype.ext (funext fun A => funext fun _ => funext fun _ =>
    map_add (L.app A) _ _)
  map_smul' c q := Subtype.ext (funext fun A => funext fun _ => funext fun _ =>
    map_smul (L.app A) _ _)

@[simp] lemma appSp_apply (L : GrSpeciesHom R Q Q') (q : Inv R Q) (A : Type) [Fintype A]
    [DecidableEq A] : (appSp L q).1 A = L.app A (q.1 A) := rfl

lemma isPar_appSp (L : GrSpeciesHom R Q Q') {p : Bool} {q : Inv R Q} (hq : IsPar p q) :
    IsPar p (appSp L q) := fun A _ _ =>
  (L.app_par p (q.1 A)).symm.trans (congrArg (L.app A) (hq A))

/-- **A pairing of morphisms of species is a pairing of the products**: if
`L₁ x ∘ᵢ L₂ y = L₃ (x ∘ᵢ y)`, then `L₁ q ⋆ L₂ q' = L₃ (q ⋆ q')`. -/
theorem appSp_star (L₁ L₂ L₃ : GrSpeciesHom R Q Q')
    (h : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
      (x : Q A) (y : Q B), GrOperad.comp (R := R) i (L₁.app A x) (L₂.app B y)
        = L₃.app _ (GrOperad.comp (R := R) i x y)) (q q' : Inv R Q) :
    star R Q' (appSp L₁ q) (appSp L₂ q') = appSp L₃ (star R Q q q') := by
  refine Subtype.ext (funext fun X => funext fun _ => funext fun _ => ?_)
  show ∑ S ∈ nonempties X, term (R := R) (appSp L₁ q).1 (appSp L₂ q').1 X S
    = L₃.app X (∑ S ∈ nonempties X, term (R := R) q.1 q'.1 X S)
  rw [map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  show GrOperad.map (R := R) (splitEquiv S) (GrOperad.comp (R := R) none
      (L₁.app _ (q.1 _)) (L₂.app _ (q'.1 _)))
    = L₃.app X (GrOperad.map (R := R) (splitEquiv S)
      (GrOperad.comp (R := R) none (q.1 _) (q'.1 _)))
  rw [h]
  exact (L₃.app_map (splitEquiv S) _).symm

/-- A pairing with values zero. -/
theorem appSp_star_eq_zero (L₁ L₂ : GrSpeciesHom R Q Q')
    (h : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
      (x : Q A) (y : Q B), GrOperad.comp (R := R) i (L₁.app A x) (L₂.app B y) = 0)
    (q q' : Inv R Q) : star R Q' (appSp L₁ q) (appSp L₂ q') = 0 := by
  refine Subtype.ext (funext fun X => funext fun _ => funext fun _ => ?_)
  show ∑ S ∈ nonempties X, term (R := R) (appSp L₁ q).1 (appSp L₂ q').1 X S = 0
  refine Finset.sum_eq_zero fun S _ => ?_
  show GrOperad.map (R := R) (splitEquiv S) (GrOperad.comp (R := R) none
      (L₁.app _ (q.1 _)) (L₂.app _ (q'.1 _))) = 0
  rw [h, map_zero]

/-- The component of an invariant family at a finite set, a linear map. -/
def evalL (X : Type) [Fintype X] [DecidableEq X] : Inv R Q →ₗ[R] Q X where
  toFun q := q.1 X
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma sum_apply {I : Type} (s : Finset I) (F : I → Inv R Q) (X : Type) [Fintype X]
    [DecidableEq X] : (∑ p ∈ s, F p).1 X = ∑ p ∈ s, (F p).1 X :=
  map_sum (evalL X) F s

end GrOperad.Inv

/-! ## Square-zero extensions -/

/-- **A square-zero extension of graded operads, split as graded linear species.** -/
structure SqZeroExt (R : Type u) [CommRing R]
    (Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    (Qh : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Qh A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Qh A)] [GrOperad R Qh] where
  /-- The inclusion of the first summand. -/
  inc : GrSpeciesHom R Q Qh
  /-- The inclusion of the ideal. -/
  eps : GrSpeciesHom R Q Qh
  /-- The projection, a morphism of graded operads. -/
  fst : GrOperadHom R Qh Q
  /-- The projection onto the ideal. -/
  snd : GrSpeciesHom R Qh Q
  fst_inc : ∀ {A : Type} [Fintype A] [DecidableEq A] (x : Q A), fst.app A (inc.app A x) = x
  snd_eps : ∀ {A : Type} [Fintype A] [DecidableEq A] (x : Q A), snd.app A (eps.app A x) = x
  inc_add_eps : ∀ {A : Type} [Fintype A] [DecidableEq A] (z : Qh A),
    inc.app A (fst.app A z) + eps.app A (snd.app A z) = z
  comp_inc_eps : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (x : Q A) (y : Q B), GrOperad.comp (R := R) i (inc.app A x) (eps.app B y)
      = eps.app _ (GrOperad.comp (R := R) i x y)
  comp_eps_inc : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (x : Q A) (y : Q B), GrOperad.comp (R := R) i (eps.app A x) (inc.app B y)
      = eps.app _ (GrOperad.comp (R := R) i x y)
  comp_eps_eps : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (x : Q A) (y : Q B), GrOperad.comp (R := R) i (eps.app A x) (eps.app B y) = 0

namespace SqZeroExt

open GrOperad.Inv

variable {R : Type u} [CommRing R] {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  {Qh : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Qh A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Qh A)] [GrOperad R Qh]
  (S : SqZeroExt R Q Qh)

/-- **The cochain of the extension on two invariant families**: `snd (inc q ⋆ inc q')`. -/
noncomputable def res (q q' : GrOperad.Inv R Q) : GrOperad.Inv R Q :=
  appSp S.snd (star R Qh (appSp S.inc q) (appSp S.inc q'))

lemma appHom_fst_inc (q : GrOperad.Inv R Q) : appHom S.fst (appSp S.inc q) = q :=
  Subtype.ext (funext fun A => funext fun _ => funext fun _ => S.fst_inc (q.1 A))

lemma appSp_snd_eps (q : GrOperad.Inv R Q) : appSp S.snd (appSp S.eps q) = q :=
  Subtype.ext (funext fun A => funext fun _ => funext fun _ => S.snd_eps (q.1 A))

lemma appSp_inc_add_eps (Z : GrOperad.Inv R Qh) :
    appSp S.inc (appHom S.fst Z) + appSp S.eps (appSp S.snd Z) = Z :=
  Subtype.ext (funext fun A => funext fun _ => funext fun _ => S.inc_add_eps (Z.1 A))

/-- **The product of the first summand**: `inc q ⋆ inc q' = inc (q ⋆ q') + eps (res (q, q'))`. -/
theorem star_inc_inc (q q' : GrOperad.Inv R Q) :
    star R Qh (appSp S.inc q) (appSp S.inc q')
      = appSp S.inc (star R Q q q') + appSp S.eps (S.res q q') := by
  have h := S.appSp_inc_add_eps (star R Qh (appSp S.inc q) (appSp S.inc q'))
  rw [appHom_star, S.appHom_fst_inc, S.appHom_fst_inc] at h
  exact h.symm

lemma star_inc_eps (q q' : GrOperad.Inv R Q) :
    star R Qh (appSp S.inc q) (appSp S.eps q') = appSp S.eps (star R Q q q') :=
  appSp_star S.inc S.eps S.eps S.comp_inc_eps q q'

lemma star_eps_inc (q q' : GrOperad.Inv R Q) :
    star R Qh (appSp S.eps q) (appSp S.inc q') = appSp S.eps (star R Q q q') :=
  appSp_star S.eps S.inc S.eps S.comp_eps_inc q q'

lemma star_eps_eps (q q' : GrOperad.Inv R Q) :
    star R Qh (appSp S.eps q) (appSp S.eps q') = 0 :=
  appSp_star_eq_zero S.eps S.eps S.comp_eps_eps q q'

lemma isPar_res {p p' : Bool} {q q' : GrOperad.Inv R Q} (hq : IsPar p q) (hq' : IsPar p' q') :
    IsPar (xor p p') (S.res q q') :=
  isPar_appSp S.snd (isPar_star (isPar_appSp S.inc hq) (isPar_appSp S.inc hq'))

/-- **The cochain of the extension on an odd family of square zero commutes with it.** -/
theorem star_res_comm {α : GrOperad.Inv R Q} (hα : IsPar true α) (h0 : star R Q α α = 0) :
    star R Q (S.res α α) α = star R Q α (S.res α α) := by
  have h := assoc_odd (appSp S.inc α) (appSp S.inc α) (isPar_appSp S.inc hα)
  rw [S.star_inc_inc, h0, map_zero, zero_add, S.star_eps_inc, S.star_inc_eps] at h
  have h' := congrArg (appSp S.snd) h
  rwa [S.appSp_snd_eps, S.appSp_snd_eps] at h'

/-- **Cocycles**: the cochain of the extension on an odd family `α` of square zero is closed for
the bracket with `α`. -/
theorem bracket_res {α : GrOperad.Inv R Q} (hα : IsPar true α) (h0 : star R Q α α = 0) :
    bracket R Q α (S.res α α) = 0 := by
  have hr : IsPar false (S.res α α) := by
    have h := S.isPar_res hα hα
    rwa [Bool.xor_self] at h
  rw [bracket_hom hα hr, Bool.and_false, σ_false, one_smul, S.star_res_comm hα h0, sub_self]

/-- **Coboundaries**: for a morphism of graded operads `F : Q → Q̂` with `fst ∘ F = 1`, the
cochain of the extension on an odd family `α` of square zero is minus the bracket of `α` with
`snd ∘ F ∘ α`. -/
theorem res_eq_neg_bracket (F : GrOperadHom R Q Qh)
    (hF : ∀ {A : Type} [Fintype A] [DecidableEq A] (x : Q A), S.fst.app A (F.app A x) = x)
    {α : GrOperad.Inv R Q} (hα : IsPar true α) (h0 : star R Q α α = 0) :
    S.res α α = -bracket R Q α (appSp S.snd (appHom F α)) := by
  have hfst : appHom S.fst (appHom F α) = α :=
    Subtype.ext (funext fun A => funext fun _ => funext fun _ => hF (α.1 A))
  have hA : appHom F α = appSp S.inc α + appSp S.eps (appSp S.snd (appHom F α)) := by
    have h := S.appSp_inc_add_eps (appHom F α)
    rw [hfst] at h
    exact h.symm
  have h := appHom_star F α α
  rw [h0, map_zero] at h
  have hu : IsPar true (appSp S.snd (appHom F α)) := isPar_appSp S.snd (fun A _ _ => by
    show GrOperad.par (R := R) true (F.app A (α.1 A)) = F.app A (α.1 A)
    rw [← F.app_par, hα A])
  generalize appSp S.snd (appHom F α) = u at hA hu ⊢
  rw [hA] at h
  simp only [map_add, LinearMap.add_apply] at h
  rw [S.star_inc_inc, h0, map_zero, zero_add, S.star_inc_eps, S.star_eps_inc, S.star_eps_eps,
    add_zero, ← map_add, ← map_add] at h
  have h' := congrArg (appSp S.snd) h
  rw [map_zero, S.appSp_snd_eps] at h'
  rw [bracket_hom hα hu, Bool.and_self, σ_true, neg_one_smul_inv, sub_neg_eq_add]
  refine eq_neg_of_add_eq_zero_left (Eq.trans ?_ h'.symm)
  abel

end SqZeroExt

/-! ## Convolution operads -/

namespace ConvOp

variable {R : Type u} [CommRing R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {P' : (A : Type) → [Fintype A] → [DecidableEq A] → Type x}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P' A)] [GrOperad R P']
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **Composing with a morphism of graded linear species is a morphism of graded linear species
of convolution operads.** -/
noncomputable def postSp (L : GrSpeciesHom R P P') :
    GrSpeciesHom R (ConvOp R C P) (ConvOp R C P') where
  app A _ _ := postL (L.app A)
  app_map σ' f := by
    ext x
    show toLin (postL (L.app _) (GrOperad.map (R := R) σ' f)) x
      = toLin (GrOperad.map (R := R) σ' (postL (L.app _) f)) x
    simp only [map_def, toLin_postL, LinearMap.comp_apply, mapC_apply]
    exact L.app_map σ' _
  app_par b f := by
    ext x
    show toLin (postL (L.app _) (GrOperad.par (R := R) b f)) x
      = toLin (GrOperad.par (R := R) b (postL (L.app _) f)) x
    simp only [par_def, toLin_postL, LinearMap.comp_apply, parC_apply, map_sum]
    exact Finset.sum_congr rfl fun c _ => L.app_par _ _

@[simp] lemma postSp_app (L : GrSpeciesHom R P P') (f : ConvOp R C P A) :
    toLin ((postSp (C := C) L).app A f) = L.app A ∘ₗ toLin f := rfl

/-- **A pairing of morphisms of species is a pairing of the convolution composites.** -/
theorem comp_postL (L₁ L₂ : GrSpeciesHom R P P') (i : A)
    (M : P (Without A i ⊕ B) →ₗ[R] P' (Without A i ⊕ B))
    (h : ∀ (x : P A) (y : P B), GrOperad.comp (R := R) i (L₁.app A x) (L₂.app B y)
      = M (GrOperad.comp (R := R) i x y)) (f : ConvOp R C P A) (g : ConvOp R C P B) :
    GrOperad.comp (R := R) i (postL (C := C) (L₁.app A) f) (postL (C := C) (L₂.app B) g)
      = postL M (GrOperad.comp (R := R) i f g) := by
  ext x
  simp only [comp_def, toLin_postL, LinearMap.comp_apply, toLin_compC]
  induction GrCooperad.decomp (R := R) (C := C) i x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [kap, LinearMap.coe_sum, Finset.sum_apply, map_sum, TensorProduct.map_tmul,
      LinearMap.comp_apply, mu_tmul]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hp : toLin (parC q (postL (C := C) (L₂.app B) g)) b
        = L₂.app B (toLin (parC q g) b) := by
      simp only [parC_apply, toLin_postL, LinearMap.comp_apply, map_sum]
      exact Finset.sum_congr rfl fun c _ => (L₂.app_par _ _).symm
    rw [hp, toLin_postL, LinearMap.comp_apply, h]
  | add a b ha hb => simp only [map_add, ha, hb]

/-! ### The convolution of a bilinear map -/

/-- **The convolution of a bilinear map** `β` with two linear maps: `β ∘ (f ⊗ g) ∘ Δᵢ`, with the
Koszul sign. The composition of the convolution operad is the case of the composition of `P`
(`ConvOp.bilC_comp`). -/
noncomputable def bilC (i : A) (β : P A →ₗ[R] P B →ₗ[R] P' (Without A i ⊕ B))
    (f : ConvOp R C P A) (g : ConvOp R C P B) : ConvOp R C P' (Without A i ⊕ B) :=
  of (TensorProduct.lift β ∘ₗ kap f g ∘ₗ GrCooperad.decomp (R := R) (C := C) i)

omit [GrOperad R P'] in
lemma toLin_bilC (i : A) (β : P A →ₗ[R] P B →ₗ[R] P' (Without A i ⊕ B))
    (f : ConvOp R C P A) (g : ConvOp R C P B) :
    toLin (bilC i β f g)
      = TensorProduct.lift β ∘ₗ kap f g ∘ₗ GrCooperad.decomp (R := R) (C := C) i := rfl

lemma bilC_comp (i : A) (f : ConvOp R C P A) (g : ConvOp R C P B) :
    bilC i (GrOperad.comp (R := R) i) f g = GrOperad.comp (R := R) i f g := rfl

lemma lift_sum_apply {M N K : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [AddCommGroup K] [Module R K] {I : Type} (s : Finset I)
    (β : I → M →ₗ[R] N →ₗ[R] K) (t : M ⊗[R] N) :
    TensorProduct.lift (∑ q ∈ s, β q) t = ∑ q ∈ s, TensorProduct.lift (β q) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp only [TensorProduct.lift.tmul, LinearMap.coe_sum, Finset.sum_apply]
  | add a b ha hb => simp only [map_add, ha, hb, Finset.sum_add_distrib]

omit [GrOperad R P'] in
/-- The convolution is additive in the bilinear map. -/
lemma bilC_sum {I : Type} (s : Finset I) (i : A)
    (β : I → P A →ₗ[R] P B →ₗ[R] P' (Without A i ⊕ B)) (f : ConvOp R C P A)
    (g : ConvOp R C P B) : bilC i (∑ q ∈ s, β q) f g = ∑ q ∈ s, bilC i (β q) f g := by
  ext x
  simp only [toLin_sum, LinearMap.coe_sum, Finset.sum_apply, toLin_bilC, LinearMap.comp_apply]
  exact lift_sum_apply s β _

omit [GrOperad R P'] in
lemma bilC_zero (i : A) (f : ConvOp R C P A) (g : ConvOp R C P B) :
    bilC i (0 : P A →ₗ[R] P B →ₗ[R] P' (Without A i ⊕ B)) f g = 0 := by
  have h := bilC_sum (∅ : Finset Unit) i
    (fun _ => (0 : P A →ₗ[R] P B →ₗ[R] P' (Without A i ⊕ B))) f g
  simpa using h

omit [GrOperad R P'] in
/-- Composing the convolution with a linear map. -/
lemma postL_bilC {P'' : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P'' A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P'' A)] [GrOperad R P''] (i : A)
    (N : P' (Without A i ⊕ B) →ₗ[R] P'' (Without A i ⊕ B))
    (β : P A →ₗ[R] P B →ₗ[R] P' (Without A i ⊕ B)) (f : ConvOp R C P A)
    (g : ConvOp R C P B) : postL N (bilC i β f g) = bilC i (β.compr₂ N) f g := by
  ext x
  rw [toLin_postL, toLin_bilC, toLin_bilC, TensorProduct.lift_compr₂]
  rfl

/-- **Composing the two arguments of the bilinear map with morphisms of graded linear species**
composes the two linear maps with them. -/
theorem bilC_compl₁₂ {P'' : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P'' A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P'' A)] [GrOperad R P'']
    (L₁ L₂ : GrSpeciesHom R P P') (i : A)
    (β : P' A →ₗ[R] P' B →ₗ[R] P'' (Without A i ⊕ B)) (f : ConvOp R C P A)
    (g : ConvOp R C P B) :
    bilC i (β.compl₁₂ (L₁.app A) (L₂.app B)) f g
      = bilC i β (postL (C := C) (L₁.app A) f) (postL (C := C) (L₂.app B) g) := by
  ext x
  simp only [toLin_bilC, LinearMap.comp_apply]
  induction GrCooperad.decomp (R := R) (C := C) i x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [kap, LinearMap.coe_sum, Finset.sum_apply, map_sum, TensorProduct.map_tmul,
      LinearMap.comp_apply, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, toLin_postL]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hp : toLin (parC q (postL (C := C) (L₂.app B) g)) b
        = L₂.app B (toLin (parC q g) b) := by
      simp only [parC_apply, toLin_postL, LinearMap.comp_apply, map_sum]
      exact Finset.sum_congr rfl fun c _ => (L₂.app_par _ _).symm
    rw [hp]
  | add a b ha hb => simp only [map_add, ha, hb]

end ConvOp

/-- **A square-zero extension of graded operads gives one of convolution operads.** -/
noncomputable def SqZeroExt.conv {R : Type u} [CommRing R]
    {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
    {Qh : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Qh A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Qh A)] [GrOperad R Qh]
    (S : SqZeroExt R Q Qh) (C : (A : Type) → [Fintype A] → [DecidableEq A] → Type x)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C] :
    SqZeroExt R (ConvOp R C Q) (ConvOp R C Qh) where
  inc := ConvOp.postSp S.inc
  eps := ConvOp.postSp S.eps
  fst := ConvOp.postHom S.fst
  snd := ConvOp.postSp S.snd
  fst_inc _ := ConvOp.ext fun _ => S.fst_inc _
  snd_eps _ := ConvOp.ext fun _ => S.snd_eps _
  inc_add_eps _ := ConvOp.ext fun _ => S.inc_add_eps _
  comp_inc_eps i f g := ConvOp.comp_postL S.inc S.eps i _ (S.comp_inc_eps i) f g
  comp_eps_inc i f g := ConvOp.comp_postL S.eps S.inc i _ (S.comp_eps_inc i) f g
  comp_eps_eps i f g := (ConvOp.comp_postL S.eps S.eps i 0 (S.comp_eps_eps i) f g).trans
    (ConvOp.ext fun _ => rfl)

section Cochain

variable {R : Type u} [CommRing R] {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  {Qh : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Qh A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Qh A)] [GrOperad R Qh]
  (S : SqZeroExt R Q Qh)

/-- **The cochain of a square-zero extension**: `ωᵢ(x, y) = snd (inc x ∘ᵢ inc y)`. -/
def SqZeroExt.cochain {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (i : A) : Q A →ₗ[R] Q B →ₗ[R] Q (Without A i ⊕ B) :=
  ((GrOperad.comp (R := R) i).compr₂ (S.snd.app _)).compl₁₂ (S.inc.app A) (S.inc.app B)

lemma SqZeroExt.cochain_apply {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (i : A) (x : Q A) (y : Q B) :
    S.cochain i x y
      = S.snd.app _ (GrOperad.comp (R := R) i (S.inc.app A x) (S.inc.app B y)) := rfl

/-- **The cochain of an extension of convolution operads on two invariant families** is the
product of the two families along the cochain of the extension:
`res (f, g) X = ∑_{∅ ≠ T ⊆ X} ω ∘ (f (X / T) ⊗ g T) ∘ Δ_T`. -/
theorem SqZeroExt.res_conv_apply (C : (A : Type) → [Fintype A] → [DecidableEq A] → Type x)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
    (f g : GrOperad.Inv R (ConvOp R C Q)) (X : Type) [Fintype X] [DecidableEq X] :
    ((S.conv C).res f g).1 X = ∑ T ∈ nonempties X, GrOperad.map (R := R) (splitEquiv T)
      (ConvOp.bilC none (S.cochain none) (f.1 (SOut T)) (g.1 (SIn T))) := by
  show ConvOp.postL (S.snd.app X) (∑ T ∈ nonempties X, GrOperad.Inv.term (R := R)
      (GrOperad.Inv.appSp (S.conv C).inc f).1 (GrOperad.Inv.appSp (S.conv C).inc g).1 X T) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  refine ((ConvOp.postSp (C := C) S.snd).app_map (splitEquiv T) _).trans (congrArg _ ?_)
  show ConvOp.postL (S.snd.app _) (GrOperad.comp (R := R) none
      (ConvOp.postL (S.inc.app _) (f.1 _)) (ConvOp.postL (S.inc.app _) (g.1 _))) = _
  rw [← ConvOp.bilC_comp, ConvOp.postL_bilC, ← ConvOp.bilC_compl₁₂]
  rfl

end Cochain

/-! ## The deformed operad of a cocycle -/

section Deformed

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]

/-- **A morphism of symmetric operads, as a morphism of graded operads in even parity.** -/
def SymGr.homOf {P' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P' A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P' A)] [SymOperad R P']
    (ψ : SymOperadHom R P P') : GrOperadHom R (SymGr P) (SymGr P') where
  app A _ _ := ψ.app A
  app_par b x := by
    cases b
    · rfl
    · exact map_zero _
  app_map e x := ψ.app_map e x
  app_one := ψ.app_one
  app_comp i x y := ψ.app_comp i x y

/-- An equivariant family of linear maps between symmetric operads, as a morphism of graded
linear species in even parity. -/
def SymGr.spOf {P' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P' A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P' A)] [SymOperad R P']
    (L : ∀ (A : Type) [Fintype A] [DecidableEq A], P A →ₗ[R] P' A)
    (hL : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
      (x : P A), L B (SymOperad.map (R := R) e x) = SymOperad.map (R := R) e (L A x)) :
    GrSpeciesHom R (SymGr P) (SymGr P') where
  app A _ _ := L A
  app_map e x := hL e x
  app_par b x := by
    cases b
    · rfl
    · exact map_zero _

variable (ω : SymCochain R P) [hω : Fact ω.IsCocycle]

/-- **The deformed operad of a cocycle is a square-zero extension**, in even parity. -/
noncomputable def SqZeroExt.ofCocycle : SqZeroExt R (SymGr P) (SymGr (Deformed ω)) where
  inc := SymGr.spOf (fun A _ _ => LinearMap.inl R (P A) (P A)) fun _ _ =>
    Deformed.ext rfl (map_zero _).symm
  eps := SymGr.spOf (fun A _ _ => LinearMap.inr R (P A) (P A)) fun _ _ =>
    Deformed.ext (map_zero _).symm rfl
  fst := SymGr.homOf (Deformed.fstHom ω)
  snd := SymGr.spOf (fun A _ _ => Deformed.sndL ω A) fun _ _ => rfl
  fst_inc _ := rfl
  snd_eps _ := rfl
  inc_add_eps _ := Deformed.ext (add_zero _) (zero_add _)
  comp_inc_eps i x y := Deformed.comp_mk_zero_right (ω := ω) i (Deformed.mk x 0) y
  comp_eps_inc i x y := Deformed.comp_mk_zero_left (ω := ω) i x (Deformed.mk y 0)
  comp_eps_eps i x y := (Deformed.comp_mk_zero_left (ω := ω) i x (Deformed.mk 0 y)).trans
    (Deformed.ext rfl (LinearMap.map_zero _))

end Deformed

end Operad
