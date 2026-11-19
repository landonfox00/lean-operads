/-
# The deformation complex of a presented operad and the two-cochains of the operad

Let `T(E)/(r)` be a presented operad over a field, with Koszul dual cooperad `P^¡` and twisting
morphism `κ : P^¡ → T(E)/(r)`, and let `φ : T(E)/(r) → P` be a morphism to a symmetric operad `P`
in modules, read as a graded operad in even parity with the zero differential. The deformation
complex `Def(φ) = Hom_𝔖(P^¡, P)` of `Operad.DeformationComplex` has the differential
`[φ κ, -]` (`Koszul.defD_apply`). The two-cochains of `P` are those of `Operad.Deformation`, the
equivariant bilinear maps `ωᵢ : P(A) ⊗ P(B) → P(A ∘ᵢ B)`.

* **The comparison map** (`Koszul.cochainOf`, `Koszul.cochainOf_apply`). A two-cocycle `ω` of
  `P` has the cochain `ω(φκ, φκ)` of `Def(φ)`, the convolution of `ω` with two copies of `φ κ`:
  on a finite set `X`, `∑_{∅ ≠ T ⊆ X} ω ∘ (φκ ⊗ φκ) ∘ Δ_T`. It is defined as the cochain of the
  square-zero extension `Hom(P^¡, P_ω) → Hom(P^¡, P)` on `(φκ, φκ)` (`Operad.SqZeroExt`).
* **Cocycles go to cocycles** (`Koszul.defD_cochainOf`), and the cochain of a cocycle is even
  (`Koszul.isPar_cochainOf`).
* **Coboundaries go to coboundaries** (`Koszul.cochainOf_coboundary`): the cochain of `δψ` is
  `-d(ψ ∘ φκ)`.
* **Degree one** (`Koszul.defD_postEndo_derivation`): for a derivation `D` of `P`, the cochain
  `D ∘ φκ` is a cocycle.
* **The two obstructions agree** (`Koszul.obstruction_trivLift`). A trivialization `Φ = ∑ tᵏ Φₖ`
  up to order `N` of the trivial formal deformation of `P` (`Operad.FormalDeformation`) is a
  morphism of operads `P → P[t]/tᴺ⁺¹`, and its composite with `φ` is a lift of `φ` to order `N`
  (`Koszul.trivLift`, a `Koszul.Lift` of `Operad.DeformationLift`). The obstruction of this lift
  is the cochain of the obstruction cocycle of `Φ` at order `N + 1`. If `Φ` extends to order
  `N + 1`, the obstruction of the lift is `-d(Φ_{N+1} ∘ φκ)`
  (`Koszul.obstruction_trivLift_of_extends`).

The map from the cohomology of the two-cochains of `P` to the cohomology of `Def(φ)` is not shown
to be injective or surjective, for a Koszul presentation of `P` or otherwise. The formal
deformations other than the trivial one are not compared: a `Koszul.Lift` has values in the
truncated polynomials with the composition of the target extended linearly.
-/
import Operad.SqZeroExt
import Operad.DeformationLift
import Operad.FormalDeformation

universe u v w

namespace Operad

open Sym GerBV
open scoped TensorProduct

/-! ## Square-zero extensions of an operad with the zero differential -/

/-- **A square-zero extension of `Q`, read on `Q` with the zero differential.** -/
def SqZeroExt.zeroDG {R : Type u} [CommRing R]
    {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
    {Qh : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Qh A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Qh A)] [GrOperad R Qh]
    (S : SqZeroExt R Q Qh) : SqZeroExt R (ZeroDG R Q) Qh where
  inc := { app := fun A _ _ => S.inc.app A, app_map := S.inc.app_map, app_par := S.inc.app_par }
  eps := { app := fun A _ _ => S.eps.app A, app_map := S.eps.app_map, app_par := S.eps.app_par }
  fst := S.fst.toZeroDG
  snd := { app := fun A _ _ => S.snd.app A, app_map := S.snd.app_map, app_par := S.snd.app_par }
  fst_inc := S.fst_inc
  snd_eps := S.snd_eps
  inc_add_eps := S.inc_add_eps
  comp_inc_eps := S.comp_inc_eps
  comp_eps_inc := S.comp_eps_inc
  comp_eps_eps := S.comp_eps_eps

section Sym

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- An equivariant family of endomorphisms of `P`, as an endomorphism of the graded linear
species of `P` in even parity. -/
def SymEndo.toSp (ψ : SymEndo R P) :
    GrSpeciesHom R (ZeroDG R (SymGr P)) (ZeroDG R (SymGr P)) where
  app A _ _ := ψ.app A
  app_map e x := ψ.app_map e x
  app_par b x := by
    cases b
    · rfl
    · exact map_zero _

/-- A two-cochain of `P`, on `P` in even parity. -/
def SymCochain.gr (ω : SymCochain R P) (i : A) :
    ZeroDG R (SymGr P) A →ₗ[R] ZeroDG R (SymGr P) B →ₗ[R] ZeroDG R (SymGr P) (Without A i ⊕ B) :=
  ω i

/-- **The cochain of the deformed operad of a cocycle is the cocycle.** -/
lemma SqZeroExt.cochain_ofCocycle (ω : SymCochain R P) [Fact ω.IsCocycle] (i : A) :
    ((SqZeroExt.ofCocycle ω).zeroDG).cochain (A := A) (B := B) i = ω.gr i := by
  refine LinearMap.ext₂ fun x y => ?_
  show Deformed.snd (SymOperad.comp (R := R) i (Deformed.mk (ω := ω) x 0)
    (Deformed.mk (ω := ω) y 0)) = ω i x y
  rw [Deformed.snd_symComp]
  simp

/-- The morphism `x ↦ (x, ψ x)` of a family whose coboundary is `ω`, in even parity. -/
def SymEndo.liftGr {ω : SymCochain R P} [Fact ω.IsCocycle] (ψ : SymEndo R P)
    (hψ : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
      (i : A) (x : P A) (y : P B), ω i x y = ψ.coboundary i x y) :
    GrOperadHom R (ZeroDG R (SymGr P)) (SymGr (Deformed ω)) where
  app A _ _ := (ψ.lift hψ).app A
  app_par b x := (SymGr.homOf (ψ.lift hψ)).app_par b x
  app_map e x := (ψ.lift hψ).app_map e x
  app_one := (ψ.lift hψ).app_one
  app_comp i x y := (ψ.lift hψ).app_comp i x y

/-- **A morphism to order `n` into the trivial formal deformation**:
`Φ_n(x ∘ᵢ y) = ∑_{a+b=n} Φ_a x ∘ᵢ Φ_b y`. -/
lemma FormalDeformation.trivial_isMorAt_apply {Φ : ℕ → SymEndo R P} {n : ℕ}
    (h : (FormalDeformation.trivial R P).IsMorAt Φ n) (i : A) (x : P A) (y : P B) :
    (Φ n).app _ (SymOperad.comp (R := R) i x y)
      = ∑ q ∈ Finset.antidiagonal n,
          SymOperad.comp (R := R) i ((Φ q.1).app A x) ((Φ q.2).app B y) := by
  rw [h i x y, FormalDeformation.sum_antidiagonal_fst_zero n
    (fun a b => ∑ q ∈ Finset.antidiagonal b,
      (FormalDeformation.trivial R P).μ a i ((Φ q.1).app A x) ((Φ q.2).app B y))
    (fun a b ha => Finset.sum_eq_zero fun q _ => by simp [FormalDeformation.trivial, ha])]
  exact Finset.sum_congr rfl fun q _ => (FormalDeformation.trivial R P).μ_zero i _ _

/-- **The obstruction cochain of the trivial formal deformation**:
`∑_{a+b=n, a,b<n} Φ_a x ∘ᵢ Φ_b y`. -/
lemma FormalDeformation.trivial_obstruction_apply (Φ : ℕ → SymEndo R P) (n : ℕ) (i : A)
    (x : P A) (y : P B) :
    (FormalDeformation.trivial R P).obstruction Φ n i x y
      = ∑ q ∈ FormalDeformation.lowPairs n n,
          SymOperad.comp (R := R) i ((Φ q.1).app A x) ((Φ q.2).app B y) := by
  rw [FormalDeformation.obstruction_apply, FormalDeformation.sum_antidiagonal_fst_zero n
    (fun a b => ∑ q ∈ FormalDeformation.lowPairs n b,
      (FormalDeformation.trivial R P).μ a i ((Φ q.1).app A x) ((Φ q.2).app B y))
    (fun a b ha => Finset.sum_eq_zero fun q _ => by simp [FormalDeformation.trivial, ha])]
  exact Finset.sum_congr rfl fun q _ => (FormalDeformation.trivial R P).μ_zero i _ _

lemma FormalDeformation.gr_obstruction_trivial (Φ : ℕ → SymEndo R P) (n : ℕ) (i : A) :
    ((FormalDeformation.trivial R P).obstruction Φ n).gr (A := A) (B := B) i
      = ∑ q ∈ FormalDeformation.lowPairs n n,
          (GrOperad.comp (R := R) (P := ZeroDG R (SymGr P)) i).compl₁₂
            ((Φ q.1).toSp.app A) ((Φ q.2).toSp.app B) := by
  refine LinearMap.ext₂ fun x y => ?_
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  exact FormalDeformation.trivial_obstruction_apply Φ n i x y

/-! ## Morphisms into the truncated polynomials -/

/-- The polynomial `∑ₖ tᵏ Φₖ x`, modulo `tᴺ⁺¹`. -/
noncomputable def TruncOp.trivApp (Φ : ℕ → SymEndo R P) (N : ℕ) (A : Type) [Fintype A]
    [DecidableEq A] : ZeroDG R (SymGr P) A →ₗ[R] TruncOp R (ZeroDG R (SymGr P)) N A :=
  (TruncOp.ofCoef R (ZeroDG R (SymGr P)) N A).comp (LinearMap.pi fun k => (Φ k).toSp.app A)

lemma TruncOp.coef_trivApp (Φ : ℕ → SymEndo R P) {N k : ℕ} (hk : k ≤ N) (x : P A) :
    TruncOp.coef R (ZeroDG R (SymGr P)) N k A (TruncOp.trivApp Φ N A x) = (Φ k).app A x :=
  TruncOp.coef_ofCoef hk _

/-- **A trivialization up to order `N` of the trivial formal deformation is a morphism of operads
`P → P[t]/tᴺ⁺¹`.** -/
noncomputable def TruncOp.trivHom {N : ℕ} {Φ : ℕ → SymEndo R P}
    (hΦ : (FormalDeformation.trivial R P).PartialTriv N Φ) :
    GrOperadHom R (ZeroDG R (SymGr P)) (TruncOp R (ZeroDG R (SymGr P)) N) where
  app A _ _ := TruncOp.trivApp Φ N A
  app_par b x := TruncOp.ext fun k hk => by
    rw [TruncOp.coef_par, TruncOp.coef_trivApp Φ hk, TruncOp.coef_trivApp Φ hk]
    exact (Φ k).toSp.app_par b x
  app_map e x := TruncOp.ext fun k hk => by
    rw [TruncOp.coef_map, TruncOp.coef_trivApp Φ hk, TruncOp.coef_trivApp Φ hk]
    exact (Φ k).app_map e x
  app_one := TruncOp.ext fun k hk => by
    rw [TruncOp.coef_one hk, TruncOp.coef_trivApp Φ hk]
    split_ifs with h
    · subst h
      exact hΦ.1 Unit _
    · exact hΦ.2.1 k h
  app_comp i x y := TruncOp.ext fun k hk => by
    rw [TruncOp.coef_comp hk, TruncOp.coef_trivApp Φ hk]
    refine (FormalDeformation.trivial_isMorAt_apply (hΦ.2.2 k hk) i x y).trans
      (Finset.sum_congr rfl fun q hq => ?_)
    have hq' := Finset.mem_antidiagonal.1 hq
    rw [TruncOp.coef_trivApp Φ (by omega), TruncOp.coef_trivApp Φ (by omega)]
    rfl

end Sym

/-! ## Sums of products of invariant families -/

namespace GrOperad.Inv

variable {R : Type u} [CommRing R] {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]

/-- **The coefficient of order `N + 1` of the square of a sequence with no term of order
`N + 1`** is the sum over the pairs of orders at most `N`. -/
lemma sq_succ_eq_sum_lowPairs (x y : ℕ → Inv R Q) (N : ℕ) (hx : x (N + 1) = 0)
    (hxy : ∀ k ≤ N, x k = y k) :
    sq x (N + 1)
      = ∑ q ∈ FormalDeformation.lowPairs (N + 1) (N + 1), star R Q (y q.1) (y q.2) := by
  rw [sq_def, FormalDeformation.lowPairs, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' := Finset.mem_antidiagonal.1 hp
  split_ifs with h
  · rw [hxy _ (by omega), hxy _ (by omega)]
  · by_cases h1 : p.1 = N + 1
    · rw [h1, hx, map_zero, LinearMap.zero_apply]
    · have h2 : p.2 = N + 1 := by omega
      rw [h2, hx, map_zero]

/-- **The product of two families along a sum of composites `L₁ x ∘ L₂ y`** is the sum of the
products of the families `L₁ f` and `L₂ g`. -/
theorem sum_bilC_compl₁₂ {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C] {I : Type}
    (s : Finset I) (L₁ L₂ : I → GrSpeciesHom R Q Q) (f g : Inv R (ConvOp R C Q)) (X : Type)
    [Fintype X] [DecidableEq X] :
    ∑ T ∈ nonempties X, GrOperad.map (R := R) (splitEquiv T)
        (ConvOp.bilC none
          (∑ q ∈ s, (GrOperad.comp (R := R) (P := Q) (A := SOut T) (B := SIn T) none).compl₁₂
            ((L₁ q).app (SOut T)) ((L₂ q).app (SIn T)))
          (f.1 (SOut T)) (g.1 (SIn T)))
      = (∑ q ∈ s, star R _ (appSp (ConvOp.postSp (C := C) (L₁ q)) f)
          (appSp (ConvOp.postSp (C := C) (L₂ q)) g)).1 X := by
  rw [sum_apply]
  have h : ∀ T : Finset X, GrOperad.map (R := R) (splitEquiv T)
      (ConvOp.bilC none
        (∑ q ∈ s, (GrOperad.comp (R := R) (P := Q) (A := SOut T) (B := SIn T) none).compl₁₂
          ((L₁ q).app (SOut T)) ((L₂ q).app (SIn T)))
        (f.1 (SOut T)) (g.1 (SIn T)))
      = ∑ q ∈ s, term (R := R) (appSp (ConvOp.postSp (C := C) (L₁ q)) f).1
          (appSp (ConvOp.postSp (C := C) (L₂ q)) g).1 X T := by
    intro T
    rw [ConvOp.bilC_sum, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [ConvOp.bilC_compl₁₂, ConvOp.bilC_comp]
    rfl
  rw [Finset.sum_congr rfl fun T _ => h T, Finset.sum_comm]
  rfl

end GrOperad.Inv

/-! ## The comparison -/

namespace Koszul

open FreeGrL GrOperad.Inv

variable {R : Type u} [Field R] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (E A)] [GrSpecies R E]
  {r : ∀ n : ℕ, Set (FreeGrL R E (Fin n))}
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]
  (φ : GrOperadHom R (ZeroDG R (Pres R E r)) (ZeroDG R (SymGr P)))

/-- The values of `φ` are cycles: the differential of the target is zero. -/
lemma closedZero (A : Type) [Fintype A] [DecidableEq A] (y : Pres R E r A) :
    DGOperad.d (R := R) (φ.app A y) = 0 := rfl

/-- **The twisting morphism `φ κ : P^¡ → P`**, as a cochain. -/
noncomputable def alpha : Def R E r (ZeroDG R (SymGr P)) := (twistingOf φ (closedZero φ)).1

lemma isPar_alpha : IsPar true (alpha φ) := (twistingOf φ (closedZero φ)).2.1

lemma appDer_convD_eq_zero (x : Def R E r (ZeroDG R (SymGr P))) :
    appDer (Twisting.convD R (Dual R E r) (ZeroDG R (SymGr P))) x = 0 :=
  Subtype.ext (funext fun _ => funext fun _ => funext fun _ => ConvOp.ext fun _ => rfl)

/-- **The twisting morphism has convolution square zero.** -/
lemma star_alpha : star R _ (alpha φ) (alpha φ) = 0 := by
  have h : appDer (Twisting.convD R (Dual R E r) (ZeroDG R (SymGr P))) (alpha φ)
      + star R _ (alpha φ) (alpha φ) = 0 := (twistingOf φ (closedZero φ)).2.2.2
  exact (zero_add _).symm.trans
    ((congrArg (· + star R _ (alpha φ) (alpha φ)) (appDer_convD_eq_zero (alpha φ)).symm).trans h)

/-- **The differential of the deformation complex is the bracket with `φ κ`**, the target having
the zero differential. -/
theorem defD_apply (x : Def R E r (ZeroDG R (SymGr P))) :
    defD φ (closedZero φ) x = bracket R _ (alpha φ) x :=
  (twD_apply _ _ x).trans
    ((congrArg (· + bracket R _ (alpha φ) x) (appDer_convD_eq_zero x)).trans (zero_add _))

/-- **Composing the cochains with an equivariant family of endomorphisms of `P`.** -/
noncomputable def postEndo (ψ : SymEndo R P) :
    Def R E r (ZeroDG R (SymGr P)) →ₗ[R] Def R E r (ZeroDG R (SymGr P)) :=
  appSp (ConvOp.postSp (C := Dual R E r) ψ.toSp)

lemma postEndo_apply (ψ : SymEndo R P) (x : Def R E r (ZeroDG R (SymGr P))) {A : Type}
    [Fintype A] [DecidableEq A] (c : Dual R E r A) :
    ConvOp.toLin ((postEndo ψ x).1 A) c = ψ.app A (ConvOp.toLin (x.1 A) c) := rfl

/-- **The cochain of a two-cocycle of `P`**: `ω(φκ, φκ)`, the cochain of the square-zero
extension `Hom(P^¡, P_ω) → Hom(P^¡, P)` on `(φκ, φκ)`. -/
noncomputable def cochainOf (ω : SymCochain R P) (hω : ω.IsCocycle) :
    Def R E r (ZeroDG R (SymGr P)) :=
  haveI : Fact ω.IsCocycle := ⟨hω⟩
  (((SqZeroExt.ofCocycle ω).zeroDG).conv (Dual R E r)).res (alpha φ) (alpha φ)

/-- **The cochain of a cocycle**, in terms of the cocycle: on a finite set `X`,
`∑_{∅ ≠ T ⊆ X} ω ∘ (φκ ⊗ φκ) ∘ Δ_T`. -/
theorem cochainOf_apply (ω : SymCochain R P) (hω : ω.IsCocycle) (X : Type) [Fintype X]
    [DecidableEq X] :
    (cochainOf φ ω hω).1 X = ∑ T ∈ nonempties X, GrOperad.map (R := R) (splitEquiv T)
      (ConvOp.bilC none (ω.gr none) ((alpha φ).1 (SOut T)) ((alpha φ).1 (SIn T))) := by
  haveI : Fact ω.IsCocycle := ⟨hω⟩
  refine (((SqZeroExt.ofCocycle ω).zeroDG).res_conv_apply (Dual R E r) (alpha φ) (alpha φ)
    X).trans (Finset.sum_congr rfl fun T _ => ?_)
  rw [SqZeroExt.cochain_ofCocycle]

/-- **The cochain of a cocycle is even.** -/
theorem isPar_cochainOf (ω : SymCochain R P) (hω : ω.IsCocycle) :
    IsPar false (cochainOf φ ω hω) := by
  haveI : Fact ω.IsCocycle := ⟨hω⟩
  have h : IsPar (xor true true) (cochainOf φ ω hω) :=
    (((SqZeroExt.ofCocycle ω).zeroDG).conv (Dual R E r)).isPar_res (isPar_alpha φ)
      (isPar_alpha φ)
  exact h

/-- **Cocycles go to cocycles**: the cochain of a two-cocycle of `P` is a cocycle of the
deformation complex. -/
theorem defD_cochainOf (ω : SymCochain R P) (hω : ω.IsCocycle) :
    defD φ (closedZero φ) (cochainOf φ ω hω) = 0 := by
  haveI : Fact ω.IsCocycle := ⟨hω⟩
  rw [defD_apply]
  exact (((SqZeroExt.ofCocycle ω).zeroDG).conv (Dual R E r)).bracket_res (isPar_alpha φ)
    (star_alpha φ)

/-- **Coboundaries go to coboundaries**: the cochain of `δψ` is `-d(ψ ∘ φκ)`. -/
theorem cochainOf_coboundary (ω : SymCochain R P) (hω : ω.IsCocycle) (ψ : SymEndo R P)
    (hψ : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
      (i : A) (x : P A) (y : P B), ω i x y = ψ.coboundary i x y) :
    cochainOf φ ω hω = -defD φ (closedZero φ) (postEndo ψ (alpha φ)) := by
  haveI : Fact ω.IsCocycle := ⟨hω⟩
  rw [defD_apply]
  exact (((SqZeroExt.ofCocycle ω).zeroDG).conv (Dual R E r)).res_eq_neg_bracket
    (ConvOp.postHom (ψ.liftGr hψ)) (fun _ => ConvOp.ext fun _ => rfl) (isPar_alpha φ)
    (star_alpha φ)

/-- The cochain of the zero cocycle is zero. -/
lemma cochainOf_zero :
    cochainOf φ (SymCochain.zero : SymCochain R P) SymCochain.isCocycle_zero = 0 := by
  refine Subtype.ext (funext fun X => funext fun _ => funext fun _ => ?_)
  rw [cochainOf_apply]
  refine Finset.sum_eq_zero fun T _ => ?_
  rw [show (SymCochain.zero : SymCochain R P).gr (A := SOut T) (B := SIn T) none = 0 from rfl,
    ConvOp.bilC_zero, map_zero]

/-- **Degree one**: for a derivation `D` of `P`, the cochain `D ∘ φκ` is a cocycle of the
deformation complex. -/
theorem defD_postEndo_derivation (D : SymDerivation R P) :
    defD φ (closedZero φ) (postEndo D.toSymEndo (alpha φ)) = 0 := by
  have h := cochainOf_coboundary φ SymCochain.zero SymCochain.isCocycle_zero D.toSymEndo
    (fun i x y => by
      rw [SymEndo.coboundary_apply, SymCochain.zero_apply, D.app_comp]
      abel)
  rw [cochainOf_zero] at h
  exact neg_eq_zero.1 h.symm

/-! ## The two obstructions -/

/-- **The lift of `φ` of a trivialization of the trivial formal deformation**: the composite of
`φ` with the morphism `P → P[t]/tᴺ⁺¹`. -/
noncomputable def trivLift {N : ℕ} {Φ : ℕ → SymEndo R P}
    (hΦ : (FormalDeformation.trivial R P).PartialTriv N Φ) : Lift φ N where
  hom := (TruncOp.trivHom hΦ).comp φ
  const A _ _ y := (TruncOp.coef_trivApp Φ (Nat.zero_le N) _).trans (hΦ.1 A _)
  closed A _ _ y := TruncOp.ext fun k _ => by
    rw [TruncOp.coef_dT, map_zero]
    rfl

/-- **The coefficients of the cochain of the lift** are the cochains `Φₖ ∘ φκ`. -/
lemma trivLift_x {N : ℕ} {Φ : ℕ → SymEndo R P}
    (hΦ : (FormalDeformation.trivial R P).PartialTriv N Φ) {k : ℕ} (hk : k ≤ N) :
    (trivLift φ hΦ).x k = postEndo (Φ k) (alpha φ) :=
  Subtype.ext (funext fun _ => funext fun _ => funext fun _ => ConvOp.ext fun _ =>
    TruncOp.coef_trivApp Φ hk _)

lemma trivLift_x_succ {N : ℕ} {Φ : ℕ → SymEndo R P}
    (hΦ : (FormalDeformation.trivial R P).PartialTriv N Φ) : (trivLift φ hΦ).x (N + 1) = 0 :=
  ((trivLift φ hΦ).toLiftSeq (closedZero φ)).x_succ

/-- **The obstruction of the lift of a trivialization**: `∑_{a+b=N+1, a,b ≤ N} Φ_a φκ ⋆ Φ_b φκ`. -/
lemma obstruction_trivLift_eq_sum {N : ℕ} {Φ : ℕ → SymEndo R P}
    (hΦ : (FormalDeformation.trivial R P).PartialTriv N Φ) :
    ((trivLift φ hΦ).toLiftSeq (closedZero φ)).obstruction
      = ∑ q ∈ FormalDeformation.lowPairs (N + 1) (N + 1),
          star R _ (postEndo (Φ q.1) (alpha φ)) (postEndo (Φ q.2) (alpha φ)) := by
  show sq (trivLift φ hΦ).x (N + 1) = _
  exact sq_succ_eq_sum_lowPairs (trivLift φ hΦ).x (fun k => postEndo (Φ k) (alpha φ)) N
    (trivLift_x_succ φ hΦ) fun k hk => trivLift_x φ hΦ hk

/-- **The two obstructions agree**: the obstruction of the lift of a trivialization up to order
`N` of the trivial formal deformation is the cochain of the obstruction cocycle of the
trivialization at order `N + 1`. -/
theorem obstruction_trivLift {N : ℕ} {Φ : ℕ → SymEndo R P}
    (hΦ : (FormalDeformation.trivial R P).PartialTriv N Φ)
    (hω : ((FormalDeformation.trivial R P).obstruction Φ (N + 1)).IsCocycle) :
    ((trivLift φ hΦ).toLiftSeq (closedZero φ)).obstruction
      = cochainOf φ ((FormalDeformation.trivial R P).obstruction Φ (N + 1)) hω := by
  refine (obstruction_trivLift_eq_sum φ hΦ).trans ?_
  refine Subtype.ext (funext fun X => funext fun _ => funext fun _ => ?_)
  refine ((sum_bilC_compl₁₂ (FormalDeformation.lowPairs (N + 1) (N + 1))
    (fun q => (Φ q.1).toSp) (fun q => (Φ q.2).toSp) (alpha φ) (alpha φ) X).symm.trans ?_).trans
    (cochainOf_apply φ _ hω X).symm
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [FormalDeformation.gr_obstruction_trivial]

/-- **The obstruction of the lift of a trivialization which extends**: if the trivialization
extends to order `N + 1`, the obstruction of the lift to order `N` is `-d(Φ_{N+1} ∘ φκ)`. -/
theorem obstruction_trivLift_of_extends {N : ℕ} {Φ : ℕ → SymEndo R P}
    (hΦ : (FormalDeformation.trivial R P).PartialTriv (N + 1) Φ) :
    ((trivLift φ (N := N) (Φ := Φ)
        ⟨hΦ.1, hΦ.2.1, fun n hn => hΦ.2.2 n (Nat.le_succ_of_le hn)⟩).toLiftSeq
          (closedZero φ)).obstruction
      = -defD φ (closedZero φ) (postEndo (Φ (N + 1)) (alpha φ)) := by
  have hω : ((FormalDeformation.trivial R P).obstruction Φ (N + 1)).IsCocycle :=
    (FormalDeformation.trivial R P).isCocycle_obstruction Φ hΦ.1 hΦ.2.1 (Nat.succ_pos N)
      fun m hm => hΦ.2.2 m (Nat.le_of_lt hm)
  rw [obstruction_trivLift φ _ hω]
  exact cochainOf_coboundary φ _ hω (Φ (N + 1))
    (((FormalDeformation.trivial R P).isMorAt_iff Φ hΦ.1 (Nat.succ_pos N)).1
      (hΦ.2.2 (N + 1) le_rfl))

end Koszul

end Operad
