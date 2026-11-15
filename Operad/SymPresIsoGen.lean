/-
# Isomorphisms of graded operads, and presentations compared through their algebras

Generic tools to compare a graded presentation `Koszul.Pres K E r` (a quotient of the free graded
operad `FreeGrL K E`) with an ungraded binary quadratic operad `BinPres K r₂ r₃` (a quotient of
`FreeBin K G`), without normal forms: relators are tested on free algebras, which are faithful
(`Schur.algebra_app_injective`, `Operad.FaithfulAlgebra`).

* **Isomorphisms of graded operads** (`GrOperadIso`): morphisms both ways, inverse to each other,
  with `GrOperadIso.symm` and the arity-wise linear equivalences `GrOperadIso.linearEquiv`. For a
  graded operad `P` and a symmetric operad `Q`, morphisms `Φ : P → SymGr Q` and
  `Ψ : Q → EvenOp P` inverse to each other give `GrOperadIso.ofEven : GrOperadIso R P (SymGr Q)`
  and `GrOperadIso.evenIso : SymOperadIso R (EvenOp R P) Q`. `SymGr` is a functor
  (`SymOperadHom.toGr`), and an even graded operad maps to `SymGr` of its even part
  (`GrOperad.toEvenHom`).
* **The free operad on binary generators maps to any symmetric operad** with given values of the
  generators (`FreeBin.homOf`, `FreeBin.homOf_gen`); a monomial of arity two is a relabelling of
  its generator (`FreeBin.bin2_eq_map`).
* **Relators are killed when all algebras kill them.** A morphism `Φ' : T → SymGr Q` kills
  relators `r` as soon as every algebra over `Q`, pulled back along `Φ'`, factors through the
  quotient of `T` by `r` (`SymPresIso.kills_gr`); a morphism `Ψ' : T' → EvenOp P` into the even
  part of an even graded operad kills relators `r'` as soon as every algebra over `P` in even
  degree, pulled back along `Ψ'`, factors through the quotient of `T'` by `r'`
  (`SymPresIso.kills_sym`).
* **Generators from a binary operation.** `SymPresIso.regHom q₀ : Reg2 K → SymGr Q` sends a
  function `f` on the numberings to `∑ τ, f τ • τ · q₀` (`SymPresIso.regApp_two` in arity two),
  and `SymPresIso.binSpHom ρ q₀` is its restriction to `BinSp K K ρ`; an algebra turns them into
  the models of `Operad.SymPresBinB` (`SymPresIso.app_regApp`). In a binary quadratic operad a
  commutative generator is fixed by the transposition and an antisymmetric one is negated
  (`SymPresIso.map_swap_genQ_comm`, `SymPresIso.map_swap_genQ_antisymm`).
* **The generic isomorphism** (`SymPresIso.iso`). Generators of `Koszul.Pres K E r` are sent to
  `BinPres K r₂ r₃` by a morphism of graded linear species `F` (`SymPresIso.toBin`,
  `SymPresIso.toBin_gen`); generators of `BinPres K r₂ r₃` are sent to vectors `q g` of
  `E (Fin 2)` (`SymPresIso.ofBin`, `SymPresIso.ofBin_gen`). The hypotheses: every algebra over
  either operad restricts to an algebra over the other one along these maps, and the two maps are
  inverse to each other on the generators.

`Operad.SymPresIso` applies this to `Com`, `Lie`, `Ass` and `Pois`.
-/
import Operad.SymPresIdent
import Operad.FaithfulAlgebra
import Operad.SymIso

universe u v w w'

namespace Operad

open Sym SymPresB

/-! ## Isomorphisms of graded operads -/

/-- **An isomorphism of graded operads.** -/
structure GrOperadIso (R : Type u) [CommRing R]
    (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
    (Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q] where
  /-- The forward morphism. -/
  hom : GrOperadHom R P Q
  /-- The inverse morphism. -/
  inv : GrOperadHom R Q P
  hom_inv_id : inv.comp hom = GrOperadHom.id R P
  inv_hom_id : hom.comp inv = GrOperadHom.id R Q

section Iso

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)]

namespace GrOperadIso

variable [GrOperad R Q]

@[simp] lemma inv_hom_apply (e : GrOperadIso R P Q) (A : Type) [Fintype A] [DecidableEq A]
    (x : P A) : e.inv.app A (e.hom.app A x) = x :=
  congrArg (fun φ : GrOperadHom R P P => φ.app A x) e.hom_inv_id

@[simp] lemma hom_inv_apply (e : GrOperadIso R P Q) (A : Type) [Fintype A] [DecidableEq A]
    (y : Q A) : e.hom.app A (e.inv.app A y) = y :=
  congrArg (fun φ : GrOperadHom R Q Q => φ.app A y) e.inv_hom_id

/-- The inverse isomorphism. -/
def symm (e : GrOperadIso R P Q) : GrOperadIso R Q P :=
  ⟨e.inv, e.hom, e.inv_hom_id, e.hom_inv_id⟩

/-- **The components of an isomorphism of graded operads**, as linear equivalences. -/
def linearEquiv (e : GrOperadIso R P Q) (A : Type) [Fintype A] [DecidableEq A] :
    P A ≃ₗ[R] Q A :=
  LinearEquiv.ofLinear (e.hom.app A) (e.inv.app A) (LinearMap.ext fun y => e.hom_inv_apply A y)
    (LinearMap.ext fun x => e.inv_hom_apply A x)

@[simp] lemma linearEquiv_apply (e : GrOperadIso R P Q) (A : Type) [Fintype A] [DecidableEq A]
    (x : P A) : e.linearEquiv A x = e.hom.app A x := rfl

@[simp] lemma linearEquiv_symm_apply (e : GrOperadIso R P Q) (A : Type) [Fintype A]
    [DecidableEq A] (y : Q A) : (e.linearEquiv A).symm y = e.inv.app A y := rfl

end GrOperadIso

variable [SymOperad R Q]
  {Q' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w'}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q' A)] [SymOperad R Q']

/-- **`SymGr` is a functor**: a morphism of symmetric operads is a morphism of graded operads
between them, every operation being even. -/
def SymOperadHom.toGr (φ : SymOperadHom R Q Q') : GrOperadHom R (SymGr Q) (SymGr Q') where
  app A _ _ := φ.app A
  app_par b x := by
    cases b
    · rfl
    · show φ.app _ 0 = 0
      exact map_zero _
  app_map e x := φ.app_map e x
  app_one := φ.app_one
  app_comp i x y := φ.app_comp i x y

@[simp] lemma SymOperadHom.toGr_app (φ : SymOperadHom R Q Q') {A : Type} [Fintype A]
    [DecidableEq A] (x : Q A) : φ.toGr.app A x = φ.app A x := rfl

lemma GrOperad.val_evenEquiv_symm (h : GrOperad.IsEven R P) {A : Type} [Fintype A]
    [DecidableEq A] (x : P A) : ((GrOperad.evenEquiv h A).symm x).val = x :=
  (GrOperad.evenEquiv h A).apply_symm_apply x

/-- **An even graded operad maps to its even part**, as a morphism of graded operads into
`SymGr (EvenOp R P)`. -/
noncomputable def GrOperad.toEvenHom (h : GrOperad.IsEven R P) :
    GrOperadHom R P (SymGr (GrOperad.EvenOp R P)) where
  app A _ _ := ((GrOperad.evenEquiv h A).symm : P A →ₗ[R] GrOperad.EvenOp R P A)
  app_par b x := by
    cases b
    · show (GrOperad.evenEquiv h _).symm (GrOperad.par (R := R) false x)
        = (GrOperad.evenEquiv h _).symm x
      rw [GrOperad.par_false_of_isEven h]
    · show (GrOperad.evenEquiv h _).symm (GrOperad.par (R := R) true x) = 0
      rw [h _ x, map_zero]
  app_map e x := GrOperad.EvenOp.ext (by
    show ((GrOperad.evenEquiv h _).symm (GrOperad.map (R := R) e x)).val
      = GrOperad.map (R := R) e ((GrOperad.evenEquiv h _).symm x).val
    rw [GrOperad.val_evenEquiv_symm, GrOperad.val_evenEquiv_symm])
  app_one := GrOperad.EvenOp.ext (GrOperad.val_evenEquiv_symm h _)
  app_comp i x y := GrOperad.EvenOp.ext (by
    show ((GrOperad.evenEquiv h _).symm (GrOperad.comp (R := R) i x y)).val
      = GrOperad.comp (R := R) i ((GrOperad.evenEquiv h _).symm x).val
          ((GrOperad.evenEquiv h _).symm y).val
    rw [GrOperad.val_evenEquiv_symm, GrOperad.val_evenEquiv_symm, GrOperad.val_evenEquiv_symm])

lemma GrOperad.toEvenHom_app_val (h : GrOperad.IsEven R P) {A : Type} [Fintype A]
    [DecidableEq A] (x : GrOperad.EvenOp R P A) : (GrOperad.toEvenHom h).app A x.val = x :=
  (GrOperad.evenEquiv h A).symm_apply_apply x

/-- **An isomorphism of graded operads from morphisms inverse to each other**, one of graded
operads `P → SymGr Q` and one of symmetric operads `Q → EvenOp P`. -/
def GrOperadIso.ofEven (Φ : GrOperadHom R P (SymGr Q))
    (Ψ : SymOperadHom R Q (GrOperad.EvenOp R P))
    (h₁ : Ψ.toGrEven.comp Φ = GrOperadHom.id R P)
    (h₂ : Φ.toSymOfEven.comp Ψ = SymOperadHom.id) : GrOperadIso R P (SymGr Q) where
  hom := Φ
  inv := Ψ.toGrEven
  hom_inv_id := h₁
  inv_hom_id := GrOperadHom.ext fun A _ _ x =>
    congrArg (fun φ : SymOperadHom R Q Q => φ.app A x) h₂

/-- **The isomorphism of symmetric operads** between the even part of `P` and `Q`, from the same
data. -/
def GrOperadIso.evenIso (Φ : GrOperadHom R P (SymGr Q))
    (Ψ : SymOperadHom R Q (GrOperad.EvenOp R P))
    (h₁ : Ψ.toGrEven.comp Φ = GrOperadHom.id R P)
    (h₂ : Φ.toSymOfEven.comp Ψ = SymOperadHom.id) : SymOperadIso R (GrOperad.EvenOp R P) Q where
  hom := Φ.toSymOfEven
  inv := Ψ
  hom_inv_id := SymOperadHom.ext fun A _ _ x => GrOperad.EvenOp.ext
    (congrArg (fun φ : GrOperadHom R P P => φ.app A x.val) h₁)
  inv_hom_id := h₂

end Iso

/-! ## The free operad on binary generators, into any symmetric operad -/

namespace FreeBin

variable {R : Type u} [CommRing R] {G : Type w}
  {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (S A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (S A)] [SymOperad R S]

/-- The generator values given by binary operations of a symmetric operad. -/
def opVal (q : G → S (Fin 2)) : ∀ n, BinGen G n → Und R S (Fin n)
  | _, .op g => Und.of R S (q g)

/-- **The morphism out of the free operad on binary generators** with given values of the
generators. -/
noncomputable def homOf (q : G → S (Fin 2)) : SymOperadHom R (FreeBin R G) S :=
  linHomEquiv R (FreeSet.homEquiv.symm (opVal q))

lemma homOf_gen (q : G → S (Fin 2)) (g : G) :
    (homOf (R := R) q).app (Fin 2) (Finsupp.single (Pres.mk (gen g)) 1) = q g := by
  show Finsupp.lift (S (Fin 2)) R (FreeSet (BinGen G) (Fin 2)) _
    (Finsupp.single (Pres.mk (gen g)) 1) = _
  simp
  rfl

/-- A monomial of arity two is a relabelling of its generator. -/
lemma bin2_eq_map (g : G) (σ : Equiv.Perm (Fin 2)) :
    bin2 (R := R) g σ = SymOperad.map (R := R) σ (Finsupp.single (Pres.mk (gen g)) 1) := by
  show _ = Lin.mapL R σ (Finsupp.single _ 1)
  rw [Lin.mapL_single, Pres.map_mk]
  rfl

lemma bin2_one (g : G) : bin2 (R := R) g 1 = Finsupp.single (Pres.mk (gen g)) 1 :=
  (bin2_eq_map g 1).trans (SymOperad.map_refl _)

end FreeBin

namespace SymPresIso

/-! ## Relators killed by all algebras -/

section Kills

variable {K : Type u} [CommRing K]

/-- **A morphism into `SymGr Q` kills relators which every algebra over `Q` kills**: if every
algebra over `Q`, pulled back along `Φ'`, factors through the quotient by `r`, then `Φ'` kills
`r`. The free algebras over `Q` are faithful. -/
theorem kills_gr {T : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (T A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (T A)] [GrOperad K T]
    (r : ∀ n : ℕ, Set (T (Fin n)))
    {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (Q A)] [SymOperad K Q]
    (Φ' : GrOperadHom K T (SymGr Q))
    (h : ∀ (V : Type (max u w)) [AddCommGroup V] [Module K V] (α : SymAlgebra K Q V),
      ∃ δ : GrOperadHom K (GrOperadIdeal.span K r).Quot (SymGr (EndOp K V)),
        δ.comp (GrOperadIdeal.span K r).projHom = α.toGr.comp Φ') :
    ∀ n, ∀ x ∈ r n, Φ'.app (Fin n) x = 0 := by
  intro n x hx
  obtain ⟨δ, hδ⟩ := h _ (Schur.algebra K Q (Fin n → K))
  have h1 := congrArg (fun φ : GrOperadHom K T (SymGr (EndOp K (Schur K Q (Fin n → K)))) =>
    φ.app (Fin n) x) hδ
  have h2 : (GrOperadIdeal.span K r).proj (Fin n) x = 0 :=
    ((GrOperadIdeal.span K r).proj_eq_zero_iff x).2 (GrOperadIdeal.subset_span n hx)
  have h3 : (Schur.algebra K Q (Fin n → K)).app (Fin n) (Φ'.app (Fin n) x) = 0 :=
    h1.symm.trans ((congrArg (δ.app (Fin n)) h2).trans (map_zero _))
  exact Schur.algebra_app_injective K Q n (h3.trans (map_zero _).symm)

/-- **A morphism into the even part of an even graded operad `P` kills relators which every
algebra over `P` kills**: if every algebra over `P` in even degree, pulled back along `Ψ'`,
factors through the quotient by `r'`, then `Ψ'` kills `r'`. The free algebras over the even part
of `P` are faithful. -/
theorem kills_sym {T : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (T A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (T A)] [SymOperad K T]
    (r' : ∀ n : ℕ, Set (T (Fin n)))
    {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (P A)] [GrOperad K P]
    (hP : GrOperad.IsEven K P) (Ψ' : SymOperadHom K T (GrOperad.EvenOp K P))
    (h : ∀ (V : Type (max u w)) [AddCommGroup V] [Module K V]
      (δ : GrOperadHom K P (SymGr (EndOp K V))),
      ∃ γ : SymAlgebra K (SymOperadIdeal.span K r').Quot V,
        γ.comp (SymOperadIdeal.span K r').projHom = δ.toSymOfEven.comp Ψ') :
    ∀ n, ∀ y ∈ r' n, Ψ'.app (Fin n) y = 0 := by
  intro n y hy
  obtain ⟨γ, hγ⟩ := h _ ((Schur.algebra K (GrOperad.EvenOp K P) (Fin n → K)).toGr.comp
    (GrOperad.toEvenHom hP))
  have h1 := congrArg (fun φ : SymOperadHom K T
    (EndOp K (Schur K (GrOperad.EvenOp K P) (Fin n → K))) => φ.app (Fin n) y) hγ
  have h2 : (SymOperadIdeal.span K r').proj (Fin n) y = 0 :=
    ((SymOperadIdeal.span K r').proj_eq_zero_iff y).2 (SymOperadIdeal.subset_span n hy)
  have h3 : (Schur.algebra K (GrOperad.EvenOp K P) (Fin n → K)).app (Fin n)
      (Ψ'.app (Fin n) y) = 0 :=
    (congrArg ((Schur.algebra K (GrOperad.EvenOp K P) (Fin n → K)).app (Fin n))
      (GrOperad.toEvenHom_app_val hP (Ψ'.app (Fin n) y)).symm).trans
      (h1.symm.trans ((congrArg (γ.app (Fin n)) h2).trans (map_zero _)))
  exact Schur.algebra_app_injective K (GrOperad.EvenOp K P) n (h3.trans (map_zero _).symm)

end Kills

/-! ## Generators from a binary operation -/

section RegHom

variable {K : Type u} [CommRing K]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (Q A)] [SymOperad K Q]

/-- **The map of a binary operation** `q₀` on `A`: a function on the numberings `τ` to the sum of
the relabellings of `q₀` along `τ`. -/
noncomputable def regApp (q₀ : Q (Fin 2)) (A : Type) [Fintype A] [DecidableEq A] :
    Reg2 K A →ₗ[K] SymGr Q A where
  toFun f := ∑ τ : Fin 2 ≃ A, f.val τ • SymOperad.map (R := K) τ q₀
  map_add' f g := by
    simp only [Reg2.val_add, add_smul]
    exact Finset.sum_add_distrib
  map_smul' a f := by
    simp only [Reg2.val_smul, mul_smul, RingHom.id_apply, Finset.smul_sum]
    rfl

lemma regApp_apply (q₀ : Q (Fin 2)) {A : Type} [Fintype A] [DecidableEq A] (f : Reg2 K A) :
    regApp q₀ A f = ∑ τ : Fin 2 ≃ A, f.val τ • SymOperad.map (R := K) τ q₀ := rfl

/-- The map of a binary operation in arity two. -/
lemma regApp_two (q₀ : Q (Fin 2)) (f : Reg2 K (Fin 2)) :
    regApp q₀ (Fin 2) f = f.val (Equiv.refl _) • q₀
      + f.val (Equiv.swap 0 1) • SymOperad.map (R := K) (Equiv.swap (0 : Fin 2) 1) q₀ := by
  rw [regApp_apply, univ_perm_two, Finset.sum_pair (by decide), SymOperad.map_refl]

/-- **The morphism of graded linear species `Reg2 K → SymGr Q` of a binary operation.** -/
noncomputable def regHom (q₀ : Q (Fin 2)) : GrSpeciesHom K (Reg2 K) (SymGr Q) where
  app := regApp q₀
  app_map {A B} _ _ _ _ e f := by
    show ∑ τ : Fin 2 ≃ B, (SymSpecies.map (R := K) e f).val τ • SymOperad.map (R := K) τ q₀
      = SymOperad.map (R := K) e (∑ τ : Fin 2 ≃ A, f.val τ • SymOperad.map (R := K) τ q₀)
    rw [map_sum]
    let e' : (Fin 2 ≃ B) ≃ (Fin 2 ≃ A) :=
      ⟨fun τ => τ.trans e.symm, fun τ => τ.trans e, fun τ => by ext; simp, fun τ => by ext; simp⟩
    refine Fintype.sum_equiv e' _ _ fun τ => ?_
    rw [map_smul, ← SymOperad.map_trans]
    show f.val (τ.trans e.symm) • _ = f.val (τ.trans e.symm) • _
    refine congrArg _ (congrArg (fun σ : Fin 2 ≃ B => SymOperad.map (R := K) σ q₀) ?_)
    exact Equiv.ext fun x => (e.apply_symm_apply (τ x)).symm
  app_par b f := by
    cases b
    · rfl
    · show regApp q₀ _ (Reg2.par K true f) = 0
      simp [Reg2.par]

variable {V : Type v} [AddCommGroup V] [Module K V]

/-- **An algebra turns the map of a binary operation into the model** of its bilinear map. -/
lemma app_regApp (α : SymAlgebra K Q V) (q₀ : Q (Fin 2)) {A : Type} [Fintype A] [DecidableEq A]
    (f : Reg2 K A) :
    α.app A (regApp q₀ A f) = modelApp (SymPresIdent.bil (α.app (Fin 2) q₀)) A f := by
  rw [regApp_apply, map_sum]
  show _ = ∑ τ : Fin 2 ≃ A, f.val τ • EndOp.mapL K V τ
    (FreeBin.bilinOp (SymPresIdent.bil (α.app (Fin 2) q₀)))
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_smul, α.app_map, SymPresIdent.bilinOp_bil]
  rfl

lemma bil_add (F F' : EndOp K V (Fin 2)) :
    SymPresIdent.bil (F + F') = SymPresIdent.bil F + SymPresIdent.bil F' := rfl

lemma bil_smul (a : K) (F : EndOp K V (Fin 2)) :
    SymPresIdent.bil (a • F) = a • SymPresIdent.bil F := rfl

end RegHom

section BinSpHom

variable {K : Type u} [Field K]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (Q A)] [SymOperad K Q]

/-- **The morphism of graded linear species `BinSp K K ρ → SymGr Q` of a binary operation**, the
restriction of `regHom`. -/
noncomputable def binSpHom (ρ : K →ₗ[K] K) (q₀ : Q (Fin 2)) :
    GrSpeciesHom K (BinSp K K ρ) (SymGr Q) where
  app A _ _ := regApp q₀ A ∘ₗ SymPresIdent.toReg2 A
  app_map e f := (regHom q₀).app_map e (SymPresIdent.toReg2 _ f)
  app_par b f := by
    cases b
    · rfl
    · show regApp q₀ _ (SymPresIdent.toReg2 _ (BinSp.parL true f)) = 0
      simp [BinSp.parL]

lemma binSpHom_app (ρ : K →ₗ[K] K) (q₀ : Q (Fin 2)) {A : Type} [Fintype A] [DecidableEq A]
    (f : BinSp K K ρ A) :
    (binSpHom ρ q₀).app A f = regApp q₀ A (SymPresIdent.toReg2 A f) := rfl

lemma isEven_binSp (ρ : K →ₗ[K] K) : GrSpecies.IsEven K (BinSp K K ρ) := fun _ _ _ _ => rfl

lemma isEven_reg2 : GrSpecies.IsEven K (Reg2 K) := fun _ _ _ _ => rfl

end BinSpHom

/-! ## The generic isomorphism -/

section Generic

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  (r : ∀ n : ℕ, Set (FreeGrL K E (Fin n)))
  {G' : Type} (r₂ : Set (FreeBin K G' (Fin 2))) (r₃ : Set (FreeBin K G' (Fin 3)))

/-- **The class of a generator** in the presented graded operad. -/
noncomputable def genP {A : Type} [Fintype A] [DecidableEq A] (v : E A) : Koszul.Pres K E r A :=
  (GrOperadIdeal.span K r).proj A ((FreeGrL.ι K E).app A v)

/-- **The class of a generator** in the binary quadratic operad. -/
noncomputable def genQ (g : G') : BinPres K r₂ r₃ (Fin 2) :=
  (SymOperadIdeal.span K (rel23 r₂ r₃)).proj (Fin 2) (Finsupp.single (Pres.mk (FreeBin.gen g)) 1)

lemma genP_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    (v : E A) : genP r (SymSpecies.map (R := K) e v) = GrOperad.map (R := K) e (genP r v) :=
  congrArg ((GrOperadIdeal.span K r).proj B) ((FreeGrL.ι K E).app_map e v)

variable {r₂ r₃}

/-- **A commutative generator is fixed by the transposition.** -/
lemma map_swap_genQ_comm {g : G'} (h : BinRel.comm K g ∈ r₂) :
    SymOperad.map (R := K) (Equiv.swap (0 : Fin 2) 1) (genQ r₂ r₃ g) = genQ r₂ r₃ g := by
  have h0 : (SymOperadIdeal.span K (rel23 r₂ r₃)).proj (Fin 2) (BinRel.comm K g) = 0 :=
    ((SymOperadIdeal.span K (rel23 r₂ r₃)).proj_eq_zero_iff _).2
      (SymOperadIdeal.subset_span (r := rel23 r₂ r₃) 2 h)
  rw [BinRel.comm, map_sub, sub_eq_zero, FreeBin.bin2_one, FreeBin.bin2_eq_map] at h0
  exact h0.symm

/-- **An antisymmetric generator is negated by the transposition.** -/
lemma map_swap_genQ_antisymm {g : G'} (h : BinRel.antisymm K g ∈ r₂) :
    SymOperad.map (R := K) (Equiv.swap (0 : Fin 2) 1) (genQ r₂ r₃ g) = -genQ r₂ r₃ g := by
  have h0 : (SymOperadIdeal.span K (rel23 r₂ r₃)).proj (Fin 2) (BinRel.antisymm K g) = 0 :=
    ((SymOperadIdeal.span K (rel23 r₂ r₃)).proj_eq_zero_iff _).2
      (SymOperadIdeal.subset_span (r := rel23 r₂ r₃) 2 h)
  rw [BinRel.antisymm, map_add, FreeBin.bin2_one, FreeBin.bin2_eq_map] at h0
  exact (eq_neg_of_add_eq_zero_right h0)

variable {r}

/-- **The generator map kills the relators** of the graded presentation, when every algebra over
the binary quadratic operad restricts along it to an algebra over the graded presentation. -/
theorem kills_toBin (F : GrSpeciesHom K E (SymGr (BinPres K r₂ r₃)))
    (hF : ∀ (V : Type (max u 1)) [AddCommGroup V] [Module K V]
      (α : SymAlgebra K (BinPres K r₂ r₃) V), ∃ δ : SymPresIdent.PresAlg K E r V,
        ∀ (A : Type) [Fintype A] [DecidableEq A] (v : E A),
          δ.app A (genP r v) = α.app A (F.app A v)) :
    SymPresIdent.Kills r (FreeGrL.homEquiv.symm F) :=
  kills_gr r _ fun V _ _ α => by
    obtain ⟨δ, hδ⟩ := hF V α
    exact ⟨δ, FreeGrL.hom_ext fun A _ _ v =>
      (hδ A v).trans (congrArg (α.app A) (FreeGrL.homEquiv_symm_ι F v).symm)⟩

/-- **The morphism from the graded presentation to the binary quadratic operad** extending a
morphism of graded linear species on the generators. -/
noncomputable def toBin (F : GrSpeciesHom K E (SymGr (BinPres K r₂ r₃)))
    (hF : ∀ (V : Type (max u 1)) [AddCommGroup V] [Module K V]
      (α : SymAlgebra K (BinPres K r₂ r₃) V), ∃ δ : SymPresIdent.PresAlg K E r V,
        ∀ (A : Type) [Fintype A] [DecidableEq A] (v : E A),
          δ.app A (genP r v) = α.app A (F.app A v)) :
    GrOperadHom K (Koszul.Pres K E r) (SymGr (BinPres K r₂ r₃)) :=
  GrOperadIdeal.presHomEquiv.symm ⟨FreeGrL.homEquiv.symm F, kills_toBin F hF⟩

lemma toBin_gen (F : GrSpeciesHom K E (SymGr (BinPres K r₂ r₃)))
    (hF : ∀ (V : Type (max u 1)) [AddCommGroup V] [Module K V]
      (α : SymAlgebra K (BinPres K r₂ r₃) V), ∃ δ : SymPresIdent.PresAlg K E r V,
        ∀ (A : Type) [Fintype A] [DecidableEq A] (v : E A),
          δ.app A (genP r v) = α.app A (F.app A v))
    {A : Type} [Fintype A] [DecidableEq A] (v : E A) :
    (toBin F hF).app A (genP r v) = F.app A v :=
  FreeGrL.homEquiv_symm_ι F v

variable (r) (hE : GrSpecies.IsEven K E)

/-- The values of the binary generators in the even part of the graded presentation. -/
noncomputable def evGen (q : G' → E (Fin 2)) (g : G') :
    GrOperad.EvenOp K (Koszul.Pres K E r) (Fin 2) :=
  (GrOperad.evenEquiv (Koszul.isEven_pres r hE) (Fin 2)).symm (genP r (q g))

lemma evGen_val (q : G' → E (Fin 2)) (g : G') : (evGen r hE q g).val = genP r (q g) :=
  GrOperad.val_evenEquiv_symm _ _

variable {r}

/-- **The generator values kill the relators** of the binary quadratic operad, when every
algebra over the graded presentation restricts along them to an algebra over the binary
quadratic operad. -/
theorem kills_ofBin (q : G' → E (Fin 2))
    (hq : ∀ (V : Type u) [AddCommGroup V] [Module K V] (δ : SymPresIdent.PresAlg K E r V),
      ∃ γ : SymAlgebra K (BinPres K r₂ r₃) V,
        ∀ g, γ.app (Fin 2) (genQ r₂ r₃ g) = δ.app (Fin 2) (genP r (q g))) :
    ∀ n, ∀ y ∈ rel23 r₂ r₃ n, (FreeBin.homOf (evGen r hE q)).app (Fin n) y = 0 :=
  kills_sym (rel23 r₂ r₃) (Koszul.isEven_pres r hE) _ fun V _ _ δ => by
    obtain ⟨γ, hγ⟩ := hq V δ
    refine ⟨γ, Pres.lin_hom_ext fun n g => ?_⟩
    cases g with
    | op g =>
      show γ.app _ (genQ r₂ r₃ g) = δ.app _ ((FreeBin.homOf (evGen r hE q)).app _
        (Finsupp.single (Pres.mk (FreeBin.gen g)) 1)).val
      rw [FreeBin.homOf_gen, evGen_val]
      exact hγ g

/-- **The morphism from the binary quadratic operad to the even part of the graded
presentation** with given values of the generators. -/
noncomputable def ofBin (q : G' → E (Fin 2))
    (hq : ∀ (V : Type u) [AddCommGroup V] [Module K V] (δ : SymPresIdent.PresAlg K E r V),
      ∃ γ : SymAlgebra K (BinPres K r₂ r₃) V,
        ∀ g, γ.app (Fin 2) (genQ r₂ r₃ g) = δ.app (Fin 2) (genP r (q g))) :
    SymOperadHom K (BinPres K r₂ r₃) (GrOperad.EvenOp K (Koszul.Pres K E r)) :=
  SymOperadIdeal.presHomEquiv.symm ⟨FreeBin.homOf (evGen r hE q), kills_ofBin hE q hq⟩

lemma ofBin_gen (q : G' → E (Fin 2))
    (hq : ∀ (V : Type u) [AddCommGroup V] [Module K V] (δ : SymPresIdent.PresAlg K E r V),
      ∃ γ : SymAlgebra K (BinPres K r₂ r₃) V,
        ∀ g, γ.app (Fin 2) (genQ r₂ r₃ g) = δ.app (Fin 2) (genP r (q g))) (g : G') :
    ((ofBin hE q hq).app (Fin 2) (genQ r₂ r₃ g)).val = genP r (q g) := by
  show ((FreeBin.homOf (evGen r hE q)).app (Fin 2) _).val = _
  rw [FreeBin.homOf_gen, evGen_val]

/-- **The isomorphism of graded operads between a graded presentation and a binary quadratic
operad**: generator maps both ways along which the algebras of either operad restrict to
algebras of the other, and which are inverse to each other on the generators. -/
noncomputable def iso {G : Type} (c : ∀ k, Module.Basis (BinGen G k) K (E (Fin k)))
    (F : GrSpeciesHom K E (SymGr (BinPres K r₂ r₃)))
    (hF : ∀ (V : Type (max u 1)) [AddCommGroup V] [Module K V]
      (α : SymAlgebra K (BinPres K r₂ r₃) V), ∃ δ : SymPresIdent.PresAlg K E r V,
        ∀ (A : Type) [Fintype A] [DecidableEq A] (v : E A),
          δ.app A (genP r v) = α.app A (F.app A v))
    (q : G' → E (Fin 2))
    (hq : ∀ (V : Type u) [AddCommGroup V] [Module K V] (δ : SymPresIdent.PresAlg K E r V),
      ∃ γ : SymAlgebra K (BinPres K r₂ r₃) V,
        ∀ g, γ.app (Fin 2) (genQ r₂ r₃ g) = δ.app (Fin 2) (genP r (q g)))
    (h₁ : ∀ g, F.app (Fin 2) (q g) = genQ r₂ r₃ g)
    (h₂ : ∀ g : G, ((ofBin hE q hq).app (Fin 2) (F.app (Fin 2) (c 2 (.op g)))).val
      = genP r (c 2 (.op g))) :
    GrOperadIso K (Koszul.Pres K E r) (SymGr (BinPres K r₂ r₃)) :=
  GrOperadIso.ofEven (toBin F hF) (ofBin hE q hq)
    (GrOperadIdeal.presHomEquiv.injective (Subtype.ext (SymPresIdent.hom_ext_basis c fun g => by
      show ((ofBin hE q hq).app (Fin 2) ((toBin F hF).app (Fin 2) (genP r (c 2 (.op g))))).val
        = genP r (c 2 (.op g))
      rw [toBin_gen]
      exact h₂ g)))
    (presLin_hom_ext fun n g => by
      cases g with
      | op g =>
        show (toBin F hF).app (Fin 2) ((ofBin hE q hq).app (Fin 2) (genQ r₂ r₃ g)).val
          = genQ r₂ r₃ g
        rw [ofBin_gen, toBin_gen]
        exact h₁ g)

end Generic

end SymPresIso

end Operad
