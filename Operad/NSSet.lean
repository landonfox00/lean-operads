/-
# Non-symmetric set operads, and linearization

The planar counterpart of `Operad.SetOperad`: a non-symmetric operad in sets, in the positional
arity convention of `Operad.Basic` (`comp a b : S (a+1+b) → S n → S (a+n+b)`), with reindexing
along equalities of arities (`reindexS`) in place of `reindex`. Its linearization `LinNS R S`,
`n ↦ S n →₀ R`, is a non-symmetric operad in `R`-modules (`instNSOperadLinNS`).

A symmetric set operad has an underlying non-symmetric one on the standard finite types
(`SetOperad.toNSSet`); its axioms are those of `SymOperad.toNS` on the linearization, transported
back along the injectivity of `Finsupp.single`.
-/
import Operad.SetOperad
import Operad.SymNS

universe u v w

namespace Operad

/-! ## Reindexing -/

section ReindexS

variable (S : ℕ → Type v)

/-- Transport along an equality of arities. -/
def reindexS {m n : ℕ} (h : m = n) : S m → S n := fun x => h ▸ x

variable {S}

@[simp] lemma reindexS_self {n : ℕ} (h : n = n) (x : S n) : reindexS S h x = x := rfl

@[simp] lemma reindexS_reindexS {l m n : ℕ} (h₁ : l = m) (h₂ : m = n) (x : S l) :
    reindexS S h₂ (reindexS S h₁ x) = reindexS S (h₁.trans h₂) x := by
  subst h₁; subst h₂; rfl

lemma reindexS_injective {m n : ℕ} (h : m = n) : Function.Injective (reindexS S h) := by
  subst h; exact fun _ _ h => h

lemma reindexS_symm_eq {m n : ℕ} (h : m = n) (x : S m) (y : S n) :
    reindexS S h x = y ↔ x = reindexS S h.symm y := by
  subst h; exact Iff.rfl

end ReindexS

/-- **A non-symmetric set operad**, in the positional arity convention. The axioms are those of
`NSOperad`, for functions. -/
class NSSetOperad (S : ℕ → Type v) where
  /-- The identity operation. -/
  one : S 1
  /-- Insert an arity-`n` operation into the slot with `a` inputs before it and `b` after. -/
  comp (a b : ℕ) {n : ℕ} : S (a + 1 + b) → S n → S (a + n + b)
  comp_one_right (a b : ℕ) (α : S (a + 1 + b)) : comp a b α one = α
  comp_one_left {n : ℕ} (α : S n) : reindexS S (by omega) (comp 0 0 one α) = α
  comp_assoc_seq (a b c d : ℕ) {p : ℕ} (α : S (a + 1 + b)) (β : S (c + 1 + d)) (γ : S p) :
    reindexS S (by omega)
        (comp (a + c) (d + b) (reindexS S (by omega) (comp a b α β)) γ)
      = comp a b α (comp c d β γ)
  comp_assoc_par (a b c : ℕ) {n p : ℕ} (α : S (a + 1 + b + 1 + c)) (β : S n) (γ : S p) :
    reindexS S (by omega)
        (comp (a + n + b) c
          (reindexS S (by omega) (comp a (b + 1 + c) (reindexS S (by omega) α) β)) γ)
      = comp a (b + p + c) (reindexS S (by omega) (comp (a + 1 + b) c α γ)) β

/-- **A morphism of non-symmetric set operads.** -/
structure NSSetOperadHom (S : ℕ → Type v) (T : ℕ → Type w) [NSSetOperad S] [NSSetOperad T] where
  /-- The component at an arity. -/
  app (n : ℕ) : S n → T n
  app_one : app 1 NSSetOperad.one = NSSetOperad.one
  app_comp (a b : ℕ) {n : ℕ} (α : S (a + 1 + b)) (β : S n) :
    app (a + n + b) (NSSetOperad.comp a b α β) = NSSetOperad.comp a b (app _ α) (app n β)

namespace NSSetOperadHom

variable {S : ℕ → Type v} {T : ℕ → Type w} [NSSetOperad S] [NSSetOperad T]

@[ext] lemma ext {φ ψ : NSSetOperadHom S T} (h : ∀ n (x : S n), φ.app n x = ψ.app n x) :
    φ = ψ := by
  obtain ⟨φa, _, _⟩ := φ
  obtain ⟨ψa, _, _⟩ := ψ
  have : φa = ψa := funext fun n => funext (h n)
  subst this
  rfl

/-- Components commute with reindexing. -/
lemma app_reindexS (φ : NSSetOperadHom S T) {m n : ℕ} (h : m = n) (x : S m) :
    φ.app n (reindexS S h x) = reindexS T h (φ.app m x) := by
  subst h; rfl

/-- The identity morphism. -/
def id : NSSetOperadHom S S where
  app _ x := x
  app_one := rfl
  app_comp := by intros; rfl

variable {U : ℕ → Type*} [NSSetOperad U]

/-- The composite of two morphisms. -/
def comp (ψ : NSSetOperadHom T U) (φ : NSSetOperadHom S T) : NSSetOperadHom S U where
  app n x := ψ.app n (φ.app n x)
  app_one := by rw [φ.app_one, ψ.app_one]
  app_comp := by
    intro a b n α β
    show ψ.app _ (φ.app _ _) = _
    rw [φ.app_comp, ψ.app_comp]

end NSSetOperadHom

/-- **An isomorphism of non-symmetric set operads.** -/
structure NSSetOperadIso (S : ℕ → Type v) (T : ℕ → Type w) [NSSetOperad S] [NSSetOperad T] where
  /-- The forward morphism. -/
  hom : NSSetOperadHom S T
  /-- The inverse morphism. -/
  inv : NSSetOperadHom T S
  hom_inv_id : inv.comp hom = NSSetOperadHom.id
  inv_hom_id : hom.comp inv = NSSetOperadHom.id

/-! ## Linearization -/

/-- **The linearization of a non-symmetric set operad.** -/
abbrev LinNS (R : Type u) [CommRing R] (S : ℕ → Type v) : ℕ → Type (max u v) :=
  fun n => S n →₀ R

namespace LinNS

variable (R : Type u) [CommRing R] {S : ℕ → Type v} [NSSetOperad S]

/-- Composition, extended bilinearly. -/
noncomputable def compL (a b : ℕ) {n : ℕ} :
    (S (a + 1 + b) →₀ R) →ₗ[R] (S n →₀ R) →ₗ[R] (S (a + n + b) →₀ R) :=
  Finsupp.lift ((S n →₀ R) →ₗ[R] (S (a + n + b) →₀ R)) R (S (a + 1 + b))
    (fun s => Finsupp.lmapDomain R R (NSSetOperad.comp a b s))

variable {R}

@[simp] lemma compL_single (a b : ℕ) {n : ℕ} (s : S (a + 1 + b)) (t : S n) (r r' : R) :
    compL R a b (Finsupp.single s r) (Finsupp.single t r')
      = Finsupp.single (NSSetOperad.comp a b s t) (r * r') := by
  simp [compL, Finsupp.mapDomain_single, Finsupp.smul_single, smul_eq_mul]

omit [NSSetOperad S] in
@[simp] lemma reindex_single {m n : ℕ} (h : m = n) (s : S m) (r : R) :
    reindex R (LinNS R S) h (Finsupp.single s r) = Finsupp.single (reindexS S h s) r := by
  subst h; rfl

end LinNS

/-- **The linearization of a non-symmetric set operad is a non-symmetric operad in `R`-modules.** -/
noncomputable instance instNSOperadLinNS (R : Type u) [CommRing R] (S : ℕ → Type v)
    [NSSetOperad S] : NSOperad R (LinNS R S) where
  one := Finsupp.single NSSetOperad.one 1
  comp a b := LinNS.compL R a b
  comp_one_right a b x := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | single s r => rw [LinNS.compL_single, NSSetOperad.comp_one_right, mul_one]
  comp_one_left x := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, hx, hx']
    | single s r => rw [LinNS.compL_single, LinNS.reindex_single, NSSetOperad.comp_one_left, one_mul]
  comp_assoc_seq a b c d p x y z := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | single s r =>
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
      | single t r' =>
        induction z using Finsupp.induction_linear with
        | zero => simp
        | add z z' hz hz' => simp only [map_add, hz, hz']
        | single w r'' =>
          simp only [LinNS.compL_single, LinNS.reindex_single, NSSetOperad.comp_assoc_seq,
            mul_assoc]
  comp_assoc_par a b c n p x y z := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | single s r =>
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
      | single t r' =>
        induction z using Finsupp.induction_linear with
        | zero => simp
        | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz']
        | single w r'' =>
          simp only [LinNS.compL_single, LinNS.reindex_single, NSSetOperad.comp_assoc_par]
          congr 1
          ring

/-! ## The underlying non-symmetric set operad of a symmetric one -/

namespace SetOperad

open Sym

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]

/-- **The underlying non-symmetric collection**: the components on the standard finite types. -/
def toNSSet (S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v) : ℕ → Type v :=
  fun n => S (Fin n)

/-- Positional composition: compose at the input `a`, then list the inputs in order. -/
def nsCompSet (a b : ℕ) {n : ℕ} (x : S (Fin (a + 1 + b))) (y : S (Fin n)) :
    S (Fin (a + n + b)) :=
  map (insertEquiv a b n) (comp (⟨a, by omega⟩ : Fin (a + 1 + b)) x y)

/-- The unit, on the one-element `Fin`. -/
def nsOneSet : S (Fin 1) := map unitFinOne one

/-! The axioms are transported from the linearization over `ℤ`, where `Operad.SymNS` proves
them, along the injectivity of `Finsupp.single`. -/

lemma single_nsCompSet (a b : ℕ) {n : ℕ} (x : toNSSet S (a + 1 + b)) (y : toNSSet S n) :
    (Finsupp.single (α := S (Fin (a + n + b))) (nsCompSet a b x y) (1 : ℤ))
      = SymOperad.nsComp (R := ℤ) (P := Lin ℤ S) a b (Finsupp.single (α := S (Fin _)) x 1)
          (Finsupp.single (α := S (Fin n)) y 1) := by
  rw [SymOperad.nsComp_apply]
  show _ = Lin.mapL ℤ _ (Lin.compL ℤ _ _ _)
  rw [Lin.compL_single, Lin.mapL_single, mul_one]
  rfl

lemma single_nsOneSet :
    (Finsupp.single (α := S (Fin 1)) (nsOneSet (S := S)) (1 : ℤ))
      = SymOperad.nsOne (R := ℤ) (P := Lin ℤ S) := by
  show _ = Lin.mapL ℤ _ (Finsupp.single one 1)
  rw [Lin.mapL_single]
  rfl

omit [SetOperad S] in
lemma single_reindexS {m n : ℕ} (h : m = n) (x : toNSSet S m) :
    (Finsupp.single (α := S (Fin n)) (reindexS (toNSSet S) h x) (1 : ℤ))
      = reindex ℤ (SymOperad.toNS (Lin ℤ S)) h (Finsupp.single (α := S (Fin m)) x 1) := by
  subst h
  rfl

omit [SetOperad S] in
private lemma single_inj {n : ℕ} {x y : toNSSet S n}
    (h : (Finsupp.single (α := S (Fin n)) x (1 : ℤ)) = Finsupp.single (α := S (Fin n)) y 1) :
    x = y :=
  Finsupp.single_left_injective one_ne_zero h

/-- **The underlying non-symmetric set operad.** -/
instance instNSSetOperadToNSSet : NSSetOperad (toNSSet S) where
  one := nsOneSet
  comp a b _ x y := nsCompSet a b x y
  comp_one_right a b x := single_inj (by
    rw [single_nsCompSet, single_nsOneSet]
    exact SymOperad.nsComp_one_right a b _)
  comp_one_left x := single_inj (by
    rw [single_reindexS, single_nsCompSet, single_nsOneSet]
    exact SymOperad.nsComp_one_left _)
  comp_assoc_seq a b c d p x y z := single_inj (by
    rw [single_reindexS, single_nsCompSet, single_reindexS, single_nsCompSet, single_nsCompSet,
      single_nsCompSet]
    exact SymOperad.nsComp_assoc_seq a b c d _ _ _)
  comp_assoc_par a b c n p x y z := single_inj (by
    rw [single_reindexS, single_nsCompSet, single_reindexS, single_nsCompSet, single_reindexS,
      single_nsCompSet, single_reindexS, single_nsCompSet]
    exact SymOperad.nsComp_assoc_par a b c _ _ _)

@[simp] lemma toNSSet_comp (a b : ℕ) {n : ℕ} (x : toNSSet S (a + 1 + b)) (y : toNSSet S n) :
    NSSetOperad.comp a b x y = nsCompSet (S := S) a b x y := rfl

@[simp] lemma toNSSet_one : (NSSetOperad.one : toNSSet S 1) = nsOneSet (S := S) := rfl

end SetOperad

end Operad
