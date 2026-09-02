/-
# Ideals and quotients of non-symmetric operads

An operad presented by generators and relations is a free operad modulo the ideal the relations
generate, so quotients are the missing step between `Operad.Free` and any concrete presentation.

An ideal is a submodule in each arity absorbing composition from either side. Because `comp` is
linear in each argument separately, the induced composition on the quotient is built by
descending one argument at a time: `Submodule.mapQ` handles the inserted operation, and
`Submodule.liftQ` handles the outer one.
-/
import Operad.Basic
import Operad.Constructions
import Mathlib.LinearAlgebra.Quotient.Basic

universe u v w

namespace Operad

open NSOperad

/-- An ideal of a non-symmetric operad: a submodule in each arity, absorbing partial composition
on either side. -/
structure OperadIdeal (R : Type u) [CommRing R] (P : ℕ → Type v)
    [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P] where
  /-- The submodule in each arity. -/
  carrier (n : ℕ) : Submodule R (P n)
  /-- Composing an element of the ideal with anything stays in the ideal. -/
  comp_mem_left (a b : ℕ) {n : ℕ} {α : P (a + 1 + b)} (hα : α ∈ carrier (a + 1 + b)) (β : P n) :
    comp (R := R) a b α β ∈ carrier (a + n + b)
  /-- Composing anything with an element of the ideal stays in the ideal. -/
  comp_mem_right (a b : ℕ) {n : ℕ} (α : P (a + 1 + b)) {β : P n} (hβ : β ∈ carrier n) :
    comp (R := R) a b α β ∈ carrier (a + n + b)

namespace OperadIdeal

variable {R : Type u} [CommRing R] {P : ℕ → Type v}
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P] (I : OperadIdeal R P)

/-- The quotient of an operad by an ideal, arity by arity. -/
def Quot (n : ℕ) : Type v := P n ⧸ I.carrier n

instance (n : ℕ) : AddCommGroup (I.Quot n) := inferInstanceAs (AddCommGroup (_ ⧸ _))

instance (n : ℕ) : Module R (I.Quot n) := inferInstanceAs (Module R (_ ⧸ _))

/-- The quotient map. -/
def proj (n : ℕ) : P n →ₗ[R] I.Quot n := (I.carrier n).mkQ

@[simp] lemma proj_apply {n : ℕ} (x : P n) : I.proj n x = Submodule.Quotient.mk x := rfl

lemma proj_surjective (n : ℕ) : Function.Surjective (I.proj n) :=
  Submodule.mkQ_surjective _

/-- Composition with a fixed outer operation, descended to the quotient. -/
def compRight (a b : ℕ) {n : ℕ} (α : P (a + 1 + b)) : I.Quot n →ₗ[R] I.Quot (a + n + b) :=
  Submodule.mapQ _ _ (comp (R := R) a b α) fun _ hx => I.comp_mem_right a b α hx

@[simp] lemma compRight_proj (a b : ℕ) {n : ℕ} (α : P (a + 1 + b)) (β : P n) :
    I.compRight a b α (I.proj n β) = I.proj (a + n + b) (comp (R := R) a b α β) := rfl

/-- Partial composition on the quotient. -/
def compQ (a b : ℕ) {n : ℕ} : I.Quot (a + 1 + b) →ₗ[R] I.Quot n →ₗ[R] I.Quot (a + n + b) :=
  Submodule.liftQ _
    { toFun := fun α => I.compRight a b α
      map_add' := fun α α' => by
        refine LinearMap.ext fun x => ?_
        obtain ⟨y, rfl⟩ := I.proj_surjective n x
        simp only [compRight_proj, LinearMap.add_apply, map_add]
      map_smul' := fun r α => by
        refine LinearMap.ext fun x => ?_
        obtain ⟨y, rfl⟩ := I.proj_surjective n x
        simp only [compRight_proj, LinearMap.smul_apply, RingHom.id_apply, map_smul] }
    (by
      intro α hα
      refine LinearMap.ext fun x => ?_
      obtain ⟨y, rfl⟩ := I.proj_surjective n x
      simpa only [compRight_proj, LinearMap.zero_apply, proj_apply] using
        (Submodule.Quotient.mk_eq_zero _).2 (I.comp_mem_left a b hα y))

@[simp] lemma compQ_proj (a b : ℕ) {n : ℕ} (α : P (a + 1 + b)) (β : P n) :
    I.compQ a b (I.proj (a + 1 + b) α) (I.proj n β) = I.proj (a + n + b) (comp (R := R) a b α β) := rfl

/-- Reindexing commutes with the quotient map. -/
lemma proj_reindex {m n : ℕ} (h : m = n) (x : P m) :
    reindex R I.Quot h (I.proj m x) = I.proj n (reindex R P h x) := by
  subst h
  simp only [reindex_self]

/-- **The quotient of an operad by an ideal is an operad.** Each axiom is the corresponding
axiom of `P`, pushed through the quotient map. -/
instance : NSOperad R I.Quot where
  one := I.proj 1 (one (R := R) (P := P))
  comp a b := I.compQ a b
  comp_one_right := by
    intro a b α
    obtain ⟨x, rfl⟩ := I.proj_surjective _ α
    exact congrArg _ (comp_one_right a b x)
  comp_one_left := by
    intro n α
    obtain ⟨x, rfl⟩ := I.proj_surjective _ α
    rw [show I.compQ 0 0 (I.proj 1 (one (R := R) (P := P))) (I.proj n x)
        = I.proj (0 + n + 0) (comp (R := R) 0 0 (one (R := R) (P := P)) x) from rfl,
      proj_reindex]
    exact congrArg _ (comp_one_left x)
  comp_assoc_seq := by
    intro a b c d p α β γ
    obtain ⟨x, rfl⟩ := I.proj_surjective _ α
    obtain ⟨y, rfl⟩ := I.proj_surjective _ β
    obtain ⟨z, rfl⟩ := I.proj_surjective _ γ
    simp only [compQ_proj, proj_reindex]
    exact congrArg _ (comp_assoc_seq a b c d x y z)
  comp_assoc_par := by
    intro a b c n p α β γ
    obtain ⟨x, rfl⟩ := I.proj_surjective _ α
    obtain ⟨y, rfl⟩ := I.proj_surjective _ β
    obtain ⟨z, rfl⟩ := I.proj_surjective _ γ
    simp only [compQ_proj, proj_reindex]
    exact congrArg _ (comp_assoc_par a b c x y z)

/-- The quotient map is a morphism of operads. -/
def projHom : NSOperadHom R P I.Quot where
  app n := I.proj n
  app_one := rfl
  app_comp := by intros; rfl

end OperadIdeal

/-! ### The ideal generated by a set of relations

This is what turns quotients into presentations: given relations, take the smallest ideal
containing them, and quotient. The generating process is an inductive predicate, whose
constructors are exactly the closure conditions an ideal must satisfy. -/

section Generated

variable {R : Type u} [CommRing R] {P : ℕ → Type v}
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]

/-- Membership in the ideal generated by `S`. -/
inductive IsGenerated (S : ∀ n, Set (P n)) : ∀ n, P n → Prop
  /-- A relation is in the ideal it generates. -/
  | basic {n : ℕ} {x : P n} (hx : x ∈ S n) : IsGenerated S n x
  /-- Ideals contain zero. -/
  | zero {n : ℕ} : IsGenerated S n 0
  /-- Ideals are closed under addition. -/
  | add {n : ℕ} {x y : P n} : IsGenerated S n x → IsGenerated S n y → IsGenerated S n (x + y)
  /-- Ideals are closed under scaling. -/
  | smul {n : ℕ} (r : R) {x : P n} : IsGenerated S n x → IsGenerated S n (r • x)
  /-- Ideals absorb composition on the left. -/
  | compL (a b : ℕ) {n : ℕ} {α : P (a + 1 + b)} (β : P n) (h : IsGenerated S (a + 1 + b) α) :
      IsGenerated S (a + n + b) (comp (R := R) a b α β)
  /-- Ideals absorb composition on the right. -/
  | compR (a b : ℕ) {n : ℕ} (α : P (a + 1 + b)) {β : P n} (h : IsGenerated S n β) :
      IsGenerated S (a + n + b) (comp (R := R) a b α β)

/-- The ideal generated by a family of relations. -/
def generated (S : ∀ n, Set (P n)) : OperadIdeal R P where
  carrier n :=
    { carrier := {x | IsGenerated S n x}
      add_mem' := fun hx hy => .add hx hy
      zero_mem' := .zero
      smul_mem' := fun r _ hx => .smul r hx }
  comp_mem_left := by
    intro a b n α hα β
    exact .compL a b β hα
  comp_mem_right := by
    intro a b n α β hβ
    exact .compR a b α hβ

lemma subset_generated (S : ∀ n, Set (P n)) {n : ℕ} {x : P n} (hx : x ∈ S n) :
    x ∈ (generated (R := R) S).carrier n := IsGenerated.basic hx

end Generated

/-! ### The universal property of the quotient

A morphism that kills the relations factors through the operad they present. This is what makes a
presentation usable: it is how one maps *out* of `AssPres` and friends. -/

section Lift

variable {R : Type u} [CommRing R] {P : ℕ → Type v}
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]
  {Q : ℕ → Type w} [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)] [NSOperad R Q]

/-- A morphism killing a family of relations kills the whole ideal they generate. -/
lemma apply_eq_zero_of_isGenerated (φ : NSOperadHom R P Q) (S : ∀ n, Set (P n))
    (hS : ∀ n, ∀ x ∈ S n, φ.app n x = 0) :
    ∀ {n : ℕ} {x : P n}, IsGenerated (R := R) S n x → φ.app n x = 0 := by
  intro n x hx
  induction hx with
  | basic h => exact hS _ _ h
  | zero => exact map_zero _
  | add _ _ ihx ihy => rw [map_add, ihx, ihy, add_zero]
  | smul r _ ih => rw [map_smul, ih, smul_zero]
  | compL a b β _ ih => rw [φ.app_comp, ih, map_zero, LinearMap.zero_apply]
  | compR a b α _ ih => rw [φ.app_comp, ih, map_zero]

/-- **The universal property of the quotient operad.** A morphism vanishing on the ideal factors
through the quotient. -/
noncomputable def OperadIdeal.liftHom (I : OperadIdeal R P) (φ : NSOperadHom R P Q)
    (h : ∀ (n : ℕ), ∀ x ∈ I.carrier n, φ.app n x = 0) : NSOperadHom R I.Quot Q where
  app n := Submodule.liftQ (I.carrier n) (φ.app n) (fun x hx => h n x hx)
  app_one := φ.app_one
  app_comp := by
    intro a b n α β
    obtain ⟨x, rfl⟩ := I.proj_surjective _ α
    obtain ⟨y, rfl⟩ := I.proj_surjective _ β
    exact φ.app_comp a b x y

@[simp] lemma OperadIdeal.liftHom_proj (I : OperadIdeal R P) (φ : NSOperadHom R P Q)
    (h : ∀ (n : ℕ), ∀ x ∈ I.carrier n, φ.app n x = 0) (n : ℕ) (x : P n) :
    (I.liftHom φ h).app n (I.proj n x) = φ.app n x := rfl

end Lift

end Operad
