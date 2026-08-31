/-
# Suboperads

An arity-wise family of submodules closed under the identity and partial composition. The point
is `instNSOperadSub`: such a family is itself an operad, so a concrete operad can be exhibited
*inside* `End V` without re-proving any of the four axioms.
-/
import Operad.Constructions

universe u v

namespace Operad

open NSOperad

variable {R : Type u} [CommRing R] {P : ℕ → Type v}
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]

/-- A suboperad of `P`: a submodule in each arity, containing the identity and closed under
partial composition. -/
structure Suboperad (R : Type u) [CommRing R] (P : ℕ → Type v)
    [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P] where
  /-- The submodule of operations of each arity. -/
  carrier (n : ℕ) : Submodule R (P n)
  /-- The identity operation belongs to the suboperad. -/
  one_mem' : one (R := R) (P := P) ∈ carrier 1
  /-- The suboperad is closed under partial composition. -/
  comp_mem' (a b : ℕ) {n : ℕ} {α : P (a + 1 + b)} {β : P n} :
    α ∈ carrier (a + 1 + b) → β ∈ carrier n → comp (R := R) a b α β ∈ carrier (a + n + b)

namespace Suboperad

variable (S : Suboperad R P)

instance : CoeSort (Suboperad R P) (ℕ → Type v) := ⟨fun S n => S.carrier n⟩

/-- Reindexing inside a suboperad agrees with reindexing in the ambient operad. -/
lemma coe_reindex {m n : ℕ} (h : m = n) (x : S.carrier m) :
    ((reindex R (fun k => (S.carrier k : Type v)) h x : S.carrier n) : P n)
      = reindex R P h (x : P m) := by
  subst h; rfl

/-- Partial composition, restricted to a suboperad. -/
def compSub (a b : ℕ) {n : ℕ} :
    (S.carrier (a + 1 + b)) →ₗ[R] (S.carrier n) →ₗ[R] (S.carrier (a + n + b)) where
  toFun α :=
    { toFun := fun β => ⟨comp (R := R) a b (α : P _) (β : P _), S.comp_mem' a b α.2 β.2⟩
      map_add' := fun β β' => by
        refine Subtype.ext ?_
        simp
      map_smul' := fun r β => by
        refine Subtype.ext ?_
        simp }
  map_add' α α' := by
    refine LinearMap.ext fun β => Subtype.ext ?_
    simp
  map_smul' r α := by
    refine LinearMap.ext fun β => Subtype.ext ?_
    simp

@[simp] lemma coe_compSub (a b : ℕ) {n : ℕ} (α : S.carrier (a + 1 + b)) (β : S.carrier n) :
    ((S.compSub a b α β : S.carrier (a + n + b)) : P (a + n + b))
      = comp (R := R) a b (α : P _) (β : P _) := rfl

/-- **A suboperad is an operad.** All four axioms are inherited from the ambient operad by
`Subtype.ext` plus `coe_reindex`. -/
instance instNSOperadSub : NSOperad R (fun n => (S.carrier n : Type v)) where
  one := ⟨one (R := R) (P := P), S.one_mem'⟩
  comp a b := S.compSub a b
  comp_one_right := by
    intro a b α
    refine Subtype.ext ?_
    simpa using NSOperad.comp_one_right a b (α : P _)
  comp_one_left := by
    intro n α
    refine Subtype.ext ?_
    rw [coe_reindex]
    simpa using NSOperad.comp_one_left (α : P n)
  comp_assoc_seq := by
    intro a b c d p α β γ
    refine Subtype.ext ?_
    rw [coe_reindex]
    simp only [coe_compSub, coe_reindex]
    simpa using NSOperad.comp_assoc_seq a b c d (α : P (a + 1 + b)) (β : P (c + 1 + d))
      (γ : P p)
  comp_assoc_par := by
    intro a b c n p α β γ
    refine Subtype.ext ?_
    rw [coe_reindex]
    simp only [coe_compSub, coe_reindex]
    simpa using NSOperad.comp_assoc_par a b c (α : P (a + 1 + b + 1 + c)) (β : P n) (γ : P p)

/-- The inclusion of a suboperad is a morphism of operads. -/
def incl : NSOperadHom R (fun n => (S.carrier n : Type v)) P where
  app n := (S.carrier n).subtype
  app_one := rfl
  app_comp := by intros; rfl

@[simp] lemma incl_app (n : ℕ) (x : S.carrier n) : S.incl.app n x = (x : P n) := rfl

end Suboperad

end Operad
