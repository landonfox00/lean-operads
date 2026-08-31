/-
# Morphisms of non-symmetric operads, and a `Fin`-indexed composition wrapper

The positional convention of `Operad.Basic` is what makes the axioms tractable, but it is not
how anyone writes operads on paper. `compFin` bridges back: it takes a genuine slot index
`i : Fin m` and produces the usual `α ∘ᵢ β : P (m - 1 + n)`.
-/
import Operad.Basic

universe u v w w'

namespace Operad

open NSOperad

section CompFin

variable {R : Type u} [CommRing R] {P : ℕ → Type v}
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]

/-- Partial composition at a slot named by `i : Fin m`, in the textbook arity `m - 1 + n`.
This is the user-facing form; `NSOperad.comp` is the form the axioms are stated in. -/
def compFin {m n : ℕ} (i : Fin m) (α : P m) (β : P n) : P (m - 1 + n) :=
  reindex R P (by have := i.isLt; omega)
    (comp (R := R) (i : ℕ) (m - (i : ℕ) - 1)
      (reindex R P (by have := i.isLt; omega) α) β)

/-- `comp` only depends on its trailing index up to equality: changing `b` to an equal `b'`
just conjugates by reindexings. -/
lemma comp_index_congr (a : ℕ) {b b' : ℕ} (hb : b = b') {n : ℕ}
    (α : P (a + 1 + b)) (β : P n) :
    comp (R := R) a b' (reindex R P (by omega) α) β
      = reindex R P (by omega) (comp (R := R) a b α β) := by
  subst hb; simp

lemma compFin_add_left {m n : ℕ} (i : Fin m) (α α' : P m) (β : P n) :
    compFin (R := R) i (α + α') β = compFin (R := R) i α β + compFin (R := R) i α' β := by
  simp only [compFin, map_add, LinearMap.add_apply]

lemma compFin_add_right {m n : ℕ} (i : Fin m) (α : P m) (β β' : P n) :
    compFin (R := R) i α (β + β') = compFin (R := R) i α β + compFin (R := R) i α β' := by
  simp only [compFin, map_add]

lemma compFin_smul_left {m n : ℕ} (i : Fin m) (r : R) (α : P m) (β : P n) :
    compFin (R := R) i (r • α) β = r • compFin (R := R) i α β := by
  simp only [compFin, map_smul, LinearMap.smul_apply, RingHom.id_apply]

lemma compFin_smul_right {m n : ℕ} (i : Fin m) (r : R) (α : P m) (β : P n) :
    compFin (R := R) i α (r • β) = r • compFin (R := R) i α β := by
  simp only [compFin, map_smul, RingHom.id_apply]

@[simp] lemma compFin_zero_left {m n : ℕ} (i : Fin m) (β : P n) :
    compFin (R := R) i (0 : P m) β = 0 := by
  simp only [compFin, map_zero, LinearMap.zero_apply]

@[simp] lemma compFin_zero_right {m n : ℕ} (i : Fin m) (α : P m) :
    compFin (R := R) i α (0 : P n) = 0 := by
  simp only [compFin, map_zero]

/-- On an operation of arity `a + 1 + b`, composing at the `Fin` slot `a` agrees with the
positional composition, up to the reindexing `a + 1 + b - 1 + n = a + n + b`. -/
lemma compFin_eq_comp (a b : ℕ) {n : ℕ} (α : P (a + 1 + b)) (β : P n) :
    compFin (R := R) ⟨a, by omega⟩ α β
      = reindex R P (by omega) (comp (R := R) a b α β) := by
  unfold compFin
  simp only [Fin.val_mk]
  rw [comp_index_congr a (show b = a + 1 + b - a - 1 by omega) α β]
  simp

end CompFin

/-- A morphism of non-symmetric operads: a family of linear maps preserving the identity and
all partial compositions. -/
structure NSOperadHom (R : Type u) [CommRing R]
    (P : ℕ → Type v) [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]
    (Q : ℕ → Type w) [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)] [NSOperad R Q] where
  /-- The underlying linear map in each arity. -/
  app (n : ℕ) : P n →ₗ[R] Q n
  /-- The identity operation is preserved. -/
  app_one : app 1 (one (R := R) (P := P)) = one (R := R) (P := Q)
  /-- Partial composition is preserved. -/
  app_comp (a b : ℕ) {n : ℕ} (α : P (a + 1 + b)) (β : P n) :
    app (a + n + b) (comp (R := R) a b α β)
      = comp (R := R) a b (app (a + 1 + b) α) (app n β)

namespace NSOperadHom

variable {R : Type u} [CommRing R]
  {P : ℕ → Type v} [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]
  {Q : ℕ → Type w} [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)] [NSOperad R Q]

/-- Two morphisms agreeing in every arity are equal. -/
@[ext]
lemma ext {f g : NSOperadHom R P Q} (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f; cases g; congr 1; funext n; exact h n

/-- The identity morphism. -/
protected def id : NSOperadHom R P P where
  app _ := LinearMap.id
  app_one := rfl
  app_comp := by intros; rfl

@[simp]
lemma id_app (n : ℕ) : (NSOperadHom.id (R := R) (P := P)).app n = LinearMap.id := rfl

variable {S : ℕ → Type w'} [∀ n, AddCommGroup (S n)] [∀ n, Module R (S n)] [NSOperad R S]

/-- Composition of morphisms of operads. -/
protected def comp (g : NSOperadHom R Q S) (f : NSOperadHom R P Q) : NSOperadHom R P S where
  app n := (g.app n).comp (f.app n)
  app_one := by
    simp only [LinearMap.comp_apply, f.app_one, g.app_one]
  app_comp := by
    intros
    simp only [LinearMap.comp_apply, f.app_comp, g.app_comp]

@[simp]
lemma comp_app (g : NSOperadHom R Q S) (f : NSOperadHom R P Q) (n : ℕ) :
    (g.comp f).app n = (g.app n).comp (f.app n) := rfl

@[simp]
lemma comp_id (f : NSOperadHom R P Q) : f.comp NSOperadHom.id = f := by ext n; rfl

@[simp]
lemma id_comp (f : NSOperadHom R P Q) : NSOperadHom.id.comp f = f := by ext n; rfl

end NSOperadHom

end Operad
