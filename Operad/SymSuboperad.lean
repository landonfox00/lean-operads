/-
# Suboperads of symmetric operads

A suboperad (`SymSuboperad`, defined in `Operad.Filtration`) of a symmetric operad is a symmetric
operad (`SymSuboperad.instSymOperad`), with an inclusion morphism (`SymSuboperad.incl`).

* **The preimage of a suboperad** under a morphism is a suboperad (`SymSuboperad.comap`).
* **A suboperad of a presented operad containing the generators is everything**
  (`SymSuboperad.mem_of_presGen`), for an operad presented by free generators and linear relators:
  the morphism out of the free operad defined by the generators lands in it, and agrees with the
  quotient map. This is the induction principle on the operations of a presented operad.
-/
import Operad.Filtration
import Operad.SymPresentation

universe u v w

namespace Operad

open Sym

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]

namespace SymSuboperad

variable (S : SymSuboperad R P)

/-- The operations of the suboperad. -/
abbrev Op (A : Type) [Fintype A] [DecidableEq A] : Type v := S.sub A

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The composition, restricted. -/
def compS (i : A) : S.Op A →ₗ[R] S.Op B →ₗ[R] S.Op (Without A i ⊕ B) :=
  LinearMap.mk₂ R (fun x y => ⟨SymOperad.comp (R := R) i x.1 y.1, S.comp_mem i x.2 y.2⟩)
    (fun x x' y => Subtype.ext (by simp only [Submodule.coe_add, map_add, LinearMap.add_apply]))
    (fun c x y => Subtype.ext (by
      simp only [SetLike.val_smul, map_smul, LinearMap.smul_apply]))
    (fun x y y' => Subtype.ext (by simp only [Submodule.coe_add, map_add]))
    (fun c x y => Subtype.ext (by simp only [SetLike.val_smul, map_smul]))

/-- **A suboperad is a symmetric operad.** -/
instance instSymOperad : SymOperad R S.Op where
  map e := (SymOperad.map (R := R) e).restrict fun _ hx => S.map_mem e hx
  map_refl x := Subtype.ext (SymOperad.map_refl (R := R) x.1)
  map_trans e f x := Subtype.ext (SymOperad.map_trans (R := R) e f x.1)
  one := ⟨SymOperad.one R, S.one_mem⟩
  comp i := S.compS i
  map_comp σ τ i x y := Subtype.ext (SymOperad.map_comp (R := R) σ τ i x.1 y.1)
  comp_one i x := Subtype.ext (SymOperad.comp_one (R := R) i x.1)
  one_comp y := Subtype.ext (SymOperad.one_comp (R := R) y.1)
  comp_assoc_seq i j x y z := Subtype.ext (SymOperad.comp_assoc_seq (R := R) i j x.1 y.1 z.1)
  comp_assoc_par hik x y z := Subtype.ext (SymOperad.comp_assoc_par (R := R) hik x.1 y.1 z.1)

/-- **The inclusion** of a suboperad. -/
def incl : SymOperadHom R S.Op P where
  app A _ _ := (S.sub A).subtype
  app_map _ _ := rfl
  app_one := rfl
  app_comp _ _ _ := rfl

@[simp] lemma incl_app (x : S.Op A) : S.incl.app A x = x.1 := rfl

variable {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]

/-- **The preimage of a suboperad** under a morphism. -/
def comap (φ : SymOperadHom R Q P) : SymSuboperad R Q where
  sub A _ _ := (S.sub A).comap (φ.app A)
  map_mem e x hx := by
    rw [Submodule.mem_comap, φ.app_map]
    exact S.map_mem e hx
  one_mem := by
    rw [Submodule.mem_comap, φ.app_one]
    exact S.one_mem
  comp_mem i x y hx hy := by
    rw [Submodule.mem_comap, φ.app_comp]
    exact S.comp_mem i hx hy

@[simp] lemma mem_comap (φ : SymOperadHom R Q P) (x : Q A) :
    x ∈ (S.comap φ).sub A ↔ φ.app A x ∈ S.sub A := Iff.rfl

end SymSuboperad

/-! ## The induction principle of a presented operad -/

namespace SymSuboperad

variable {T : ℕ → Type w}

/-- **A suboperad of the free operad containing the generators contains every operation.** -/
theorem mem_of_gen (S : SymSuboperad R (Lin R (FreeSet T)))
    (h : ∀ n (g : T n), Finsupp.single (Pres.gen g) 1 ∈ S.sub (Fin n))
    {A : Type} [Fintype A] [DecidableEq A] (x : Lin R (FreeSet T) A) : x ∈ S.sub A := by
  let Φ : SymOperadHom R (Lin R (FreeSet T)) S.Op :=
    linHomEquiv R (FreeSet.homEquiv.symm fun n g => Und.of R S.Op ⟨_, h n g⟩)
  have hΦ : S.incl.comp Φ = SymOperadHom.id := Pres.lin_hom_ext fun n g => by
    show ((Finsupp.lift _ R _ _ (Finsupp.single (Pres.gen g) 1) : S.Op (Fin n)) :
      Lin R (FreeSet T) (Fin n)) = _
    simp only [Finsupp.lift_apply, Finsupp.sum_single_index, zero_smul, one_smul]
    rfl
  have := congrArg (fun φ : SymOperadHom R (Lin R (FreeSet T)) (Lin R (FreeSet T)) =>
    φ.app A x) hΦ
  simp only [SymOperadHom.comp_app, incl_app] at this
  rw [show x = (Φ.app A x).1 from this.symm]
  exact (Φ.app A x).2

/-- **A suboperad of a presented operad containing the generators contains every operation**, for
an operad presented by free generators and linear relators. -/
theorem mem_of_presGen {r : ∀ n : ℕ, Set (Lin R (FreeSet T) (Fin n))}
    (S : SymSuboperad R (SymOperadIdeal.span R r).Quot)
    (h : ∀ n (g : T n),
      (SymOperadIdeal.span R r).proj _ (Finsupp.single (Pres.gen g) 1) ∈ S.sub (Fin n))
    {A : Type} [Fintype A] [DecidableEq A] (x : (SymOperadIdeal.span R r).Quot A) :
    x ∈ S.sub A := by
  obtain ⟨y, rfl⟩ := (SymOperadIdeal.span R r).proj_surjective A x
  exact mem_of_gen (S.comap (SymOperadIdeal.span R r).projHom) h y

end SymSuboperad

end Operad
