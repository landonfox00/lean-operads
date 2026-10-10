/-
# Graded suboperads

A **graded suboperad** (`GrSuboperad`) of a graded operad is a family of submodules stable under
the parity projections, the relabellings and the compositions, and containing the unit. It is a
graded operad (`GrSuboperad.instGrOperad`), with an inclusion morphism (`GrSuboperad.incl`).

* **The preimage of a graded suboperad** under a morphism is a graded suboperad
  (`GrSuboperad.comap`).
* **A graded suboperad of a presented graded operad containing the generators is everything**
  (`GrSuboperad.mem_of_presGen`): the morphism out of the free graded operad defined by the
  generators lands in it, and agrees with the quotient map. This is the induction principle on the
  operations of a presented graded operad.
-/
import Operad.GrPresentation

universe u v w

namespace Operad

open Sym GerBV

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]

variable (R P) in
/-- **A graded suboperad**: submodules stable under the parity projections, the relabellings and
the compositions, containing the unit. -/
structure GrSuboperad where
  /-- The operations with inputs `A`. -/
  sub (A : Type) [Fintype A] [DecidableEq A] : Submodule R (P A)
  par_mem {A : Type} [Fintype A] [DecidableEq A] (b : Bool) {x : P A} :
    x ∈ sub A → GrOperad.par (R := R) b x ∈ sub A
  map_mem {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    {x : P A} : x ∈ sub A → GrOperad.map (R := R) e x ∈ sub B
  one_mem : GrOperad.one (R := R) (P := P) ∈ sub Unit
  comp_mem {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    {x : P A} {y : P B} :
    x ∈ sub A → y ∈ sub B → GrOperad.comp (R := R) i x y ∈ sub (Without A i ⊕ B)

namespace GrSuboperad

variable (S : GrSuboperad R P)

/-- The operations of the suboperad. -/
abbrev Op (A : Type) [Fintype A] [DecidableEq A] : Type v := S.sub A

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The composition, restricted. -/
def compS (i : A) : S.Op A →ₗ[R] S.Op B →ₗ[R] S.Op (Without A i ⊕ B) :=
  LinearMap.mk₂ R (fun x y => ⟨GrOperad.comp (R := R) i x.1 y.1, S.comp_mem i x.2 y.2⟩)
    (fun x x' y => Subtype.ext (by simp only [Submodule.coe_add, map_add, LinearMap.add_apply]))
    (fun c x y => Subtype.ext (by
      simp only [SetLike.val_smul, map_smul, LinearMap.smul_apply]))
    (fun x y y' => Subtype.ext (by simp only [Submodule.coe_add, map_add]))
    (fun c x y => Subtype.ext (by simp only [SetLike.val_smul, map_smul]))

@[simp] lemma coe_compS (i : A) (x : S.Op A) (y : S.Op B) :
    ((S.compS i x y : S.Op _) : P (Without A i ⊕ B)) = GrOperad.comp (R := R) i x.1 y.1 := rfl

/-- **A graded suboperad is a graded operad.** -/
instance instGrOperad : GrOperad R S.Op where
  par b := (GrOperad.par (R := R) b).restrict fun _ hx => S.par_mem b hx
  par_add x := Subtype.ext (GrOperad.par_add (R := R) x.1)
  par_par b b' x := Subtype.ext (by
    show GrOperad.par (R := R) b (GrOperad.par (R := R) b' x.1) = _
    rw [GrOperad.par_par]
    split_ifs <;> rfl)
  map e := (GrOperad.map (R := R) e).restrict fun _ hx => S.map_mem e hx
  map_refl x := Subtype.ext (GrOperad.map_refl (R := R) x.1)
  map_trans e f x := Subtype.ext (GrOperad.map_trans (R := R) e f x.1)
  map_par e b x := Subtype.ext (GrOperad.map_par (R := R) e b x.1)
  one := ⟨GrOperad.one (R := R), S.one_mem⟩
  par_one := Subtype.ext (GrOperad.par_one (R := R) (P := P))
  comp i := S.compS i
  comp_par i p q x y := Subtype.ext (GrOperad.comp_par (R := R) i p q x.1 y.1)
  map_comp σ' τ i x y := Subtype.ext (GrOperad.map_comp (R := R) σ' τ i x.1 y.1)
  comp_one i x := Subtype.ext (GrOperad.comp_one (R := R) i x.1)
  one_comp y := Subtype.ext (GrOperad.one_comp (R := R) y.1)
  comp_assoc_seq i j x y z := Subtype.ext (GrOperad.comp_assoc_seq (R := R) i j x.1 y.1 z.1)
  comp_assoc_par hik x q r y z hy hz := Subtype.ext
    (GrOperad.comp_assoc_par (R := R) hik x.1 (congrArg Subtype.val hy) (congrArg Subtype.val hz))

/-- **The inclusion** of a graded suboperad. -/
def incl : GrOperadHom R S.Op P where
  app A _ _ := (S.sub A).subtype
  app_par _ _ := rfl
  app_map _ _ := rfl
  app_one := rfl
  app_comp _ _ _ := rfl

@[simp] lemma incl_app (x : S.Op A) : S.incl.app A x = x.1 := rfl

variable {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]

/-- **The preimage of a graded suboperad** under a morphism. -/
def comap (φ : GrOperadHom R Q P) : GrSuboperad R Q where
  sub A _ _ := (S.sub A).comap (φ.app A)
  par_mem b x hx := by
    rw [Submodule.mem_comap, φ.app_par]
    exact S.par_mem b hx
  map_mem e x hx := by
    rw [Submodule.mem_comap, φ.app_map]
    exact S.map_mem e hx
  one_mem := by
    rw [Submodule.mem_comap, φ.app_one]
    exact S.one_mem
  comp_mem i x y hx hy := by
    rw [Submodule.mem_comap, φ.app_comp]
    exact S.comp_mem i hx hy

@[simp] lemma mem_comap (φ : GrOperadHom R Q P) (x : Q A) :
    x ∈ (S.comap φ).sub A ↔ φ.app A x ∈ S.sub A := Iff.rfl

end GrSuboperad

namespace GrOperadHom

variable {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]

/-- **The image of a morphism** is a graded suboperad. -/
def range (φ : GrOperadHom R Q P) : GrSuboperad R P where
  sub A _ _ := LinearMap.range (φ.app A)
  par_mem := by
    rintro A _ _ b _ ⟨x, rfl⟩
    exact ⟨GrOperad.par (R := R) b x, φ.app_par b x⟩
  map_mem := by
    rintro A B _ _ _ _ e _ ⟨x, rfl⟩
    exact ⟨GrOperad.map (R := R) e x, φ.app_map e x⟩
  one_mem := ⟨GrOperad.one (R := R), φ.app_one⟩
  comp_mem := by
    rintro A B _ _ _ _ i _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨GrOperad.comp (R := R) i x y, φ.app_comp i x y⟩

@[simp] lemma mem_range (φ : GrOperadHom R Q P) {A : Type} [Fintype A] [DecidableEq A]
    (x : P A) : x ∈ φ.range.sub A ↔ ∃ y, φ.app A y = x := Iff.rfl

end GrOperadHom

/-! ## The induction principle of a presented graded operad -/

namespace FreeGr

variable {T : ℕ → Type v} {gp : ∀ k, T k → Bool} {r : ∀ n : ℕ, Set (FreeGr R gp (Fin n))}

/-- **A generator has the parity of its label**, in a presented graded operad. -/
lemma par_presGen {k : ℕ} (e : T k) :
    GrOperad.par (R := R) (gp k e) (presGen r e) = presGen r e := by
  show GrOperad.par (R := R) _ ((GrOperadIdeal.span R r).projHom.app (Fin k) (gen e))
    = (GrOperadIdeal.span R r).projHom.app (Fin k) (gen e)
  rw [← GrOperadHom.app_par, par_gen]

/-- **A graded suboperad of a presented graded operad containing the generators contains every
operation.** -/
theorem mem_of_presGen (S : GrSuboperad R (GrOperadIdeal.span R r).Quot)
    (h : ∀ k (e : T k), presGen r e ∈ S.sub (Fin k)) {A : Type} [Fintype A] [DecidableEq A]
    (x : (GrOperadIdeal.span R r).Quot A) : x ∈ S.sub A := by
  let f : GenVal R gp S.Op := ⟨fun k e => ⟨presGen r e, h k e⟩, fun k e =>
    Subtype.ext (par_presGen e)⟩
  have hφ : S.incl.comp (homEquiv.symm f) = (GrOperadIdeal.span R r).projHom :=
    hom_ext fun k e => by
      rw [GrOperadHom.comp_app, homEquiv_symm_gen]
      rfl
  obtain ⟨y, rfl⟩ := (GrOperadIdeal.span R r).proj_surjective A x
  have := congrArg (fun φ : GrOperadHom R (FreeGr R gp) (GrOperadIdeal.span R r).Quot =>
    φ.app A y) hφ
  simp only [GrOperadHom.comp_app, GrSuboperad.incl_app] at this
  show (GrOperadIdeal.span R r).projHom.app A y ∈ S.sub A
  rw [← this]
  exact ((homEquiv.symm f).app A y).2

end FreeGr

end Operad
