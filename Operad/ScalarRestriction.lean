/-
# Restriction of scalars for symmetric operads

For a commutative `R`-algebra `S`, an operad `Q` over `S` is an operad over `R`.

* `ResOp R S Q`: the same modules, with `r • x = algebraMap R S r • x`, and the operad structure
  over `R` (`ResOp.instSymOperad`).
* `SymOperadHom.res`: a morphism of operads over `S` as a morphism over `R`;
  `SymOperadIdeal.res`: an ideal over `S` as an ideal over `R`.
* `SymOperadIdeal.smulTop c`: the multiples of a scalar `c` form an ideal.
-/
import Operad.SymQuot
import Operad.SymIso

universe u u' v w

namespace Operad

/-- **Restriction of scalars**: the modules of an operad over `S`, as modules over `R`. -/
@[nolint unusedArguments]
def ResOp (_R : Type u) (_S : Type u')
    (Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v) :
    (A : Type) → [Fintype A] → [DecidableEq A] → Type v :=
  fun A _ _ => Q A

variable (R : Type u) [CommRing R] (S : Type u') [CommRing S] [Algebra R S]
  (Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module S (Q A)]

namespace ResOp

variable {R S Q}

instance (A : Type) [Fintype A] [DecidableEq A] : AddCommGroup (ResOp R S Q A) :=
  inferInstanceAs (AddCommGroup (Q A))

instance (A : Type) [Fintype A] [DecidableEq A] : Module S (ResOp R S Q A) :=
  inferInstanceAs (Module S (Q A))

instance (A : Type) [Fintype A] [DecidableEq A] : Module R (ResOp R S Q A) :=
  Module.compHom (Q A) (algebraMap R S)

lemma smul_def {A : Type} [Fintype A] [DecidableEq A] (r : R) (x : ResOp R S Q A) :
    r • x = algebraMap R S r • x := rfl

instance (A : Type) [Fintype A] [DecidableEq A] : IsScalarTower R S (ResOp R S Q A) :=
  ⟨fun r s x => by
    show (r • s) • x = algebraMap R S r • s • x
    rw [Algebra.smul_def, mul_smul]⟩

variable [SymOperad S Q]

/-- **Restriction of scalars of an operad.** -/
instance instSymOperad : SymOperad R (ResOp R S Q) where
  map e :=
    { toFun := SymOperad.map (R := S) (P := Q) e
      map_add' := map_add _
      map_smul' := fun r x => map_smul (SymOperad.map (R := S) (P := Q) e) (algebraMap R S r) x }
  map_refl x := SymOperad.map_refl (R := S) (P := Q) x
  map_trans e f x := SymOperad.map_trans (R := S) (P := Q) e f x
  one := (SymOperad.one S : Q Unit)
  comp i := LinearMap.mk₂ R (fun x y => SymOperad.comp (R := S) (P := Q) i x y)
    (fun x x' y => LinearMap.congr_fun ((SymOperad.comp (R := S) (P := Q) i).map_add x x') y)
    (fun r x y => LinearMap.congr_fun
      ((SymOperad.comp (R := S) (P := Q) i).map_smul (algebraMap R S r) x) y)
    (fun x y y' => (SymOperad.comp (R := S) (P := Q) i x).map_add y y')
    (fun r x y => (SymOperad.comp (R := S) (P := Q) i x).map_smul (algebraMap R S r) y)
  map_comp σ τ i x y := SymOperad.map_comp (R := S) (P := Q) σ τ i x y
  comp_one i x := SymOperad.comp_one (R := S) (P := Q) i x
  one_comp y := SymOperad.one_comp (R := S) (P := Q) y
  comp_assoc_seq i j x y z := SymOperad.comp_assoc_seq (R := S) (P := Q) i j x y z
  comp_assoc_par hik x y z := SymOperad.comp_assoc_par (R := S) (P := Q) hik x y z

lemma map_def {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    (x : ResOp R S Q A) :
    SymOperad.map (R := R) e x = SymOperad.map (R := S) (P := Q) e x := rfl

lemma comp_def {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (x : ResOp R S Q A) (y : ResOp R S Q B) :
    SymOperad.comp (R := R) i x y = SymOperad.comp (R := S) (P := Q) i x y := rfl

lemma one_def : (SymOperad.one R : ResOp R S Q Unit) = (SymOperad.one S : Q Unit) := rfl

end ResOp

variable {R S Q}
variable [SymOperad S Q]
  {Q' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module S (Q' A)] [SymOperad S Q']

variable (R) in
/-- **A morphism of operads over `S` is a morphism over `R`.** -/
def SymOperadHom.res (f : SymOperadHom S Q Q') : SymOperadHom R (ResOp R S Q) (ResOp R S Q') where
  app A _ _ :=
    { toFun := f.app A
      map_add' := map_add _
      map_smul' := fun r x => map_smul (f.app A) (algebraMap R S r) x }
  app_map e x := f.app_map e x
  app_one := by
    show f.app Unit (SymOperad.one S : Q Unit) = (SymOperad.one S : Q' Unit)
    exact f.app_one
  app_comp i x y := f.app_comp i x y

@[simp] lemma SymOperadHom.res_app (f : SymOperadHom S Q Q') {A : Type} [Fintype A]
    [DecidableEq A] (x : Q A) : (f.res R).app A x = f.app A x := rfl

namespace SymOperadIdeal

variable (R) in
/-- **An ideal over `S` is an ideal over `R`.** -/
def res (I : SymOperadIdeal S Q) : SymOperadIdeal R (ResOp R S Q) where
  sub A _ _ :=
    { carrier := {x | x ∈ I.sub A}
      add_mem' := (I.sub A).add_mem
      zero_mem' := (I.sub A).zero_mem
      smul_mem' := fun r _ hx => (I.sub A).smul_mem (algebraMap R S r) hx }
  map_mem e _ hx := I.map_mem e hx
  comp_mem_left i _ y hx := I.comp_mem_left i y hx
  comp_mem_right i x _ hy := I.comp_mem_right i x hy

@[simp] lemma mem_res (I : SymOperadIdeal S Q) {A : Type} [Fintype A] [DecidableEq A]
    {x : Q A} : x ∈ (I.res R).sub A ↔ x ∈ I.sub A := Iff.rfl

variable (Q) in
/-- **The multiples of a scalar** form an ideal. -/
def smulTop (c : S) : SymOperadIdeal S Q where
  sub A _ _ := LinearMap.range (c • (LinearMap.id : Q A →ₗ[S] Q A))
  map_mem := by
    rintro A B _ _ _ _ e _ ⟨x, rfl⟩
    exact ⟨SymOperad.map (R := S) e x, by
      simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, map_smul]⟩
  comp_mem_left := by
    rintro A B _ _ _ _ i _ y ⟨x, rfl⟩
    exact ⟨SymOperad.comp (R := S) i x y, by
      simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, map_smul]⟩
  comp_mem_right := by
    rintro A B _ _ _ _ i x _ ⟨y, rfl⟩
    exact ⟨SymOperad.comp (R := S) i x y, by
      simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, map_smul]⟩

lemma mem_smulTop {c : S} {A : Type} [Fintype A] [DecidableEq A] {x : Q A} :
    x ∈ (smulTop Q c).sub A ↔ ∃ y : Q A, x = c • y :=
  ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩

end SymOperadIdeal

end Operad
