/-
# Algebras over `Com` are commutative algebras

`Com R A = R`, with composition the product. An algebra over `Com` on a module `V` acts by `p` in
each arity; the action of `1` is a product of the arguments, invariant under relabelling and
compatible with substitution.

* `ComAlg.toCommRing`, `ComAlg.toAlgebra`: **the commutative algebra of a `Com`-algebra**, with
  product the action of `1` in arity two and unit its action in arity zero.
* `ComAlg.act_eq_prod`: the action of `p` is `p` times the product of the arguments.
* `ComAlg.ofCommAlgebra`: **the `Com`-algebra of a commutative algebra**. The two constructions
  are inverse to each other (`ComAlg.ofCommAlgebra_toCommRing`, `ComAlg.mul_ofCommAlgebra`,
  `ComAlg.one_ofCommAlgebra`), and the morphisms of `Com`-algebras between commutative algebras
  are the algebra morphisms (`ComAlg.homEquiv`).
* **The free `Com`-algebra is the symmetric algebra** (`Schur.isSymmetricAlgebra_com`,
  `Schur.symmetricAlgebraEquiv`).
-/
import Operad.FreeAlgebra
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.Algebra.Ring.Ext

universe u v w x

namespace Operad

open Function

namespace Sym

namespace ComAlg

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
  (α : SymAlgebra R (Com R) V)

/-! ## Products in a `Com`-algebra -/

/-- **The product of a family** in a `Com`-algebra: the action of `1`. -/
def prod {A : Type} [Fintype A] [DecidableEq A] (s : A → V) : V := α.act (1 : Com R A) s

/-- The action of `p` is `p` times the product. -/
lemma act_eq_smul_prod {A : Type} [Fintype A] [DecidableEq A] (p : Com R A) (s : A → V) :
    α.act p s = p • prod α s := by
  unfold prod SymAlgebra.act
  conv_lhs => rw [show p = p • (1 : R) by rw [smul_eq_mul, mul_one]]
  rw [map_smul]
  rfl

/-- **Products are invariant under relabelling.** -/
lemma prod_relabel {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) (s : B → V) : prod α (fun a => s (e a)) = prod α s :=
  (SymAlgebra.act_map α e (1 : Com R A) s).symm

/-- **Products are compatible with substitution.** -/
lemma prod_comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (s : Without A i ⊕ B → V) : prod α s = prod α (feed i s (prod α fun b => s (Sum.inr b))) := by
  have h := SymAlgebra.act_comp α i (1 : Com R A) (1 : Com R B) s
  rw [show SymOperad.comp (R := R) i (1 : Com R A) (1 : Com R B)
    = (1 : Com R (Without A i ⊕ B)) from mul_one (1 : R)] at h
  exact h

lemma prod_unit (s : Unit → V) : prod α s = s () :=
  SymAlgebra.act_one α s

lemma prod_unique {A : Type} [Fintype A] [DecidableEq A] [Unique A] (s : A → V) :
    prod α s = s default := by
  rw [← prod_relabel α (Equiv.equivPUnit A).symm, prod_unit]
  rfl

lemma prod_eq_of_forall_eq {A : Type} [Fintype A] [DecidableEq A] (a₀ : A) (h : ∀ a, a = a₀)
    (s : A → V) : prod α s = s a₀ := by
  letI : Unique A := ⟨⟨a₀⟩, h⟩
  exact prod_unique α s

lemma prod_congr_empty {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [IsEmpty A] [IsEmpty B] (s : A → V) (t : B → V) : prod α s = prod α t := by
  rw [← prod_relabel α (Equiv.equivOfIsEmpty A B) t]
  congr 1
  funext a
  exact isEmptyElim a

/-! ## The commutative algebra -/

/-- The product of a `Com`-algebra: the action of `1` in arity two. -/
def mul (x y : V) : V := prod α ![x, y]

/-- The unit of a `Com`-algebra: the action of `1` in arity zero. -/
def one : V := prod α (Fin.elim0 : Fin 0 → V)

lemma prod_empty {A : Type} [Fintype A] [DecidableEq A] [IsEmpty A] (s : A → V) :
    prod α s = one α :=
  prod_congr_empty α s _

/-- The inputs of a binary operation with an operation inserted at its second input. -/
def splitEquiv {A : Type} [DecidableEq A] (i : A) : Without (Fin 2) 1 ⊕ Without A i ≃ A where
  toFun
    | Sum.inl _ => i
    | Sum.inr a => a.1
  invFun a := if h : a = i then Sum.inl ⟨0, by decide⟩ else Sum.inr ⟨a, h⟩
  left_inv := by
    rintro (⟨k, hk⟩ | ⟨a, ha⟩)
    · have hk0 : k = 0 := by
        revert k
        decide
      subst hk0
      simp
    · simp [ha]
  right_inv a := by
    by_cases h : a = i
    · subst h
      simp
    · simp [h]

/-- **Splitting off one argument.** -/
lemma prod_split {A : Type} [Fintype A] [DecidableEq A] (i : A) (s : A → V) :
    prod α s = mul α (s i) (prod α fun a : Without A i => s a.1) := by
  rw [← prod_relabel α (splitEquiv i) s, prod_comp α 1]
  unfold mul
  congr 1
  funext k
  fin_cases k <;> rfl

lemma mul_comm' (x y : V) : mul α x y = mul α y x := by
  unfold mul
  rw [← prod_relabel α (Equiv.swap 0 1) ![x, y]]
  congr 1
  funext k
  fin_cases k <;> rfl

lemma one_mul' (x : V) : mul α (one α) x = x := by
  have h := prod_comp α (B := Fin 0) (0 : Fin 2) fun _ => x
  have hu : ∀ c : Without (Fin 2) 0 ⊕ Fin 0, c = Sum.inl ⟨1, by decide⟩ := by decide
  rw [prod_eq_of_forall_eq α _ hu] at h
  refine Eq.trans ?_ h.symm
  unfold mul one
  congr 1
  funext k
  fin_cases k
  · exact prod_congr_empty α _ _
  · rfl

lemma mul_one' (x : V) : mul α x (one α) = x := by
  rw [mul_comm', one_mul']

lemma mul_assoc' (x y z : V) : mul α (mul α x y) z = mul α x (mul α y z) := by
  have h0 := prod_split α (0 : Fin 3) ![x, y, z]
  have h2 := prod_split α (2 : Fin 3) ![x, y, z]
  have u0 : ∀ c : Without (Without (Fin 3) 0) ⟨1, by decide⟩, c = ⟨⟨2, by decide⟩, by decide⟩ := by
    decide
  have u2 : ∀ c : Without (Without (Fin 3) 2) ⟨0, by decide⟩, c = ⟨⟨1, by decide⟩, by decide⟩ := by
    decide
  rw [prod_split α (⟨1, by decide⟩ : Without (Fin 3) 0), prod_eq_of_forall_eq α _ u0] at h0
  rw [prod_split α (⟨0, by decide⟩ : Without (Fin 3) 2), prod_eq_of_forall_eq α _ u2] at h2
  rw [mul_comm' α (mul α x y)]
  exact h2.symm.trans h0

lemma mul_add' (x y z : V) : mul α x (y + z) = mul α x y + mul α x z := by
  unfold mul prod SymAlgebra.act
  have h := (α.app (Fin 2) (1 : Com R (Fin 2))).map_update_add ![x, y] 1 y z
  simp only [show ∀ t : V, update ![x, y] 1 t = ![x, t] from fun t => by
    funext k
    fin_cases k <;> rfl] at h
  exact h

lemma mul_smul' (c : R) (x y : V) : mul α x (c • y) = c • mul α x y := by
  unfold mul prod SymAlgebra.act
  have h := (α.app (Fin 2) (1 : Com R (Fin 2))).map_update_smul ![x, y] 1 c y
  simp only [show ∀ t : V, update ![x, y] 1 t = ![x, t] from fun t => by
    funext k
    fin_cases k <;> rfl] at h
  exact h

lemma mul_zero' (x : V) : mul α x 0 = 0 := by
  have h := mul_smul' α (0 : R) x 0
  rwa [zero_smul, zero_smul] at h

/-- **The commutative ring of a `Com`-algebra.** -/
abbrev toCommRing : CommRing V :=
  { ‹AddCommGroup V› with
    mul := mul α
    one := one α
    mul_assoc := mul_assoc' α
    one_mul := one_mul' α
    mul_one := mul_one' α
    left_distrib := mul_add' α
    right_distrib := fun x y z => by
      show mul α (x + y) z = mul α x z + mul α y z
      rw [mul_comm' α, mul_add', mul_comm' α x, mul_comm' α y]
    zero_mul := fun x => by
      show mul α 0 x = 0
      rw [mul_comm', mul_zero']
    mul_zero := mul_zero' α
    mul_comm := mul_comm' α }

/-- **The commutative algebra of a `Com`-algebra.** -/
abbrev toAlgebra : @Algebra R V _ (toCommRing α).toSemiring :=
  letI := toCommRing α
  Algebra.ofModule (fun c x y => by
      show mul α (c • x) y = c • mul α x y
      rw [mul_comm', mul_smul', mul_comm'])
    fun c x y => mul_smul' α c x y

/-- **The action of `p` is `p` times the product of the arguments.** -/
theorem act_eq_prod {A : Type} [Fintype A] [DecidableEq A] (p : Com R A) (s : A → V) :
    letI := toCommRing α
    α.act p s = p • ∏ a, s a := by
  letI := toCommRing α
  rw [act_eq_smul_prod]
  congr 1
  suffices h : ∀ (n : ℕ) (t : Fin n → V), prod α t = ∏ k, t k by
    rw [← prod_relabel α (Fintype.equivFin A).symm, h, Equiv.prod_comp]
  intro n
  induction n with
  | zero =>
    intro t
    rw [prod_empty, Finset.univ_eq_empty, Finset.prod_empty]
    rfl
  | succ n ih =>
    intro t
    rw [prod_split α 0, Fin.prod_univ_succ, ← ih]
    congr 1
    rw [← prod_relabel α (finSuccAboveEquiv (0 : Fin (n + 1)))]
    rfl

/-! ## The `Com`-algebra of a commutative algebra -/

section OfCommAlgebra

variable (A : Type w) [CommRing A] [Algebra R A]

variable (R) in
/-- **The `Com`-algebra of a commutative algebra**: `p` acts as `p` times the product. -/
noncomputable def ofCommAlgebra : SymAlgebra R (Com R) A where
  app B _ _ :=
    { toFun := fun p => p • MultilinearMap.mkPiAlgebra R B A
      map_add' := fun p q => add_smul p q _
      map_smul' := fun c p => smul_assoc c p _ }
  app_map e p := MultilinearMap.ext fun v => by
    show p • ∏ b, v b = p • ∏ a, v (e a)
    rw [Equiv.prod_comp]
  app_one := MultilinearMap.ext fun v => by
    show (1 : R) • ∏ u, v u = v ()
    simp
  app_comp i x y := MultilinearMap.ext fun v => by
    show (x * y) • ∏ c, v c = x • ∏ a, feed i v (y • ∏ b, v (Sum.inr b)) a
    rw [Fintype.prod_sum_type, Fintype.prod_eq_mul_prod_subtype_ne _ i, feed_self,
      Fintype.prod_congr _ _ (fun a : {a // a ≠ i} => feed_of_ne a.2 v _), smul_mul_assoc,
      smul_smul, mul_comm (∏ b, v (Sum.inr b))]

lemma ofCommAlgebra_act {B : Type} [Fintype B] [DecidableEq B] (p : Com R B) (s : B → A) :
    (ofCommAlgebra R A).act p s = p • ∏ b, s b :=
  rfl

lemma mul_ofCommAlgebra (x y : A) : mul (ofCommAlgebra R A) x y = x * y := by
  show (1 : R) • ∏ k, ![x, y] k = x * y
  simp

lemma one_ofCommAlgebra : one (ofCommAlgebra R A) = 1 := by
  show (1 : R) • ∏ k, (Fin.elim0 : Fin 0 → A) k = 1
  simp

/-- **The commutative ring of the `Com`-algebra of a commutative ring is that ring.** -/
theorem ofCommAlgebra_toCommRing : toCommRing (ofCommAlgebra R A) = ‹CommRing A› := by
  refine CommRing.ext rfl ?_
  funext x y
  exact mul_ofCommAlgebra (R := R) A x y

end OfCommAlgebra

/-- **The `Com`-algebra of the commutative algebra of a `Com`-algebra is that `Com`-algebra.** -/
theorem toCommRing_ofCommAlgebra :
    letI := toCommRing α
    letI := toAlgebra α
    ofCommAlgebra R V = α := by
  letI := toCommRing α
  letI := toAlgebra α
  exact SymOperadHom.ext fun B _ _ p => MultilinearMap.ext fun s => (act_eq_prod α p s).symm

/-! ## Morphisms -/

section Hom

variable {A : Type w} {B : Type x} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- **Morphisms of `Com`-algebras between commutative algebras are the algebra morphisms.** -/
noncomputable def homEquiv :
    SymAlgebraHom (ofCommAlgebra R A) (ofCommAlgebra R B) ≃ (A →ₐ[R] B) where
  toFun F :=
    { toFun := F.toLinearMap
      map_one' := by
        rw [← one_ofCommAlgebra (R := R) A, one, prod, F.map_act, ← one_ofCommAlgebra (R := R) B]
        exact congrArg _ (funext fun k => k.elim0)
      map_mul' := fun x y => by
        rw [← mul_ofCommAlgebra (R := R) A, mul, prod, F.map_act, ← mul_ofCommAlgebra (R := R) B]
        show _ = (ofCommAlgebra R B).act 1 ![_, _]
        congr 1
        funext k
        fin_cases k <;> rfl
      map_zero' := F.toLinearMap.map_zero
      map_add' := F.toLinearMap.map_add
      commutes' := fun c => by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
        show F.toLinearMap (c • 1) = c • 1
        rw [map_smul, ← one_ofCommAlgebra (R := R) A, one, prod, F.map_act,
          ← one_ofCommAlgebra (R := R) B]
        congr 2
        funext k
        exact k.elim0 }
  invFun f :=
    { toLinearMap := f.toLinearMap
      map_act := fun p s => by
        rw [ofCommAlgebra_act, ofCommAlgebra_act, map_smul]
        simp }
  left_inv _ := rfl
  right_inv _ := rfl

end Hom

end ComAlg

end Sym

/-! ## The free `Com`-algebra -/

namespace Schur

open Sym

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

noncomputable instance instCommRingCom : CommRing (Schur R (Com R) V) :=
  ComAlg.toCommRing (algebra R (Com R) V)

noncomputable instance instAlgebraCom : Algebra R (Schur R (Com R) V) :=
  ComAlg.toAlgebra (algebra R (Com R) V)

/-- In the free `Com`-algebra, operations act by products. -/
lemma act_com {A : Type} [Fintype A] [DecidableEq A] (p : Com R A) (s : A → Schur R (Com R) V) :
    act p s = p • ∏ a, s a :=
  ComAlg.act_eq_prod (algebra R (Com R) V) p s

/-- The `Com`-algebra morphism of an algebra morphism out of the free `Com`-algebra. -/
noncomputable def comHom {B : Type w} [CommRing B] [Algebra R B]
    (f : Schur R (Com R) V →ₐ[R] B) : SymAlgebraHom (algebra R (Com R) V) (ComAlg.ofCommAlgebra R B)
    where
  toLinearMap := f.toLinearMap
  map_act p s := by
    rw [algebra_act, act_com, ComAlg.ofCommAlgebra_act, AlgHom.toLinearMap_apply, map_smul,
      map_prod]
    rfl

/-- The algebra morphism of a `Com`-algebra morphism out of the free `Com`-algebra. -/
noncomputable def algHomOf {B : Type w} [CommRing B] [Algebra R B]
    (F : SymAlgebraHom (algebra R (Com R) V) (ComAlg.ofCommAlgebra R B)) :
    Schur R (Com R) V →ₐ[R] B where
  toFun := F.toLinearMap
  map_one' := by
    show F.toLinearMap (ComAlg.prod (algebra R (Com R) V) Fin.elim0) = 1
    rw [ComAlg.prod, F.map_act, ← ComAlg.one_ofCommAlgebra (R := R) B]
    exact congrArg _ (funext fun k => k.elim0)
  map_mul' x y := by
    show F.toLinearMap (ComAlg.prod (algebra R (Com R) V) ![x, y]) = _
    rw [ComAlg.prod, F.map_act, ← ComAlg.mul_ofCommAlgebra (R := R) B]
    show (ComAlg.ofCommAlgebra R B).act 1 _ = (ComAlg.ofCommAlgebra R B).act 1 ![_, _]
    congr 1
    funext k
    fin_cases k <;> rfl
  map_zero' := F.toLinearMap.map_zero
  map_add' := F.toLinearMap.map_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    show F.toLinearMap (c • ComAlg.prod (algebra R (Com R) V) Fin.elim0) = c • 1
    rw [map_smul, ComAlg.prod, F.map_act, ← ComAlg.one_ofCommAlgebra (R := R) B]
    congr 2
    funext k
    exact k.elim0

/-- **The free `Com`-algebra on `V` is the symmetric algebra of `V`.** -/
theorem isSymmetricAlgebra_com : IsSymmetricAlgebra (ι R (Com R) V) := by
  let G : Schur R (Com R) V →ₐ[R] SymmetricAlgebra R V :=
    algHomOf (liftHom (ComAlg.ofCommAlgebra R (SymmetricAlgebra R V)) (SymmetricAlgebra.ι R V))
  let L : SymmetricAlgebra R V →ₐ[R] Schur R (Com R) V := SymmetricAlgebra.lift (ι R (Com R) V)
  have hGL : G.comp L = AlgHom.id R (SymmetricAlgebra R V) := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun v => ?_)
    show G (L (SymmetricAlgebra.ι R V v)) = SymmetricAlgebra.ι R V v
    rw [SymmetricAlgebra.lift_ι_apply]
    exact liftHom_ι _ _ v
  have hLG : L.comp G = AlgHom.id R (Schur R (Com R) V) := by
    have h := algHom_ext (F := comHom (L.comp G)) (G := comHom (AlgHom.id R _)) fun v => by
      show L (G (ι R (Com R) V v)) = ι R (Com R) V v
      rw [show G (ι R (Com R) V v) = SymmetricAlgebra.ι R V v from liftHom_ι _ _ v,
        SymmetricAlgebra.lift_ι_apply]
    exact AlgHom.ext fun x => congrArg (fun F => F.toLinearMap x) h
  refine ⟨fun x y hxy => ?_, fun y => ⟨G y, congrArg (fun F => F y) hLG⟩⟩
  have hx : G (L x) = x := congrArg (fun F => F x) hGL
  have hy : G (L y) = y := congrArg (fun F => F y) hGL
  rw [← hx, ← hy]
  exact congrArg G hxy

/-- **The free `Com`-algebra on `V` is the symmetric algebra of `V`**, as algebras. -/
noncomputable def symmetricAlgebraEquiv : SymmetricAlgebra R V ≃ₐ[R] Schur R (Com R) V :=
  isSymmetricAlgebra_com.equiv

end Schur

end Operad
