/-
# Algebras over `Lie` are Lie algebras, and the free one is the free Lie algebra

The operad `Lie` is presented by an antisymmetric bracket and the Jacobi identity
(`Operad.LieAlg`). Over a ring in which `2` is invertible, antisymmetry gives `[x, x] = 0`, and
`Lie`-algebras are Mathlib's Lie algebras.

* `Operad.Pres.act_mk_of_gen`, `Operad.SymOperadIdeal.algHomOfGen`: **a linear map between
  algebras over a presented operad commuting with the generators is a morphism of algebras**: the
  operations it commutes with are closed under relabelling and composition.
* `Operad.Lie.homEquiv`: **morphisms of `Lie`-algebras are the linear maps preserving the
  bracket** `Operad.Lie.bracket`.
* `Operad.LieAlg.toLieRing`, `Operad.LieAlg.toLieAlgebra`, `Operad.LieAlg.ofLieAlgebra`: **the Lie
  algebra of a `Lie`-algebra, and the `Lie`-algebra of a Lie algebra**, inverse to each other
  (`Operad.LieAlg.toLieRing_ofLieAlgebra`, `Operad.LieAlg.ofLieAlgebra_toLieAlgebra`); morphisms of
  `Lie`-algebras between Lie algebras are the Lie algebra morphisms (`Operad.LieAlg.homEquiv`).
* `Operad.Schur.lieLift`: **the free `Lie`-algebra on `V` is the free Lie algebra on the module
  `V`**: Lie algebra morphisms out of it are the linear maps out of `V`.
* **The free `Lie`-algebra on the free module on `X` is the free Lie algebra on `X`**
  (`Operad.Schur.freeLieAlgebraEquiv`).
-/
import Operad.FreeAlgebra
import Operad.BinaryQuadratic
import Mathlib.Algebra.Lie.Free

universe u v w x

namespace Operad

open Sym

/-! ## Morphisms of algebras over a presented operad -/

section Generators

variable {R : Type u} [CommRing R] {T : ℕ → Type w}
  {ρ : ∀ {A : Type} [Fintype A] [DecidableEq A], Syn T A → Syn T A → Prop}
  {V : Type v} [AddCommGroup V] [Module R V] {W : Type x} [AddCommGroup W] [Module R W]

lemma map_feed (f : V →ₗ[R] W) {A B : Type} [DecidableEq A] (i : A) (s : Without A i ⊕ B → V)
    (w : V) : (fun a => f (feed i s w a)) = feed i (fun c => f (s c)) (f w) := by
  funext a
  by_cases h : a = i
  · subst h
    simp
  · rw [feed_of_ne h, feed_of_ne h]

/-- **A linear map commuting with the generators commutes with every operation** of the free
operad on them. -/
theorem Pres.act_mk_of_gen {α : SymAlgebra R (Lin R (Pres T ρ)) V}
    {β : SymAlgebra R (Lin R (Pres T ρ)) W} {f : V →ₗ[R] W}
    (h : ∀ (n : ℕ) (g : T n) (s : Fin n → V),
      f (α.act (Finsupp.single (Pres.gen g) 1) s) =
        β.act (Finsupp.single (Pres.gen g) 1) fun k => f (s k))
    {A : Type} [Fintype A] [DecidableEq A] (x : Syn T A) :
    ∀ s : A → V, f (α.act (Finsupp.single (Pres.mk x) 1) s) =
      β.act (Finsupp.single (Pres.mk x) 1) fun a => f (s a) := by
  induction x with
  | one =>
    intro s
    show f (α.act (SymOperad.one R) s) = β.act (SymOperad.one R) _
    rw [SymAlgebra.act_one, SymAlgebra.act_one]
  | gen g => exact h _ g
  | @map A' A _ _ _ _ e x ih =>
    intro s
    have hx : (Finsupp.single (Pres.mk (Syn.map e x)) (1 : R) : Lin R (Pres T ρ) A) =
        SymOperad.map (R := R) (P := Lin R (Pres T ρ)) e (Finsupp.single (Pres.mk x) 1) := by
      show _ = Lin.mapL R e _
      rw [Lin.mapL_single]
      rfl
    rw [hx, SymAlgebra.act_map, SymAlgebra.act_map]
    exact ih _
  | @comp A₁ A₂ _ _ _ _ i x y ihx ihy =>
    intro s
    have hx : (Finsupp.single (Pres.mk (Syn.comp i x y)) (1 : R) : Lin R (Pres T ρ) _) =
        SymOperad.comp (R := R) (P := Lin R (Pres T ρ)) i (Finsupp.single (Pres.mk x) 1)
          (Finsupp.single (Pres.mk y) 1) := by
      show _ = Lin.compL R i _ _
      rw [Lin.compL_single, mul_one]
      rfl
    rw [hx, SymAlgebra.act_comp, SymAlgebra.act_comp, ihx, map_feed, ihy]

/-- **A morphism of algebras over a presented operad from its values on the generators**: a
linear map commuting with the actions of the generators commutes with every action. -/
def SymOperadIdeal.algHomOfGen (I : SymOperadIdeal R (Lin R (Pres T ρ)))
    {α : SymAlgebra R I.Quot V} {β : SymAlgebra R I.Quot W} (f : V →ₗ[R] W)
    (h : ∀ (n : ℕ) (g : T n) (s : Fin n → V),
      f (α.act (I.proj _ (Finsupp.single (Pres.gen g) 1)) s) =
        β.act (I.proj _ (Finsupp.single (Pres.gen g) 1)) fun k => f (s k)) :
    SymAlgebraHom α β where
  toLinearMap := f
  map_act {A} _ _ p s := by
    obtain ⟨y, rfl⟩ := I.proj_surjective A p
    show f (SymAlgebra.act (α.comp I.projHom) y s) =
      SymAlgebra.act (β.comp I.projHom) y fun a => f (s a)
    induction y using Finsupp.induction_linear with
    | zero => simp only [SymAlgebra.act, map_zero, MultilinearMap.zero_apply]
    | add y z hy hz =>
      simp only [SymAlgebra.act, map_add, MultilinearMap.add_apply] at hy hz ⊢
      rw [hy, hz]
    | single y c =>
      obtain ⟨x, rfl⟩ := Pres.mk_surjective y
      rw [show Finsupp.single (Pres.mk x) c = c • Finsupp.single (Pres.mk (ρ := ρ) x) (1 : R) by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
      simp only [SymAlgebra.act, map_smul, MultilinearMap.smul_apply]
      exact congrArg (c • ·) (Pres.act_mk_of_gen (α := α.comp I.projHom)
        (β := β.comp I.projHom) h x s)

end Generators

/-! ## `Lie`-algebras and Lie algebras -/

namespace LieAlg

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V] (a : LieAlg R V)

/-- The bracket of a `Lie`-algebra. -/
def br (x y : V) : V := a.bracket ![x, y]

lemma br_add_left (x y z : V) : a.br (x + y) z = a.br x z + a.br y z := by
  have h := a.bracket.map_update_add ![x, z] 0 x y
  simp only [show ∀ t : V, Function.update ![x, z] 0 t = ![t, z] from fun t => by
    funext k
    fin_cases k <;> rfl] at h
  exact h

lemma br_add_right (x y z : V) : a.br x (y + z) = a.br x y + a.br x z := by
  have h := a.bracket.map_update_add ![x, y] 1 y z
  simp only [show ∀ t : V, Function.update ![x, y] 1 t = ![x, t] from fun t => by
    funext k
    fin_cases k <;> rfl] at h
  exact h

lemma br_smul_left (c : R) (x y : V) : a.br (c • x) y = c • a.br x y := by
  have h := a.bracket.map_update_smul ![x, y] 0 c x
  simp only [show ∀ t : V, Function.update ![x, y] 0 t = ![t, y] from fun t => by
    funext k
    fin_cases k <;> rfl] at h
  exact h

lemma br_smul_right (c : R) (x y : V) : a.br x (c • y) = c • a.br x y := by
  have h := a.bracket.map_update_smul ![x, y] 1 c y
  simp only [show ∀ t : V, Function.update ![x, y] 1 t = ![x, t] from fun t => by
    funext k
    fin_cases k <;> rfl] at h
  exact h

lemma br_antisymm (x y : V) : a.br x y = -a.br y x := a.antisymm x y

lemma br_neg_left (x y : V) : a.br (-x) y = -a.br x y := by
  rw [← neg_one_smul R x, br_smul_left, neg_one_smul]

/-- **Antisymmetry gives `[x, x] = 0`** when `2` is invertible. -/
lemma br_self [Invertible (2 : R)] (x : V) : a.br x x = 0 := by
  have h : (2 : R) • a.br x x = 0 := by
    rw [two_smul]
    nth_rewrite 1 [a.br_antisymm]
    exact neg_add_cancel _
  calc a.br x x = ((⅟2 : R) * 2) • a.br x x := by rw [invOf_mul_self, one_smul]
    _ = (⅟2 : R) • ((2 : R) • a.br x x) := by rw [smul_smul]
    _ = 0 := by rw [h, smul_zero]

/-- **The Leibniz form of the Jacobi identity.** -/
lemma br_leibniz (x y z : V) : a.br x (a.br y z) = a.br (a.br x y) z + a.br y (a.br x z) := by
  have hj : a.br (a.br x y) z + a.br (a.br y z) x + a.br (a.br z x) y = 0 := a.jacobi x y z
  have e₂ : a.br y (a.br x z) = a.br (a.br z x) y := by
    rw [a.br_antisymm y, a.br_antisymm x z, br_neg_left, neg_neg]
  rw [a.br_antisymm x (a.br y z), e₂]
  exact neg_eq_of_add_eq_zero_left ((add_right_comm _ _ _).trans hj)

/-- **The Lie ring of a `Lie`-algebra**, when `2` is invertible. -/
abbrev toLieRing [Invertible (2 : R)] : LieRing V :=
  { ‹AddCommGroup V› with
    bracket := a.br
    add_lie := a.br_add_left
    lie_add := a.br_add_right
    lie_self := a.br_self
    leibniz_lie := a.br_leibniz }

/-- **The Lie algebra of a `Lie`-algebra**, when `2` is invertible. -/
abbrev toLieAlgebra [Invertible (2 : R)] : @LieAlgebra R V _ a.toLieRing :=
  letI := a.toLieRing
  { ‹Module R V› with lie_smul := fun c x y => a.br_smul_right c x y }

omit a in
@[ext] lemma ext {a b : LieAlg R V} (h : a.bracket = b.bracket) : a = b := by
  cases a
  cases b
  cases h
  rfl

section OfLieAlgebra

variable (L : Type w) [LieRing L] [LieAlgebra R L]

/-- The bracket of a Lie algebra, as a bilinear operation. -/
def lieML : EndOp R L (Fin 2) :=
  MultilinearMap.mk' (fun v => ⁅v 0, v 1⁆)
    (fun v i x y => by fin_cases i <;> simp [add_lie, lie_add])
    (fun v i c x => by fin_cases i <;> simp [smul_lie, lie_smul])

variable (R) in
/-- **The `Lie`-algebra of a Lie algebra.** -/
def ofLieAlgebra : LieAlg R L where
  bracket := lieML L
  antisymm x y := (lie_skew x y).symm
  jacobi x y z := by
    show ⁅⁅x, y⁆, z⁆ + ⁅⁅y, z⁆, x⁆ + ⁅⁅z, x⁆, y⁆ = 0
    rw [← lie_skew ⁅x, y⁆ z, ← lie_skew ⁅y, z⁆ x, ← lie_skew ⁅z, x⁆ y]
    calc -⁅z, ⁅x, y⁆⁆ + -⁅x, ⁅y, z⁆⁆ + -⁅y, ⁅z, x⁆⁆
        = -(⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆) := by abel
      _ = 0 := by rw [lie_jacobi, neg_zero]

lemma ofLieAlgebra_br (x y : L) : (ofLieAlgebra R L).br x y = ⁅x, y⁆ := rfl

/-- **The Lie ring of the `Lie`-algebra of a Lie algebra is that Lie ring.** -/
theorem toLieRing_ofLieAlgebra [Invertible (2 : R)] :
    (ofLieAlgebra R L).toLieRing = ‹LieRing L› :=
  rfl

/-- **The Lie algebra of the `Lie`-algebra of a Lie algebra is that Lie algebra.** -/
theorem toLieAlgebra_ofLieAlgebra [Invertible (2 : R)] :
    (ofLieAlgebra R L).toLieAlgebra = ‹LieAlgebra R L› :=
  rfl

end OfLieAlgebra

/-- **The `Lie`-algebra of the Lie algebra of a `Lie`-algebra is that `Lie`-algebra.** -/
theorem ofLieAlgebra_toLieAlgebra [Invertible (2 : R)] :
    letI := a.toLieRing
    letI := a.toLieAlgebra
    ofLieAlgebra R V = a := by
  letI := a.toLieRing
  letI := a.toLieAlgebra
  refine ext (MultilinearMap.ext fun v => ?_)
  conv_rhs => rw [EndOp.vec_two v]
  rfl

end LieAlg

/-! ## Morphisms of `Lie`-algebras -/

section Hom

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
  {W : Type x} [AddCommGroup W] [Module R W]

variable (R) in
/-- **The bracket of the Lie operad.** -/
noncomputable def Lie.bracket : Lie R (Fin 2) :=
  (SymOperadIdeal.span R (rel23 {BinRel.antisymm R ()} {BinRel.jacobi R ()})).proj _
    (Finsupp.single (Pres.gen (BinGen.op ())) 1)

/-- **The bracket of the operad acts as the bracket of the `Lie`-algebra.** -/
lemma Lie.act_bracket (α : SymAlgebra R (Lie R) V) (x y : V) :
    α.act (Lie.bracket R) ![x, y] = (Lie.algebraEquiv α).br x y :=
  rfl

/-- **Morphisms of `Lie`-algebras are the linear maps preserving the bracket.** -/
noncomputable def Lie.homEquiv (α : SymAlgebra R (Lie R) V) (β : SymAlgebra R (Lie R) W) :
    SymAlgebraHom α β ≃ {f : V →ₗ[R] W //
      ∀ x y, f ((Lie.algebraEquiv α).br x y) = (Lie.algebraEquiv β).br (f x) (f y)} where
  toFun F := ⟨F.toLinearMap, fun x y => by
    rw [← Lie.act_bracket, ← Lie.act_bracket, F.map_act]
    congr 1
    funext k
    fin_cases k <;> rfl⟩
  invFun f := SymOperadIdeal.algHomOfGen _ f.1 fun n g s => by
    cases g
    show f.1 (α.act (Lie.bracket R) s) = β.act (Lie.bracket R) fun k => f.1 (s k)
    rw [EndOp.vec_two (fun k => f.1 (s k)), EndOp.vec_two s]
    exact f.2 (s 0) (s 1)
  left_inv _ := rfl
  right_inv _ := rfl

lemma LieAlg.br_symm_ofLieAlgebra (L : Type w) [LieRing L] [LieAlgebra R L] (x y : L) :
    (Lie.algebraEquiv (Lie.algebraEquiv.symm (LieAlg.ofLieAlgebra R L))).br x y = ⁅x, y⁆ := by
  rw [Equiv.apply_symm_apply]
  rfl

/-- **Morphisms of `Lie`-algebras between Lie algebras are the Lie algebra morphisms.** -/
noncomputable def LieAlg.homEquiv (L : Type w) [LieRing L] [LieAlgebra R L] (L' : Type x)
    [LieRing L'] [LieAlgebra R L'] :
    SymAlgebraHom (Lie.algebraEquiv.symm (LieAlg.ofLieAlgebra R L))
      (Lie.algebraEquiv.symm (LieAlg.ofLieAlgebra R L')) ≃ (L →ₗ⁅R⁆ L') :=
  (Lie.homEquiv _ _).trans
    { toFun := fun f =>
        { f.1 with
          map_lie' := fun {x y} => by
            have h := f.2 x y
            rw [LieAlg.br_symm_ofLieAlgebra, LieAlg.br_symm_ofLieAlgebra] at h
            exact h }
      invFun := fun f => ⟨f.toLinearMap, fun x y => by
        rw [LieAlg.br_symm_ofLieAlgebra, LieAlg.br_symm_ofLieAlgebra]
        exact f.map_lie x y⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Hom

/-! ## The free `Lie`-algebra -/

namespace Schur

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {V : Type v} [AddCommGroup V]
  [Module R V]

noncomputable instance instLieRingLie : LieRing (Schur R (Lie R) V) :=
  (Lie.algebraEquiv (algebra R (Lie R) V)).toLieRing

noncomputable instance instLieAlgebraLie : LieAlgebra R (Schur R (Lie R) V) :=
  (Lie.algebraEquiv (algebra R (Lie R) V)).toLieAlgebra

/-- In the free `Lie`-algebra, the bracket of the operad acts as the Lie bracket. -/
lemma act_bracket (x y : Schur R (Lie R) V) : act (Lie.bracket R) ![x, y] = ⁅x, y⁆ :=
  rfl

variable {L : Type w} [LieRing L] [LieAlgebra R L]

/-- The Lie algebra morphism of a morphism of `Lie`-algebras out of the free `Lie`-algebra. -/
noncomputable def lieHomOf
    (F : SymAlgebraHom (algebra R (Lie R) V) (Lie.algebraEquiv.symm (LieAlg.ofLieAlgebra R L))) :
    Schur R (Lie R) V →ₗ⁅R⁆ L :=
  { F.toLinearMap with
    map_lie' := fun {x y} => by
      have h := (Lie.homEquiv _ _ F).2 x y
      rw [LieAlg.br_symm_ofLieAlgebra] at h
      exact h }

@[simp] lemma lieHomOf_apply
    (F : SymAlgebraHom (algebra R (Lie R) V) (Lie.algebraEquiv.symm (LieAlg.ofLieAlgebra R L)))
    (x : Schur R (Lie R) V) : lieHomOf F x = F.toLinearMap x :=
  rfl

/-- The morphism of `Lie`-algebras of a Lie algebra morphism out of the free `Lie`-algebra. -/
noncomputable def lieAlgHom (f : Schur R (Lie R) V →ₗ⁅R⁆ L) :
    SymAlgebraHom (algebra R (Lie R) V) (Lie.algebraEquiv.symm (LieAlg.ofLieAlgebra R L)) :=
  (Lie.homEquiv _ _).symm ⟨f.toLinearMap, fun x y => by
    rw [LieAlg.br_symm_ofLieAlgebra]
    exact f.map_lie x y⟩

@[simp] lemma lieAlgHom_toLinearMap (f : Schur R (Lie R) V →ₗ⁅R⁆ L) :
    (lieAlgHom f).toLinearMap = f.toLinearMap :=
  rfl

/-- **Lie algebra morphisms out of the free `Lie`-algebra agree when they agree on
generators.** -/
theorem lieHom_ext {f g : Schur R (Lie R) V →ₗ⁅R⁆ L}
    (h : ∀ v, f (ι R (Lie R) V v) = g (ι R (Lie R) V v)) : f = g := by
  have := algHom_ext (F := lieAlgHom f) (G := lieAlgHom g) h
  exact LieHom.ext fun x => congrArg (fun F => F.toLinearMap x) this

/-- **The universal property of the free `Lie`-algebra among Lie algebras**: Lie algebra
morphisms out of it are the linear maps out of `V`. -/
noncomputable def lieLift : (V →ₗ[R] L) ≃ (Schur R (Lie R) V →ₗ⁅R⁆ L) where
  toFun φ := lieHomOf (liftHom _ φ)
  invFun f := f.toLinearMap ∘ₗ ι R (Lie R) V
  left_inv φ := LinearMap.ext fun v => liftHom_ι _ φ v
  right_inv _ := lieHom_ext fun v => liftHom_ι _ _ v

@[simp] lemma lieLift_ι (φ : V →ₗ[R] L) (v : V) : lieLift φ (ι R (Lie R) V v) = φ v :=
  liftHom_ι _ φ v

section Free

variable (R) (X : Type w)

/-- The Lie algebra morphism from the free `Lie`-algebra on `X →₀ R` to the free Lie algebra on
`X`. -/
noncomputable def toFreeLie : Schur R (Lie R) (X →₀ R) →ₗ⁅R⁆ FreeLieAlgebra R X :=
  lieLift (Finsupp.linearCombination R (FreeLieAlgebra.of R))

/-- The Lie algebra morphism from the free Lie algebra on `X` to the free `Lie`-algebra on
`X →₀ R`. -/
noncomputable def ofFreeLie : FreeLieAlgebra R X →ₗ⁅R⁆ Schur R (Lie R) (X →₀ R) :=
  FreeLieAlgebra.lift R fun x => ι R (Lie R) _ (Finsupp.single x 1)

theorem toFreeLie_comp_ofFreeLie : (toFreeLie R X).comp (ofFreeLie R X) = LieHom.id := by
  refine FreeLieAlgebra.hom_ext fun x => ?_
  rw [LieHom.comp_apply, ofFreeLie, FreeLieAlgebra.lift_of_apply, toFreeLie, lieLift_ι,
    Finsupp.linearCombination_single, one_smul, LieHom.id_apply]

theorem ofFreeLie_comp_toFreeLie : (ofFreeLie R X).comp (toFreeLie R X) = LieHom.id := by
  refine lieHom_ext fun v => ?_
  rw [LieHom.comp_apply, LieHom.id_apply, toFreeLie, lieLift_ι]
  induction v using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero]
  | add v w hv hw => rw [map_add, map_add, hv, hw, map_add]
  | single x c =>
    rw [Finsupp.linearCombination_single, map_smul, ofFreeLie, FreeLieAlgebra.lift_of_apply,
      ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- **The free `Lie`-algebra on the free module on `X` is the free Lie algebra on `X`**, when `2`
is invertible. -/
noncomputable def freeLieAlgebraEquiv : FreeLieAlgebra R X ≃ₗ⁅R⁆ Schur R (Lie R) (X →₀ R) :=
  { ofFreeLie R X with
    invFun := toFreeLie R X
    left_inv := LieHom.congr_fun (toFreeLie_comp_ofFreeLie R X)
    right_inv := LieHom.congr_fun (ofFreeLie_comp_toFreeLie R X) }

lemma freeLieAlgebraEquiv_of (x : X) :
    freeLieAlgebraEquiv R X (FreeLieAlgebra.of R x) = ι R (Lie R) _ (Finsupp.single x 1) :=
  FreeLieAlgebra.lift_of_apply _ _

end Free

end Schur

end Operad
