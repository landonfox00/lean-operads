/-
# The endomorphism operad, and algebras over a symmetric operad

For an `R`-module `V`, the endomorphism operad `EndOp R V` has the multilinear maps `V^A → V` as its
operations with inputs `A`: relabelling precomposes with the bijection, the unit is the identity of
`V`, and `f ∘ᵢ g` feeds the value of `g` into the input `i` of `f`. A morphism of operads
`P → EndOp R V` is a `P`-algebra structure on `V` (`SymAlgebra`).
-/
import Operad.Sym
import Mathlib.LinearAlgebra.Multilinear.Basic

universe u v w

namespace Operad

namespace Sym

section Feed

variable {V : Type v} {A B : Type} [DecidableEq A]

/-- The arguments of the outer operation when `w` is fed into its input `i`, the other inputs
being read off `v`. -/
def feed (i : A) (v : Without A i ⊕ B → V) (w : V) : A → V :=
  fun a => if h : a = i then w else v (Sum.inl ⟨a, h⟩)

@[simp] lemma feed_self (i : A) (v : Without A i ⊕ B → V) (w : V) : feed i v w i = w :=
  dif_pos rfl

lemma feed_of_ne {i a : A} (h : a ≠ i) (v : Without A i ⊕ B → V) (w : V) :
    feed i v w a = v (Sum.inl ⟨a, h⟩) :=
  dif_neg h

@[simp] lemma feed_val (i : A) (v : Without A i ⊕ B → V) (w : V) (a : Without A i) :
    feed i v w a.1 = v (Sum.inl a) :=
  dif_neg a.2

lemma feed_eq_update [Zero V] (i : A) (v : Without A i ⊕ B → V) (w : V) :
    feed i v w = Function.update (feed i v 0) i w := by
  funext a
  by_cases h : a = i
  · subst h
    simp
  · rw [Function.update_of_ne h, feed_of_ne h, feed_of_ne h]

variable [DecidableEq B]

lemma feed_update_inl (i : A) (v : Without A i ⊕ B → V) (w : V) (a : Without A i) (z : V) :
    feed i (Function.update v (Sum.inl a) z) w = Function.update (feed i v w) a.1 z := by
  funext c
  by_cases h : c = i
  · subst h
    rw [feed_self, Function.update_of_ne (Ne.symm a.2), feed_self]
  · rw [feed_of_ne h]
    by_cases hc : c = a.1
    · subst hc
      simp
    · rw [Function.update_of_ne (fun e => hc (congrArg Subtype.val (Sum.inl_injective e))),
        Function.update_of_ne hc, feed_of_ne h]

lemma feed_update_inr (i : A) (v : Without A i ⊕ B → V) (w : V) (b : B) (z : V) :
    feed i (Function.update v (Sum.inr b) z) w = feed i v w := by
  funext c
  by_cases h : c = i
  · subst h
    simp
  · rw [feed_of_ne h, feed_of_ne h, Function.update_of_ne Sum.inl_ne_inr]

end Feed

section EndOp

variable (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V] [Module R V]

/-- **The endomorphism operad** of an `R`-module `V`: the multilinear maps `V^A → V`. -/
@[nolint unusedArguments]
abbrev EndOp (A : Type) [Fintype A] [DecidableEq A] : Type v :=
  MultilinearMap R (fun _ : A => V) V

variable {A A' B : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype B]
  [DecidableEq B]

omit [AddCommGroup V] [Fintype A] [Fintype B] in
private lemma inr_update_inl {i : A} (v : Without A i ⊕ B → V) (a : Without A i) (z : V) :
    (fun b => Function.update v (Sum.inl a) z (Sum.inr b)) = fun b => v (Sum.inr b) :=
  funext fun _ => Function.update_of_ne Sum.inr_ne_inl _ _

omit [AddCommGroup V] [Fintype A] [Fintype B] in
private lemma inr_update_inr {i : A} (v : Without A i ⊕ B → V) (b : B) (z : V) :
    (fun b' => Function.update v (Sum.inr b) z (Sum.inr b'))
      = Function.update (fun b' => v (Sum.inr b')) b z :=
  Function.update_comp_eq_of_injective v Sum.inr_injective b z

/-- **Feed `g` into the input `i` of `f`.** -/
def EndOp.compML (i : A) (f : EndOp R V A) (g : EndOp R V B) : EndOp R V (Without A i ⊕ B) :=
  MultilinearMap.mk' (fun v => f (feed i v (g fun b => v (Sum.inr b))))
    (fun v c x y => by
      rcases c with a | b
      · simp only [inr_update_inl, feed_update_inl]
        exact f.map_update_add _ _ _ _
      · simp only [inr_update_inr, feed_update_inr, g.map_update_add]
        rw [feed_eq_update, f.map_update_add, ← feed_eq_update, ← feed_eq_update])
    (fun v c r x => by
      rcases c with a | b
      · simp only [inr_update_inl, feed_update_inl]
        exact f.map_update_smul _ _ _ _
      · simp only [inr_update_inr, feed_update_inr, g.map_update_smul]
        rw [feed_eq_update, f.map_update_smul, ← feed_eq_update])

@[simp] lemma EndOp.compML_apply (i : A) (f : EndOp R V A) (g : EndOp R V B)
    (v : Without A i ⊕ B → V) :
    EndOp.compML R V i f g v = f (feed i v (g fun b => v (Sum.inr b))) := rfl

/-- Composition, bilinearly. -/
def EndOp.compL (i : A) : EndOp R V A →ₗ[R] EndOp R V B →ₗ[R] EndOp R V (Without A i ⊕ B) :=
  LinearMap.mk₂ R (EndOp.compML R V i)
    (fun _ _ _ => MultilinearMap.ext fun _ => rfl)
    (fun _ _ _ => MultilinearMap.ext fun _ => rfl)
    (fun f g g' => MultilinearMap.ext fun v => by
      simp only [EndOp.compML_apply, MultilinearMap.add_apply]
      rw [feed_eq_update, f.map_update_add, ← feed_eq_update, ← feed_eq_update])
    (fun r f g => MultilinearMap.ext fun v => by
      simp only [EndOp.compML_apply, MultilinearMap.smul_apply]
      rw [feed_eq_update, f.map_update_smul, ← feed_eq_update])

/-- Relabelling: precompose with the bijection. -/
def EndOp.mapL (e : A ≃ A') : EndOp R V A →ₗ[R] EndOp R V A' where
  toFun f := f.domDomCongr e
  map_add' _ _ := MultilinearMap.ext fun _ => rfl
  map_smul' _ _ := MultilinearMap.ext fun _ => rfl

@[simp] lemma EndOp.mapL_apply (e : A ≃ A') (f : EndOp R V A) (v : A' → V) :
    EndOp.mapL R V e f v = f fun a => v (e a) := rfl

/-- The unit: the identity of `V`. -/
def EndOp.one : EndOp R V Unit := MultilinearMap.ofSubsingleton R V V () LinearMap.id

@[simp] lemma EndOp.one_apply (v : Unit → V) : EndOp.one R V v = v () := rfl

/-- **The endomorphism operad is a symmetric operad.** -/
instance instSymOperadEndOp : SymOperad R (EndOp R V) where
  map e := EndOp.mapL R V e
  map_refl _ := MultilinearMap.ext fun _ => rfl
  map_trans _ _ _ := MultilinearMap.ext fun _ => rfl
  one := EndOp.one R V
  comp i := EndOp.compL R V i
  map_comp := by
    intro A A' B B' _ _ _ _ _ _ _ _ σ τ i x y
    refine MultilinearMap.ext fun v => ?_
    show EndOp.compML R V i x y _ = EndOp.mapL R V σ x _
    simp only [EndOp.compML_apply, EndOp.mapL_apply, compEquiv_inr]
    congr 1
    funext a
    by_cases h : a = i
    · subst h
      simp
    · rw [feed_of_ne h, feed_of_ne (fun e => h (σ.injective e)), compEquiv_inl]
  comp_one := by
    intro A _ _ i x
    refine MultilinearMap.ext fun v => ?_
    show EndOp.compML R V i x (EndOp.one R V) _ = x v
    simp only [EndOp.compML_apply, EndOp.one_apply, rightUnitEquiv_inr]
    congr 1
    funext a
    by_cases h : a = i
    · subst h
      simp
    · rw [feed_of_ne h, rightUnitEquiv_inl]
  one_comp := by
    intro B _ _ y
    refine MultilinearMap.ext fun v => ?_
    show EndOp.mapL R V (leftUnitEquiv B) (EndOp.compL R V () (EndOp.one R V) y) v = y v
    rw [EndOp.mapL_apply]
    show EndOp.compML R V () (EndOp.one R V) y (fun c => v (leftUnitEquiv B c)) = y v
    simp only [EndOp.compML_apply, EndOp.one_apply, feed_self, leftUnitEquiv_inr]
  comp_assoc_seq := by
    intro A B D _ _ _ _ _ _ i j x y z
    refine MultilinearMap.ext fun v => ?_
    show EndOp.compML R V (Sum.inr j) (EndOp.compML R V i x y) z _
      = EndOp.compML R V i x (EndOp.compML R V j y z) v
    simp only [EndOp.compML_apply, seqEquiv_inr]
    congr 1
    funext a
    by_cases h : a = i
    · subst h
      simp only [feed_self]
      congr 1
      funext b
      by_cases hb : b = j
      · subst hb
        simp only [feed_self]
      · simp only [feed_of_ne (show (Sum.inr b : Without A a ⊕ B) ≠ Sum.inr j from
          fun e => hb (Sum.inr_injective e)), feed_of_ne hb, seqEquiv_inl_inr]
    · simp only [feed_of_ne h, feed_of_ne (show (Sum.inl ⟨a, h⟩ : Without A i ⊕ B) ≠ Sum.inr j
        from Sum.inl_ne_inr), seqEquiv_inl_inl]
  comp_assoc_par := by
    intro A B D _ _ _ _ _ _ i k hik x y z
    refine MultilinearMap.ext fun v => ?_
    show EndOp.compML R V (Sum.inl ⟨k, Ne.symm hik⟩) (EndOp.compML R V i x y) z _
      = EndOp.compML R V (Sum.inl ⟨i, hik⟩) (EndOp.compML R V k x z) y v
    simp only [EndOp.compML_apply, parEquiv_inr]
    congr 1
    funext a
    by_cases hai : a = i
    · rw [hai, feed_self, feed_of_ne hik, feed_self]
      congr 1
    · by_cases hak : a = k
      · rw [hak, feed_of_ne (Ne.symm hik), feed_self, feed_self]
        congr 1
      · rw [feed_of_ne hai, feed_of_ne hak,
          feed_of_ne (show (Sum.inl ⟨a, hai⟩ : Without A i ⊕ B) ≠ Sum.inl ⟨k, Ne.symm hik⟩ from
            fun e => hak (congrArg Subtype.val (Sum.inl_injective e))),
          feed_of_ne (show (Sum.inl ⟨a, hak⟩ : Without A k ⊕ D) ≠ Sum.inl ⟨i, hik⟩ from
            fun e => hai (congrArg Subtype.val (Sum.inl_injective e)))]
        simp only [parEquiv_inl_inl]

/-! ## Algebras over a symmetric operad -/

variable {R V}

variable (R) in
/-- **An algebra over a symmetric operad** `P` on the module `V`: a morphism of operads into the
endomorphism operad. -/
abbrev SymAlgebra (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P] (V : Type v)
    [AddCommGroup V] [Module R V] :=
  SymOperadHom R P (EndOp R V)

variable {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]

/-- The action of an operation on a family of elements. -/
def SymAlgebra.act (α : SymAlgebra R P V) (x : P A) (v : A → V) : V := α.app A x v

/-- **Composites act by substitution.** -/
lemma SymAlgebra.act_comp (α : SymAlgebra R P V) (i : A) (x : P A) (y : P B)
    (v : Without A i ⊕ B → V) :
    α.act (SymOperad.comp (R := R) i x y) v
      = α.act x (feed i v (α.act y fun b => v (Sum.inr b))) := by
  unfold SymAlgebra.act
  rw [α.app_comp]
  rfl

/-- **Relabelled operations act on relabelled families.** -/
lemma SymAlgebra.act_map (α : SymAlgebra R P V) (e : A ≃ A') (x : P A) (v : A' → V) :
    α.act (SymOperad.map (R := R) e x) v = α.act x fun a => v (e a) := by
  unfold SymAlgebra.act
  rw [α.app_map]
  rfl

/-- The unit acts as the identity. -/
lemma SymAlgebra.act_one (α : SymAlgebra R P V) (v : Unit → V) :
    α.act (SymOperad.one R) v = v () := by
  unfold SymAlgebra.act
  rw [α.app_one]
  rfl

end EndOp

end Sym

end Operad
