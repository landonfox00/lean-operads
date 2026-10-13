/-
# The underlying non-symmetric operad of a symmetric operad

A symmetric operad `P` in the sense of `Operad.Sym` has inputs indexed by arbitrary finite types.
Restricting to the types `Fin n` and composing positionally gives a non-symmetric operad in the
convention of `Operad.Basic`,

  `comp a b x y = relabel (comp ⟨a⟩ x y)` along `insertEquiv a b n`,

where `insertEquiv a b n : Without (Fin (a+1+b)) a ⊕ Fin n ≃ Fin (a+n+b)` keeps the outer inputs
before the slot in place, puts the inserted inputs in the block `[a, a+n)`, and shifts the outer
inputs after the slot by `n - 1`. This is the forgetful functor from symmetric to non-symmetric
operads, and it is how a symmetric operad reaches the computational layer of the library.

Each non-symmetric axiom reduces, through the symmetric axiom of the same name and the
equivariance axiom, to an identity between two bijections of finite types, which is checked
pointwise by arithmetic on `Fin`. That is where all the positional bookkeeping lives, once.
-/
import Operad.Sym
import Operad.Constructions
import Operad.Perm

universe u v w

namespace Operad

namespace Sym

/-! ## Positional bijections -/

/-- **The positional insertion bijection.** The inputs of `x ∘ₐ y`, for `x` with `a + 1 + b`
inputs and `y` with `n`, in their order: outer inputs before the slot, then the inserted ones, then
the outer inputs after the slot. -/
def insertEquiv (a b n : ℕ) :
    Without (Fin (a + 1 + b)) ⟨a, by omega⟩ ⊕ Fin n ≃ Fin (a + n + b) where
  toFun x :=
    match x with
    | Sum.inl k =>
        if h : (k.1 : ℕ) < a then ⟨k.1, by omega⟩
        else ⟨k.1 + n - 1, by
          have hk : (k.1 : ℕ) ≠ a := fun e => k.2 (Fin.ext e)
          have := k.1.isLt
          omega⟩
    | Sum.inr j => ⟨a + j, by have := j.isLt; omega⟩
  invFun m :=
    if h : (m : ℕ) < a then
      Sum.inl ⟨⟨m, by omega⟩, fun e => by
        have := congrArg Fin.val e; simp only at this; omega⟩
    else if h' : (m : ℕ) < a + n then Sum.inr ⟨m - a, by omega⟩
    else
      Sum.inl ⟨⟨m - n + 1, by have := m.isLt; omega⟩, fun e => by
        have := congrArg Fin.val e; simp only at this; omega⟩
  left_inv := by
    rintro (⟨⟨k, hk⟩, hne⟩ | ⟨j, hj⟩)
    · have hka : k ≠ a := fun e => hne (Fin.ext e)
      by_cases h : k < a
      · simp only [h, ↓reduceDIte]
      · have h1 : ¬ k + n - 1 < a := by omega
        have h2 : ¬ k + n - 1 < a + n := by omega
        simp only [h, h1, h2, ↓reduceDIte, Sum.inl.injEq, Subtype.mk.injEq, Fin.mk.injEq]
        omega
    · have h1 : ¬ a + j < a := by omega
      have h2 : a + j < a + n := by omega
      simp only [h1, h2, ↓reduceDIte, Sum.inr.injEq, Fin.mk.injEq]
      omega
  right_inv := by
    rintro ⟨m, hm⟩
    by_cases h : m < a
    · simp only [h, ↓reduceDIte]
    · by_cases h' : m < a + n
      · simp only [h, h', ↓reduceDIte, Fin.mk.injEq]
        omega
      · have h3 : ¬ m - n + 1 < a := by omega
        simp only [h, h', h3, ↓reduceDIte, Fin.mk.injEq]
        omega

lemma insertEquiv_inl_val (a b n : ℕ) (k : Without (Fin (a + 1 + b)) ⟨a, by omega⟩) :
    ((insertEquiv a b n (Sum.inl k) : Fin (a + n + b)) : ℕ)
      = if (k.1 : ℕ) < a then (k.1 : ℕ) else (k.1 : ℕ) + n - 1 := by
  show ((if h : (k.1 : ℕ) < a then _ else _ : Fin (a + n + b)) : ℕ) = _
  split_ifs <;> rfl

@[simp] lemma insertEquiv_inr_val (a b n : ℕ) (j : Fin n) :
    ((insertEquiv a b n (Sum.inr j) : Fin (a + n + b)) : ℕ) = a + j := rfl

end Sym

open Sym

namespace SymOperad

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]

/-! ## Moving relabellings through a composition -/

section Moves

variable {A A' B B' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']

lemma comp_map_left (σ : A ≃ A') (i : A) (x : P A) (y : P B) :
    comp (R := R) (σ i) (map (R := R) σ x) y
      = map (R := R) (compEquiv σ (Equiv.refl B) i) (comp (R := R) i x y) := by
  rw [map_comp (R := R), map_refl (R := R)]

lemma comp_map_right (τ : B ≃ B') (i : A) (x : P A) (y : P B) :
    comp (R := R) i x (map (R := R) τ y)
      = map (R := R) (Equiv.sumCongr (Equiv.refl (Without A i)) τ) (comp (R := R) i x y) := by
  have h := map_comp (R := R) (P := P) (Equiv.refl A) τ i x y
  rw [map_refl (R := R)] at h
  have e : compEquiv (Equiv.refl A) τ i = Equiv.sumCongr (Equiv.refl (Without A i)) τ := by
    ext c; rcases c with a | b <;> rfl
  rw [e] at h
  exact h.symm

omit [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] in
lemma comp_slot {i i' : A} (h : i = i') (x : P A) (y : P B) :
    comp (R := R) i' x y = map (R := R) (slotEquiv h) (comp (R := R) i x y) := by
  subst h
  have e : slotEquiv (B := B) (rfl : i = i) = Equiv.refl _ := by
    ext c; rcases c with ⟨a, ha⟩ | b <;> rfl
  rw [e, map_refl (R := R)]

end Moves

/-! ## The underlying non-symmetric operad -/

/-- **The underlying non-symmetric collection**: the components on the standard finite types.

A `def`, not an `abbrev`: for `P = Perm` the collection `n ↦ Fin n → R` is literally the
non-symmetric `Perm`, and an `abbrev` would let instance resolution pick that operad's structure
instead of this one. -/
def toNS (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v) : ℕ → Type v :=
  fun n => P (Fin n)

instance (n : ℕ) : AddCommGroup (toNS P n) := inferInstanceAs (AddCommGroup (P (Fin n)))

instance (n : ℕ) : Module R (toNS P n) := inferInstanceAs (Module R (P (Fin n)))

/-- Positional composition: compose at the input `a`, then list the inputs in order. -/
def nsComp (a b : ℕ) {n : ℕ} :
    P (Fin (a + 1 + b)) →ₗ[R] P (Fin n) →ₗ[R] P (Fin (a + n + b)) :=
  (comp (R := R) (⟨a, by omega⟩ : Fin (a + 1 + b))).compr₂ (map (R := R) (insertEquiv a b n))

lemma nsComp_apply (a b : ℕ) {n : ℕ} (x : P (Fin (a + 1 + b))) (y : P (Fin n)) :
    nsComp (R := R) a b x y
      = map (R := R) (insertEquiv a b n) (comp (R := R) (⟨a, by omega⟩ : Fin (a + 1 + b)) x y) :=
  rfl

/-- The unit on the standard one-element type. -/
def nsOne : P (Fin 1) := map (R := R) unitFinOne (one R)

/-- Reindexing along an equality of arities is relabelling along `finCongr`. -/
lemma reindex_toNS {m n : ℕ} (h : m = n) (x : P (Fin m)) :
    reindex R (toNS P) h x = map (R := R) (finCongr h) x := by
  subst h
  rw [finCongr_refl, map_refl (R := R)]
  rfl

/-- Two relabellings of the same element agree as soon as the bijections do. -/
lemma map_eq_of_equiv_eq {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {e f : A ≃ B} (h : ∀ a, e a = f a) (x : P A) : map (R := R) e x = map (R := R) f x := by
  rw [Equiv.ext h]

theorem nsComp_one_right (a b : ℕ) (x : P (Fin (a + 1 + b))) :
    nsComp (R := R) a b x (nsOne (R := R)) = x := by
  rw [nsComp_apply, nsOne, comp_map_right, comp_one', map_map, map_map]
  conv_rhs => rw [← map_refl (R := R) x]
  refine map_eq_of_equiv_eq (fun k => Fin.ext ?_) x
  simp only [Equiv.trans_apply, Equiv.refl_apply]
  by_cases hk : k = ⟨a, by omega⟩
  · subst hk
    rw [rightUnitEquiv_symm_self]
    simp [unitFinOne]
  · have hka : (k : ℕ) ≠ a := fun e => hk (Fin.ext e)
    rw [rightUnitEquiv_symm_of_ne hk, Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply,
      insertEquiv_inl_val]
    dsimp only
    split_ifs <;> omega

theorem nsComp_one_left {n : ℕ} (x : P (Fin n)) :
    reindex R (toNS P) (by omega) (nsComp (R := R) 0 0 (nsOne (R := R)) x) = x := by
  rw [reindex_toNS, nsComp_apply, nsOne]
  have hc : comp (R := R) (⟨0, by omega⟩ : Fin (0 + 1 + 0)) (map (R := R) unitFinOne (one R)) x
      = map (R := R) (compEquiv unitFinOne (Equiv.refl (Fin n)) ())
          (comp (R := R) () (one R) x) :=
    comp_map_left (R := R) unitFinOne () (one R) x
  rw [hc, one_comp', map_map, map_map]
  erw [map_map]
  conv_rhs => rw [← map_refl (R := R) x]
  refine map_eq_of_equiv_eq (fun k => Fin.ext ?_) x
  show 0 + (k : ℕ) = k
  omega

/-- Sequential associativity, with the relabelling moved to the other side. -/
lemma comp_assoc_seq' {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] (i : A) (j : B) (x : P A) (y : P B) (z : P D) :
    comp (R := R) (Sum.inr j) (comp (R := R) i x y) z
      = map (R := R) (seqEquiv i j D).symm (comp (R := R) i x (comp (R := R) j y z)) := by
  rw [← comp_assoc_seq (R := R) i j x y z, map_symm_map]

/-- Parallel associativity, with the relabelling moved to the other side. -/
lemma comp_assoc_par' {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] {i k : A} (hik : i ≠ k) (x : P A) (y : P B) (z : P D) :
    comp (R := R) (Sum.inl ⟨k, Ne.symm hik⟩) (comp (R := R) i x y) z
      = map (R := R) (parEquiv hik B D).symm
          (comp (R := R) (Sum.inl ⟨i, hik⟩) (comp (R := R) k x z) y) := by
  rw [← comp_assoc_par (R := R) hik x y z, map_symm_map]

theorem nsComp_assoc_seq (a b c d : ℕ) {p : ℕ} (α : P (Fin (a + 1 + b)))
    (β : P (Fin (c + 1 + d))) (γ : P (Fin p)) :
    reindex R (toNS P) (by omega)
        (nsComp (R := R) (a + c) (d + b)
          (reindex R (toNS P) (by omega) (nsComp (R := R) a b α β)) γ)
      = nsComp (R := R) a b α (nsComp (R := R) c d β γ) := by
  have h2 : a + (c + 1 + d) + b = a + c + 1 + (d + b) := by omega
  rw [reindex_toNS, reindex_toNS, nsComp_apply, nsComp_apply,
    map_map (insertEquiv a b (c + 1 + d)) (finCongr h2)]
  have hs : ((insertEquiv a b (c + 1 + d)).trans (finCongr h2)) (Sum.inr ⟨c, by omega⟩)
      = (⟨a + c, by omega⟩ : Fin (a + c + 1 + (d + b))) := Fin.ext rfl
  rw [comp_slot hs, comp_map_left, comp_assoc_seq', nsComp_apply, nsComp_apply,
    comp_map_right]
  simp only [map_map]
  refine map_eq_of_equiv_eq (fun y => Fin.ext ?_) _
  rcases y with ⟨⟨k, hk⟩, hne⟩ | ⟨⟨l, hl⟩, hne⟩ | q
  · have hka : k ≠ a := fun e => hne (Fin.ext e)
    simp only [Equiv.trans_apply, seqEquiv_symm_inl, compEquiv, slotEquiv, Equiv.coe_fn_mk,
      Equiv.sumCongr_apply, Sum.map_inl, Equiv.subtypeEquivRight_apply_coe, insertEquiv_inl_val,
      finCongr_apply, Fin.val_cast, Equiv.refl_apply]
    split_ifs <;> omega
  · have hlc : l ≠ c := fun e => hne (Fin.ext e)
    simp only [Equiv.trans_apply, seqEquiv_symm_inr_inl, compEquiv, slotEquiv, Equiv.coe_fn_mk,
      Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.subtypeEquivRight_apply_coe,
      insertEquiv_inl_val, insertEquiv_inr_val, finCongr_apply, Fin.val_cast, Equiv.refl_apply]
    split_ifs <;> omega
  · simp only [Equiv.trans_apply, seqEquiv_symm_inr_inr, compEquiv, slotEquiv, Equiv.coe_fn_mk,
      Equiv.sumCongr_apply, Sum.map_inr, insertEquiv_inr_val, finCongr_apply, Fin.val_cast,
      Equiv.refl_apply]
    omega

/-- Positional composition into a relabelled element: the slot must be the image of an input. -/
lemma nsComp_map_left {A : Type} [Fintype A] [DecidableEq A] (a b : ℕ) {n : ℕ}
    (e : A ≃ Fin (a + 1 + b)) (i : A) (h : e i = ⟨a, by omega⟩) (x : P A) (y : P (Fin n)) :
    nsComp (R := R) a b (map (R := R) e x) y
      = map (R := R) ((compEquiv e (Equiv.refl (Fin n)) i).trans
          ((slotEquiv h).trans (insertEquiv a b n))) (comp (R := R) i x y) := by
  rw [nsComp_apply, comp_slot h, comp_map_left, map_map, map_map]

theorem nsComp_assoc_par (a b c : ℕ) {n p : ℕ} (α : P (Fin (a + 1 + b + 1 + c)))
    (β : P (Fin n)) (γ : P (Fin p)) :
    reindex R (toNS P) (by omega)
        (nsComp (R := R) (a + n + b) c
          (reindex R (toNS P) (by omega)
            (nsComp (R := R) a (b + 1 + c) (reindex R (toNS P) (by omega) α) β)) γ)
      = nsComp (R := R) a (b + p + c)
          (reindex R (toNS P) (by omega) (nsComp (R := R) (a + 1 + b) c α γ)) β := by
  have k2 : a + n + (b + 1 + c) = a + n + b + 1 + c := by omega
  have k3 : a + 1 + b + 1 + c = a + 1 + (b + 1 + c) := by omega
  have k4 : a + 1 + b + p + c = a + 1 + (b + p + c) := by omega
  -- the two slots of `α`
  let s₁ : Fin (a + 1 + b + 1 + c) := ⟨a, by omega⟩
  let s₂ : Fin (a + 1 + b + 1 + c) := ⟨a + 1 + b, by omega⟩
  have hik : s₁ ≠ s₂ := fun e => by
    have := congrArg Fin.val e
    simp only [s₁, s₂] at this
    omega
  rw [reindex_toNS, reindex_toNS, reindex_toNS, reindex_toNS]
  have h₁ : (finCongr k3) s₁ = (⟨a, by omega⟩ : Fin (a + 1 + (b + 1 + c))) := Fin.ext rfl
  rw [nsComp_map_left a (b + 1 + c) (finCongr k3) s₁ h₁, map_map]
  have h₂ : (((compEquiv (finCongr k3) (Equiv.refl (Fin n)) s₁).trans ((slotEquiv h₁).trans
      (insertEquiv a (b + 1 + c) n))).trans (finCongr k2)) (Sum.inl ⟨s₂, Ne.symm hik⟩)
      = (⟨a + n + b, by omega⟩ : Fin (a + n + b + 1 + c)) := by
    refine Fin.ext ?_
    simp only [Equiv.trans_apply, compEquiv, slotEquiv, Equiv.coe_fn_mk, Equiv.sumCongr_apply,
      Sum.map_inl, Equiv.subtypeEquivRight_apply_coe, insertEquiv_inl_val, finCongr_apply,
      Fin.val_cast, s₂]
    split_ifs <;> omega
  rw [nsComp_map_left (a + n + b) c _ (Sum.inl ⟨s₂, Ne.symm hik⟩) h₂, comp_assoc_par' hik,
    nsComp_apply (a + 1 + b) c, map_map (insertEquiv (a + 1 + b) c p) (finCongr k4)]
  have h₃ : ((insertEquiv (a + 1 + b) c p).trans (finCongr k4)) (Sum.inl ⟨s₁, hik⟩)
      = (⟨a, by omega⟩ : Fin (a + 1 + (b + p + c))) := by
    refine Fin.ext ?_
    simp only [Equiv.trans_apply, insertEquiv_inl_val, finCongr_apply, Fin.val_cast, s₁]
    split_ifs <;> omega
  rw [nsComp_map_left a (b + p + c) _ (Sum.inl ⟨s₁, hik⟩) h₃]
  simp only [map_map]
  refine map_eq_of_equiv_eq (fun y => Fin.ext ?_) _
  rcases y with ⟨(⟨⟨k, hk⟩, hne₂⟩ | q), hne₁⟩ | j
  · have hk₂ : k ≠ a + 1 + b := fun e => hne₂ (Fin.ext e)
    have hk₁ : k ≠ a := fun e => hne₁ (by
      simp only [Sum.inl.injEq, Subtype.mk.injEq]; exact Fin.ext e)
    simp only [Equiv.trans_apply, parEquiv_symm_inl_inl, compEquiv, slotEquiv, Equiv.coe_fn_mk,
      Equiv.sumCongr_apply, Sum.map_inl, Equiv.subtypeEquivRight_apply_coe, insertEquiv_inl_val,
      finCongr_apply, Fin.val_cast, Equiv.refl_apply]
    split_ifs <;> omega
  · simp only [Equiv.trans_apply, parEquiv_symm_inl_inr, compEquiv, slotEquiv, Equiv.coe_fn_mk,
      Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.subtypeEquivRight_apply_coe,
      insertEquiv_inl_val, insertEquiv_inr_val, finCongr_apply, Fin.val_cast, Equiv.refl_apply]
    split_ifs <;> omega
  · simp only [Equiv.trans_apply, parEquiv_symm_inr, compEquiv, slotEquiv, Equiv.coe_fn_mk,
      Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.subtypeEquivRight_apply_coe,
      insertEquiv_inl_val, insertEquiv_inr_val, finCongr_apply, Fin.val_cast, Equiv.refl_apply]
    split_ifs <;> omega

/-- **The underlying non-symmetric operad** of a symmetric operad: its components on the standard
finite types, composed positionally. -/
instance instNSOperadToNS : NSOperad R (toNS P) where
  one := nsOne (R := R)
  comp a b := nsComp (R := R) a b
  comp_one_right a b α := nsComp_one_right a b α
  comp_one_left α := nsComp_one_left α
  comp_assoc_seq a b c d _ α β γ := nsComp_assoc_seq a b c d α β γ
  comp_assoc_par a b c _ _ α β γ := nsComp_assoc_par a b c α β γ

lemma toNS_comp (a b : ℕ) {n : ℕ} (x : toNS P (a + 1 + b)) (y : toNS P n) :
    NSOperad.comp (R := R) a b x y
      = map (R := R) (insertEquiv a b n) (comp (R := R) (⟨a, by omega⟩ : Fin (a + 1 + b)) x y) :=
  rfl

lemma toNS_one : (NSOperad.one R : toNS P 1) = map (R := R) unitFinOne (one R) := rfl

end SymOperad

/-- **The forgetful functor on morphisms**: a morphism of symmetric operads restricts to a morphism
of the underlying non-symmetric operads. -/
def SymOperadHom.toNS {R : Type u} [CommRing R]
    {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]
    {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]
    (φ : SymOperadHom R P Q) : NSOperadHom R (SymOperad.toNS P) (SymOperad.toNS Q) where
  app n := φ.app (Fin n)
  app_one := by
    rw [SymOperad.toNS_one, SymOperad.toNS_one]
    exact (φ.app_map _ _).trans (congrArg _ φ.app_one)
  app_comp a b _ α β := by
    rw [SymOperad.toNS_comp, SymOperad.toNS_comp]
    exact (φ.app_map _ _).trans (congrArg _ (φ.app_comp _ _ _))

namespace Sym.Perm

variable (R : Type u) [CommRing R]

/-- **The restriction of the symmetric `Perm` to `Fin n` is the non-symmetric `Perm`**, composition
for composition. -/
theorem toNS_comp_eq_permComp (a b : ℕ) {n : ℕ} (x : Fin (a + 1 + b) → R) (y : Fin n → R) :
    NSOperad.comp (R := R) (P := SymOperad.toNS (Sym.Perm R)) a b x y
      = Operad.Perm.permComp a b x y := by
  funext m
  rw [SymOperad.toNS_comp]
  show compFun (⟨a, by omega⟩ : Fin (a + 1 + b)) x y ((insertEquiv a b n).symm m) = _
  have hm := m.isLt
  by_cases h1 : (m : ℕ) < a
  · rw [Operad.Perm.permComp_apply_lt a b x y m h1 (by omega)]
    have : (insertEquiv a b n).symm m = Sum.inl ⟨⟨m, by omega⟩, fun e => by
        have := congrArg Fin.val e; simp only at this; omega⟩ := by
      simp [insertEquiv, h1]
    rw [this, compFun_inl, mul_comm]
  · by_cases h2 : (m : ℕ) < a + n
    · rw [Operad.Perm.permComp_apply_mid a b x y m (by omega) h2 (by omega) (by omega)]
      have : (insertEquiv a b n).symm m = Sum.inr ⟨m - a, by omega⟩ := by
        simp [insertEquiv, h1, h2]
      rw [this, compFun_inr]
    · rw [Operad.Perm.permComp_apply_ge a b x y m (by omega) (by omega)]
      have : (insertEquiv a b n).symm m = Sum.inl ⟨⟨m - n + 1, by omega⟩, fun e => by
          have := congrArg Fin.val e; simp only at this; omega⟩ := by
        simp [insertEquiv, h1, h2]
      rw [this, compFun_inl, mul_comm]

/-- The comparison, as a morphism of non-symmetric operads, identity in every arity. -/
def toNSHom : NSOperadHom R (SymOperad.toNS (Sym.Perm R)) (Operad.Perm R) where
  app _ := LinearMap.id
  app_one := by
    funext k
    have : k = 0 := Fin.fin_one_eq_zero k
    subst this
    rfl
  app_comp a b _ α β := toNS_comp_eq_permComp R a b α β

end Sym.Perm


end Operad
