/-
# Hadamard products of set operads; dialgebras and trialgebras

The **Hadamard product** `Hadamard S T` of two set operads pairs operations on the same inputs:
`Hadamard S T A = S A × T A`, with relabelling, unit and partial composition taken in both
factors at once (`Hadamard.instSetOperad`). The two projections are morphisms (`Hadamard.fst`,
`Hadamard.snd`), and two morphisms out of a common source pair to a morphism into the product
(`Hadamard.lift`), uniquely (`Hadamard.lift_unique`): the Hadamard product is the categorical
product of set operads. Filling the inputs of a binary operation is componentwise
(`Hadamard.bin_fst`, `Hadamard.bin_snd`), so an identity between composites holds in the product
when it holds in both factors. The product is functorial (`Hadamard.prodMap`) and commutative
(`Hadamard.commIso`). Linearizing, `Lin R (Hadamard S T) A` is free on `S A × T A`, so it is the
tensor product of the free modules on `S A` and on `T A`: the Hadamard product of the linear
operads (the library has no tensor products of operads, so this is not stated).

Two set operads are multiplied with linear orders below.

* `PointedSet A = A`: an operation is one of its inputs, the *pointed* one. Composing `b` into the
  input `i` of `a` points at `a` when `a ≠ i` and at `b` when `a = i` (`PointedSet.comp`). Its
  linearization is the permutative operad, the basis vector of an input going to the indicator
  function of that input (`PointedSet.linPermIso`).
* `NonemptySubset A`: an operation is a nonempty set of inputs. Composing `t` into the input `i`
  of `s` keeps `s` away from `i`, and puts `t` in place of `i` when `i ∈ s` (`NonemptySubset.comp`).
  Its linearization is Vallette's operad `ComTrias` of commutative trialgebras. Singletons embed
  the pointed sets (`PointedSet.toNonemptySubset`).

**Loday's dialgebras and Loday–Ronco's trialgebras.** `Dias R = Lin R DiasSet` with
`DiasSet = Hadamard LinOrd PointedSet`, and `Trias R = Lin R TriasSet` with
`TriasSet = Hadamard LinOrd NonemptySubset`. A linear order on `n` inputs is a ranking of them
(`LinOrd.equivRank`), so there are `n!` of them (`LinOrd.card`; `dim Ass(n) = n!`, `Ass.finrank`),
and `Dias` and `Trias` on `n` inputs have dimensions `n · n!` and `(2ⁿ - 1) · n!` (`DiasSet.card`,
`TriasSet.card`, `Dias.finrank`, `Trias.finrank`). The binary operations `⊣ = (0 < 1, {0})`,
`⊢ = (0 < 1, {1})` and `⊥ = (0 < 1, {0, 1})` satisfy the five relations of dialgebras
(`DiasSet.relations`) and the eleven of trialgebras (`TriasSet.relations`), stated on three
identity leaves as `nestL p q = nestR p' q'` for `(x q y) p z = x p' (y q' z)`; in each, the
order component is the associativity of the ordinal sum (`LinOrd.nestL_std`). Singletons give the
morphism `Dias → Trias` (`DiasSet.toTrias`, `Dias.toTrias`), injective in every arity. That these
relations present `Dias` and `Trias` is not proved here.
-/
import Operad.SymAss
import Operad.SetBinary
import Operad.SymIso
import Mathlib.Data.Fintype.Perm
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

set_option synthInstance.maxSize 1024

universe u v w

namespace Operad

open Sym

/-! ## The Hadamard product -/

/-- **The Hadamard product of set operads**: pairs of operations on the same inputs. -/
abbrev Hadamard (S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    (T : (A : Type) → [Fintype A] → [DecidableEq A] → Type w) :
    (A : Type) → [Fintype A] → [DecidableEq A] → Type (max v w) :=
  fun A _ _ => S A × T A

namespace Hadamard

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  {T : (A : Type) → [Fintype A] → [DecidableEq A] → Type w} [SetOperad S] [SetOperad T]

/-- **The Hadamard product of set operads is a set operad**, componentwise. -/
instance instSetOperad : SetOperad (Hadamard S T) where
  map e x := (SetOperad.map e x.1, SetOperad.map e x.2)
  map_refl x := Prod.ext (SetOperad.map_refl x.1) (SetOperad.map_refl x.2)
  map_trans e f x := Prod.ext (SetOperad.map_trans e f x.1) (SetOperad.map_trans e f x.2)
  one := (SetOperad.one, SetOperad.one)
  comp i x y := (SetOperad.comp i x.1 y.1, SetOperad.comp i x.2 y.2)
  map_comp σ τ i x y :=
    Prod.ext (SetOperad.map_comp σ τ i x.1 y.1) (SetOperad.map_comp σ τ i x.2 y.2)
  comp_one i x := Prod.ext (SetOperad.comp_one i x.1) (SetOperad.comp_one i x.2)
  one_comp y := Prod.ext (SetOperad.one_comp y.1) (SetOperad.one_comp y.2)
  comp_assoc_seq i j x y z :=
    Prod.ext (SetOperad.comp_assoc_seq i j x.1 y.1 z.1)
      (SetOperad.comp_assoc_seq i j x.2 y.2 z.2)
  comp_assoc_par hik x y z :=
    Prod.ext (SetOperad.comp_assoc_par hik x.1 y.1 z.1)
      (SetOperad.comp_assoc_par hik x.2 y.2 z.2)

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

@[simp] lemma map_fst (e : A ≃ B) (x : Hadamard S T A) :
    (SetOperad.map e x).1 = SetOperad.map e x.1 := rfl

@[simp] lemma map_snd (e : A ≃ B) (x : Hadamard S T A) :
    (SetOperad.map e x).2 = SetOperad.map e x.2 := rfl

@[simp] lemma one_fst : (SetOperad.one : Hadamard S T Unit).1 = SetOperad.one := rfl

@[simp] lemma one_snd : (SetOperad.one : Hadamard S T Unit).2 = SetOperad.one := rfl

@[simp] lemma comp_fst (i : A) (x : Hadamard S T A) (y : Hadamard S T B) :
    (SetOperad.comp i x y).1 = SetOperad.comp i x.1 y.1 := rfl

@[simp] lemma comp_snd (i : A) (x : Hadamard S T A) (y : Hadamard S T B) :
    (SetOperad.comp i x y).2 = SetOperad.comp i x.2 y.2 := rfl

/-- **Filling the inputs of a binary operation is componentwise.** -/
@[simp] lemma bin_fst (g : Hadamard S T (Fin 2)) (x : Hadamard S T A) (y : Hadamard S T B) :
    (SetOperad.bin g x y).1 = SetOperad.bin g.1 x.1 y.1 := rfl

@[simp] lemma bin_snd (g : Hadamard S T (Fin 2)) (x : Hadamard S T A) (y : Hadamard S T B) :
    (SetOperad.bin g x y).2 = SetOperad.bin g.2 x.2 y.2 := rfl

/-- The first projection. -/
def fst : SetOperadHom (Hadamard S T) S where
  app _ _ _ x := x.1
  app_map _ _ := rfl
  app_one := rfl
  app_comp _ _ _ := rfl

/-- The second projection. -/
def snd : SetOperadHom (Hadamard S T) T where
  app _ _ _ x := x.2
  app_map _ _ := rfl
  app_one := rfl
  app_comp _ _ _ := rfl

variable {U : (A : Type) → [Fintype A] → [DecidableEq A] → Type*} [SetOperad U]

/-- **The pairing of two morphisms**, into the Hadamard product. -/
def lift (φ : SetOperadHom U S) (ψ : SetOperadHom U T) : SetOperadHom U (Hadamard S T) where
  app A _ _ x := (φ.app A x, ψ.app A x)
  app_map e x := Prod.ext (φ.app_map e x) (ψ.app_map e x)
  app_one := Prod.ext φ.app_one ψ.app_one
  app_comp i x y := Prod.ext (φ.app_comp i x y) (ψ.app_comp i x y)

@[simp] lemma fst_comp_lift (φ : SetOperadHom U S) (ψ : SetOperadHom U T) :
    fst.comp (lift φ ψ) = φ := rfl

@[simp] lemma snd_comp_lift (φ : SetOperadHom U S) (ψ : SetOperadHom U T) :
    snd.comp (lift φ ψ) = ψ := rfl

/-- **The pairing is unique**: the Hadamard product is the product of set operads. -/
lemma lift_unique (φ : SetOperadHom U S) (ψ : SetOperadHom U T)
    (χ : SetOperadHom U (Hadamard S T)) (h₁ : fst.comp χ = φ) (h₂ : snd.comp χ = ψ) :
    χ = lift φ ψ := by
  subst h₁ h₂
  rfl

variable {S' : (A : Type) → [Fintype A] → [DecidableEq A] → Type*} [SetOperad S']
  {T' : (A : Type) → [Fintype A] → [DecidableEq A] → Type*} [SetOperad T']

/-- **The Hadamard product of two morphisms.** -/
def prodMap (φ : SetOperadHom S S') (ψ : SetOperadHom T T') :
    SetOperadHom (Hadamard S T) (Hadamard S' T') :=
  lift (φ.comp fst) (ψ.comp snd)

@[simp] lemma prodMap_app (φ : SetOperadHom S S') (ψ : SetOperadHom T T') (x : Hadamard S T A) :
    (prodMap φ ψ).app A x = (φ.app A x.1, ψ.app A x.2) := rfl

lemma prodMap_injective {φ : SetOperadHom S S'} {ψ : SetOperadHom T T'}
    (hφ : Function.Injective (φ.app A)) (hψ : Function.Injective (ψ.app A)) :
    Function.Injective ((prodMap φ ψ).app A) :=
  fun _ _ h => Prod.ext (hφ (congrArg Prod.fst h)) (hψ (congrArg Prod.snd h))

/-- The factors in the other order. -/
def swap : SetOperadHom (Hadamard S T) (Hadamard T S) := lift snd fst

/-- **The Hadamard product is commutative.** -/
def commIso : SetOperadIso (Hadamard S T) (Hadamard T S) where
  hom := swap
  inv := swap
  hom_inv_id := rfl
  inv_hom_id := rfl

end Hadamard

/-! ## The pointed sets -/

/-- **The set operad of pointed inputs**: an operation on `A` is an input of `A`. -/
@[nolint unusedArguments]
abbrev PointedSet : (A : Type) → [Fintype A] → [DecidableEq A] → Type := fun A _ _ => A

namespace PointedSet

variable {A B : Type} [DecidableEq A]

/-- **Composition of pointed inputs**: the point of the outer operation, unless it is the input
filled, in which case the point of the inner one. -/
def comp (i a : A) (b : B) : Without A i ⊕ B := if h : a = i then Sum.inr b else Sum.inl ⟨a, h⟩

@[simp] lemma comp_self (i : A) (b : B) : comp i i b = Sum.inr b := dif_pos rfl

lemma comp_of_ne {i a : A} (h : a ≠ i) (b : B) : comp i a b = Sum.inl ⟨a, h⟩ := dif_neg h

/-- **The set operad of pointed inputs.** -/
instance instSetOperad : SetOperad PointedSet where
  map e a := e a
  map_refl _ := rfl
  map_trans _ _ _ := rfl
  one := ()
  comp i a b := comp i a b
  map_comp σ τ i a b := by
    show compEquiv σ τ i (comp i a b) = comp (σ i) (σ a) (τ b)
    by_cases h : a = i
    · subst h
      rw [comp_self, comp_self]
      rfl
    · rw [comp_of_ne h, comp_of_ne (σ.injective.ne h)]
      rfl
  comp_one i a := by
    show rightUnitEquiv i (comp i a ()) = a
    by_cases h : a = i
    · subst h
      rw [comp_self]
      rfl
    · rw [comp_of_ne h]
      rfl
  one_comp b := rfl
  comp_assoc_seq i j a b d := by
    show seqEquiv i j _ (comp (Sum.inr j) (comp i a b) d) = comp i a (comp j b d)
    by_cases ha : a = i
    · subst ha
      rw [comp_self, comp_self]
      by_cases hb : b = j
      · subst hb
        rw [comp_self, comp_self]
        rfl
      · rw [comp_of_ne (fun h => hb (Sum.inr_injective h)), comp_of_ne hb]
        rfl
    · rw [comp_of_ne ha, comp_of_ne Sum.inl_ne_inr, comp_of_ne ha]
      rfl
  comp_assoc_par {_ _ _} _ _ _ _ _ _ i k hik a b d := by
    show parEquiv hik _ _ (comp (Sum.inl ⟨k, Ne.symm hik⟩) (comp i a b) d)
      = comp (Sum.inl ⟨i, hik⟩) (comp k a d) b
    by_cases ha : a = i
    · subst ha
      rw [comp_self, comp_of_ne Sum.inr_ne_inl, comp_of_ne hik, comp_self]
      rfl
    · by_cases hk : a = k
      · subst hk
        rw [comp_of_ne ha, comp_self, comp_self, comp_of_ne Sum.inr_ne_inl]
        rfl
      · rw [comp_of_ne ha, comp_of_ne (fun h => hk (congrArg Subtype.val (Sum.inl_injective h))),
          comp_of_ne hk, comp_of_ne (fun h => ha (congrArg Subtype.val (Sum.inl_injective h)))]
        rfl

end PointedSet

/-! ## The nonempty subsets -/

/-- **The set operad of nonempty subsets**: an operation on `A` is a nonempty set of inputs, as its
indicator function. -/
@[nolint unusedArguments]
abbrev NonemptySubset : (A : Type) → [Fintype A] → [DecidableEq A] → Type :=
  fun A _ _ => {s : A → Bool // ∃ a, s a = true}

namespace NonemptySubset

variable {A B : Type} [DecidableEq A]

/-- The indicator function of a composite: `s` away from `i`, and `t` in place of `i` when
`i ∈ s`. -/
def compFun (i : A) (s : A → Bool) (t : B → Bool) : Without A i ⊕ B → Bool :=
  Sum.elim (fun a => s a.1) (fun b => s i && t b)

lemma exists_compFun (i : A) {s : A → Bool} {t : B → Bool} (hs : ∃ a, s a = true)
    (ht : ∃ b, t b = true) : ∃ c, compFun i s t c = true := by
  obtain ⟨a, ha⟩ := hs
  by_cases h : a = i
  · subst h
    obtain ⟨b, hb⟩ := ht
    exact ⟨Sum.inr b, by simp [compFun, ha, hb]⟩
  · exact ⟨Sum.inl ⟨a, h⟩, ha⟩

/-- **Composition of nonempty subsets.** -/
def comp (i : A) (s : {s : A → Bool // ∃ a, s a = true}) (t : {t : B → Bool // ∃ b, t b = true}) :
    {c : Without A i ⊕ B → Bool // ∃ c', c c' = true} :=
  ⟨compFun i s.1 t.1, exists_compFun i s.2 t.2⟩

/-- **The set operad of nonempty subsets.** -/
instance instSetOperad : SetOperad NonemptySubset where
  map e s := ⟨s.1 ∘ e.symm, by
    obtain ⟨a, ha⟩ := s.2
    exact ⟨e a, by simpa using ha⟩⟩
  map_refl _ := rfl
  map_trans _ _ _ := rfl
  one := ⟨fun _ => true, ⟨(), rfl⟩⟩
  comp i s t := comp i s t
  map_comp σ τ i s t := by
    refine Subtype.ext (funext fun c => ?_)
    rcases c with a | b
    · rfl
    · simp [comp, compFun]
  comp_one i s := by
    refine Subtype.ext (funext fun a => ?_)
    by_cases h : a = i
    · subst h
      simp [comp, compFun, rightUnitEquiv_symm_self]
    · simp [comp, compFun, rightUnitEquiv_symm_of_ne h]
  one_comp _ := rfl
  comp_assoc_seq i j s t u := by
    refine Subtype.ext (funext fun c => ?_)
    rcases c with a | b | d
    · rfl
    · rfl
    · simp [comp, compFun, Bool.and_assoc]
  comp_assoc_par hik s t u := by
    refine Subtype.ext (funext fun c => ?_)
    rcases c with ⟨a | d, h⟩ | b <;> rfl

end NonemptySubset

/-! ## Two-fold composites on three leaves -/

namespace SetOperad

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]

/-- **The left-nested composite** `(x q y) p z` of two binary operations, on three identity leaves,
with its inputs relabelled to `Unit ⊕ (Unit ⊕ Unit)`. -/
def nestL (p q : S (Fin 2)) : S (Unit ⊕ (Unit ⊕ Unit)) :=
  map (Equiv.sumAssoc Unit Unit Unit) (bin p (bin q one one) one)

/-- **The right-nested composite** `x p (y q z)` of two binary operations, on three identity
leaves. -/
def nestR (p q : S (Fin 2)) : S (Unit ⊕ (Unit ⊕ Unit)) := bin p one (bin q one one)

end SetOperad

namespace Hadamard

open SetOperad

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  {T : (A : Type) → [Fintype A] → [DecidableEq A] → Type w} [SetOperad S] [SetOperad T]

@[simp] lemma nestL_fst (p q : Hadamard S T (Fin 2)) : (nestL p q).1 = nestL p.1 q.1 := rfl

@[simp] lemma nestL_snd (p q : Hadamard S T (Fin 2)) : (nestL p q).2 = nestL p.2 q.2 := rfl

@[simp] lemma nestR_fst (p q : Hadamard S T (Fin 2)) : (nestR p q).1 = nestR p.1 q.1 := rfl

@[simp] lemma nestR_snd (p q : Hadamard S T (Fin 2)) : (nestR p q).2 = nestR p.2 q.2 := rfl

end Hadamard

/-! ## Linear orders: rankings, counting, associativity -/

namespace Sym.LinOrd

open SetOperad

variable {A : Type} [Fintype A]

open Classical in
/-- **The rank of an input**: the number of inputs before it. -/
noncomputable def rank (x : LinOrd A) (a : A) : ℕ := (Finset.univ.filter fun b => x.lt b a).card

lemma rank_lt_card (x : LinOrd A) (a : A) : x.rank a < Fintype.card A := by
  classical
  rw [← Finset.card_univ]
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).2 ?_)
  exact ⟨a, Finset.mem_univ _, by simp [x.irrefl]⟩

lemma rank_lt_rank (x : LinOrd A) {a b : A} (h : x.lt a b) : x.rank a < x.rank b := by
  classical
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun c hc => ?_).2 ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact x.trans _ _ _ hc h
  · exact ⟨a, by simp [h], by simp [x.irrefl]⟩

/-- **A linear order compares inputs by rank.** -/
lemma lt_iff_rank_lt (x : LinOrd A) (a b : A) : x.lt a b ↔ x.rank a < x.rank b := by
  refine ⟨x.rank_lt_rank, fun h => ?_⟩
  by_cases hab : a = b
  · subst hab
    exact absurd h (lt_irrefl _)
  · rcases x.total a b hab with h' | h'
    · exact h'
    · exact absurd (x.rank_lt_rank h') (not_lt.2 h.le)

lemma rank_injective (x : LinOrd A) : Function.Injective x.rank := by
  intro a b h
  by_contra hab
  rcases x.total a b hab with h' | h'
  · exact (x.rank_lt_rank h').ne h
  · exact (x.rank_lt_rank h').ne' h

/-- The ranking of a linear order, as a bijection onto `Fin n`. -/
noncomputable def toRank (x : LinOrd A) : A ≃ Fin (Fintype.card A) :=
  Equiv.ofBijective (fun a => ⟨x.rank a, x.rank_lt_card a⟩) <| by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨fun a b h => x.rank_injective (congrArg Fin.val h), (Fintype.card_fin _).symm⟩

/-- The linear order pulled back along a bijection onto `Fin n`. -/
def ofRank {n : ℕ} (e : A ≃ Fin n) : LinOrd A where
  lt a b := e a < e b
  irrefl _ := lt_irrefl _
  trans _ _ _ h h' := lt_trans h h'
  total _ _ h := lt_or_gt_of_ne (e.injective.ne h)

lemma rank_ofRank {n : ℕ} (e : A ≃ Fin n) (a : A) : (ofRank e).rank a = e a := by
  calc (ofRank e).rank a = ((Finset.Iio (e a)).map e.symm.toEmbedding).card := by
        unfold rank
        congr 1
        ext b
        simp [ofRank]
    _ = e a := by rw [Finset.card_map, Fin.card_Iio]

/-- **Linear orders are rankings**: a linear order on `A` is the same as a bijection from `A` onto
`Fin n`, where `n` is the number of inputs. -/
noncomputable def equivRank : LinOrd A ≃ (A ≃ Fin (Fintype.card A)) where
  toFun := toRank
  invFun := ofRank
  left_inv x := LinOrd.ext fun a b => (x.lt_iff_rank_lt a b).symm
  right_inv e := Equiv.ext fun a => Fin.ext (rank_ofRank e a)

instance [DecidableEq A] : Finite (LinOrd A) := Finite.of_equiv _ equivRank.symm

/-- **There are `n!` linear orders on `n` inputs.** -/
theorem card [DecidableEq A] : Nat.card (LinOrd A) = (Fintype.card A).factorial := by
  rw [Nat.card_congr equivRank, Nat.card_eq_fintype_card,
    Fintype.card_equiv (Fintype.equivFin A)]

/-- **The ordinal sum is associative**: the standard binary order composed with itself in the two
ways gives the same order on three inputs. -/
theorem nestL_std : nestL (S := fun A _ _ => LinOrd A) (std 2) (std 2)
    = nestR (S := fun A _ _ => LinOrd A) (std 2) (std 2) := by
  refine LinOrd.ext ?_
  rintro (⟨⟩ | ⟨⟩ | ⟨⟩) (⟨⟩ | ⟨⟩ | ⟨⟩) <;>
    simp [nestL, nestR, bin, binEquiv, slotOne, SetOperad.map, SetOperad.comp, SetOperad.one,
      LinOrd.compLt, LinOrd.one]

end Sym.LinOrd

/-- **`dim Ass(n) = n!`.** -/
theorem Sym.Ass.finrank (R : Type u) [CommRing R] [Nontrivial R] (A : Type) [Fintype A]
    [DecidableEq A] : Module.finrank R (Ass R A) = (Fintype.card A).factorial := by
  let _ := Fintype.ofFinite (LinOrd A)
  rw [Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card, LinOrd.card]

/-! ## The pointed sets: the permutative operad, counting, singletons -/

namespace PointedSet

variable (R : Type u) [CommRing R]

/-- The indicator function of the pointed input, in the underlying set operad of `Perm`. -/
def toPerm : SetOperadHom PointedSet (Und R (Sym.Perm R)) where
  app A _ _ a := Und.of R (Sym.Perm R) (Pi.single a 1)
  app_map e a := by
    show (Pi.single (e a) 1 : _ → R) = Sym.Perm.mapL e (Pi.single a 1)
    funext b
    simp only [Sym.Perm.mapL_apply, Pi.single_apply, Equiv.symm_apply_eq]
  app_one := by
    show (Pi.single () 1 : Unit → R) = fun _ => 1
    funext u
    simp
  app_comp i a b := by
    show (Pi.single (comp i a b) 1 : _ → R)
      = Sym.Perm.compFun i (Pi.single a 1) (Pi.single b 1)
    funext c
    by_cases h : a = i
    · subst h
      rw [comp_self]
      rcases c with a' | b'
      · simp [Pi.single_apply, a'.2]
      · simp [Pi.single_apply]
    · rw [comp_of_ne h]
      rcases c with a' | b'
      · simp [Pi.single_apply, Subtype.ext_iff]
      · simp [Pi.single_apply, Ne.symm h]

/-- The linear extension of `toPerm`. -/
noncomputable def linToPerm : SymOperadHom R (Lin R PointedSet) (Sym.Perm R) :=
  SetOperadHom.linExtend R (toPerm R)

lemma linToPerm_apply {A : Type} [Fintype A] [DecidableEq A] (x : A →₀ R) :
    (linToPerm R).app A x = ⇑x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, Finsupp.coe_add]
  | single a r =>
    show Finsupp.lift _ R _ _ (Finsupp.single a r) = _
    funext b
    simp [Finsupp.lift_apply, toPerm, Und.of, Pi.single_apply, Finsupp.single_apply, eq_comm]

/-- **The linearization of the pointed sets is the permutative operad**: the basis vector of an
input goes to the indicator function of that input. -/
noncomputable def linPermIso : SymOperadIso R (Lin R PointedSet) (Sym.Perm R) :=
  SymOperadIso.ofBijective (linToPerm R) fun A _ _ => by
    have h : ⇑((linToPerm R).app A) = Finsupp.equivFunOnFinite := funext (linToPerm_apply R)
    rw [h]
    exact Finsupp.equivFunOnFinite.bijective

/-- **Singletons**: a pointed input, as a one-element set of inputs. -/
def toNonemptySubset : SetOperadHom PointedSet NonemptySubset where
  app A _ _ a := ⟨fun b => decide (b = a), ⟨a, by simp⟩⟩
  app_map e a := by
    refine Subtype.ext (funext fun b => ?_)
    show decide (b = e a) = decide (e.symm b = a)
    simp [Equiv.symm_apply_eq]
  app_one := Subtype.ext (funext fun u => by cases u; rfl)
  app_comp i a b := by
    refine Subtype.ext (funext fun c => ?_)
    show decide (c = comp i a b)
      = NonemptySubset.compFun i (fun x => decide (x = a)) (fun y => decide (y = b)) c
    by_cases h : a = i
    · subst h
      rw [comp_self]
      rcases c with a' | b'
      · simp [NonemptySubset.compFun, a'.2]
      · simp [NonemptySubset.compFun]
    · rw [comp_of_ne h]
      rcases c with a' | b'
      · simp [NonemptySubset.compFun, Subtype.ext_iff]
      · simp [NonemptySubset.compFun, Ne.symm h]

lemma toNonemptySubset_injective (A : Type) [Fintype A] [DecidableEq A] :
    Function.Injective (toNonemptySubset.app A) := by
  intro a b h
  have := congrArg (fun s : NonemptySubset A => s.1 a) h
  simpa [toNonemptySubset] using this

end PointedSet

namespace NonemptySubset

/-- **There are `2ⁿ - 1` nonempty sets of `n` inputs.** -/
theorem card (A : Type) [Fintype A] [DecidableEq A] :
    Fintype.card (NonemptySubset A) = 2 ^ Fintype.card A - 1 := by
  have h : (Finset.univ.filter fun s : A → Bool => ∃ a, s a = true)
      = Finset.univ.erase (fun _ => false) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true, ne_eq]
    constructor
    · rintro ⟨a, ha⟩ rfl
      simp at ha
    · intro hs
      by_contra h'
      exact hs (funext fun a => Bool.eq_false_iff.2 fun h => h' ⟨a, h⟩)
  rw [Fintype.card_subtype, h, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool]

end NonemptySubset

/-- **Vallette's operad of commutative trialgebras**, free on the nonempty sets of inputs. -/
abbrev ComTrias (R : Type u) [CommRing R] := Lin R NonemptySubset

/-! ## Dialgebras and trialgebras -/

open SetOperad

/-- **The set operad of dialgebras**: a linear order on the inputs, with one input pointed. -/
abbrev DiasSet := Hadamard (fun A _ _ => LinOrd A) PointedSet

/-- **Loday's operad of associative dialgebras.** -/
abbrev Dias (R : Type u) [CommRing R] := Lin R DiasSet

/-- **The set operad of trialgebras**: a linear order on the inputs, with a nonempty set of inputs
marked. -/
abbrev TriasSet := Hadamard (fun A _ _ => LinOrd A) NonemptySubset

/-- **Loday and Ronco's operad of associative trialgebras.** -/
abbrev Trias (R : Type u) [CommRing R] := Lin R TriasSet

namespace DiasSet

/-- `x ⊣ y`: the two inputs in order, the first pointed. -/
def left : DiasSet (Fin 2) := (LinOrd.std 2, (0 : Fin 2))

/-- `x ⊢ y`: the two inputs in order, the second pointed. -/
def right : DiasSet (Fin 2) := (LinOrd.std 2, (1 : Fin 2))

/-- **The five relations of dialgebras**: `(x ⊣ y) ⊣ z = x ⊣ (y ⊣ z) = x ⊣ (y ⊢ z)`,
`(x ⊢ y) ⊣ z = x ⊢ (y ⊣ z)`, `(x ⊣ y) ⊢ z = x ⊢ (y ⊢ z) = (x ⊢ y) ⊢ z`. -/
theorem relations :
    nestL left left = nestR left left ∧ nestL left left = nestR left right ∧
      nestL left right = nestR right left ∧ nestL right left = nestR right right ∧
      nestL right right = nestR right right :=
  ⟨Prod.ext LinOrd.nestL_std rfl, Prod.ext LinOrd.nestL_std rfl, Prod.ext LinOrd.nestL_std rfl,
    Prod.ext LinOrd.nestL_std rfl, Prod.ext LinOrd.nestL_std rfl⟩

/-- **There are `n · n!` basis elements of `Dias` on `n` inputs.** -/
theorem card (A : Type) [Fintype A] [DecidableEq A] :
    Nat.card (DiasSet A) = Fintype.card A * (Fintype.card A).factorial := by
  rw [Nat.card_prod, LinOrd.card, Nat.card_eq_fintype_card, mul_comm]

/-- **Dialgebras are trialgebras**: singletons give a morphism `Dias → Trias`. -/
def toTrias : SetOperadHom DiasSet TriasSet :=
  Hadamard.prodMap SetOperadHom.id PointedSet.toNonemptySubset

lemma toTrias_injective (A : Type) [Fintype A] [DecidableEq A] :
    Function.Injective (toTrias.app A) :=
  Hadamard.prodMap_injective (fun _ _ h => h) (PointedSet.toNonemptySubset_injective A)

end DiasSet

/-- **`dim Dias(n) = n · n!`.** -/
theorem Dias.finrank (R : Type u) [CommRing R] [Nontrivial R] (A : Type) [Fintype A]
    [DecidableEq A] :
    Module.finrank R (Dias R A) = Fintype.card A * (Fintype.card A).factorial := by
  let _ := Fintype.ofFinite (DiasSet A)
  rw [Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card, DiasSet.card]

namespace TriasSet

/-- `x ⊣ y`: the two inputs in order, the first marked. -/
def left : TriasSet (Fin 2) := (LinOrd.std 2, ⟨fun k => decide (k = 0), ⟨0, rfl⟩⟩)

/-- `x ⊢ y`: the two inputs in order, the second marked. -/
def right : TriasSet (Fin 2) := (LinOrd.std 2, ⟨fun k => decide (k = 1), ⟨1, rfl⟩⟩)

/-- `x ⊥ y`: the two inputs in order, both marked. -/
def middle : TriasSet (Fin 2) := (LinOrd.std 2, ⟨fun _ => true, ⟨0, rfl⟩⟩)

/-- **The eleven relations of trialgebras**: the five of dialgebras, and
`(x ⊣ y) ⊣ z = x ⊣ (y ⊥ z)`, `(x ⊥ y) ⊣ z = x ⊥ (y ⊣ z)`, `(x ⊣ y) ⊥ z = x ⊥ (y ⊢ z)`,
`(x ⊢ y) ⊥ z = x ⊢ (y ⊥ z)`, `(x ⊥ y) ⊢ z = x ⊢ (y ⊢ z)`, `(x ⊥ y) ⊥ z = x ⊥ (y ⊥ z)`. -/
theorem relations :
    nestL left left = nestR left left ∧ nestL left left = nestR left right ∧
      nestL left right = nestR right left ∧ nestL right left = nestR right right ∧
      nestL right right = nestR right right ∧ nestL left left = nestR left middle ∧
      nestL left middle = nestR middle left ∧ nestL middle left = nestR middle right ∧
      nestL middle right = nestR right middle ∧ nestL right middle = nestR right right ∧
      nestL middle middle = nestR middle middle := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact Prod.ext LinOrd.nestL_std (by decide)

/-- **There are `(2ⁿ - 1) · n!` basis elements of `Trias` on `n` inputs.** -/
theorem card (A : Type) [Fintype A] [DecidableEq A] :
    Nat.card (TriasSet A) = (2 ^ Fintype.card A - 1) * (Fintype.card A).factorial := by
  rw [Nat.card_prod, LinOrd.card, Nat.card_eq_fintype_card, NonemptySubset.card, mul_comm]

/-- The singletons are the dialgebra operations: `⊣` and `⊢` of `Dias` go to those of `Trias`. -/
lemma toTrias_left : DiasSet.toTrias.app _ DiasSet.left = left := by
  refine Prod.ext rfl (Subtype.ext ?_)
  decide

lemma toTrias_right : DiasSet.toTrias.app _ DiasSet.right = right := by
  refine Prod.ext rfl (Subtype.ext ?_)
  decide

end TriasSet

/-- **`dim Trias(n) = (2ⁿ - 1) · n!`.** -/
theorem Trias.finrank (R : Type u) [CommRing R] [Nontrivial R] (A : Type) [Fintype A]
    [DecidableEq A] :
    Module.finrank R (Trias R A) = (2 ^ Fintype.card A - 1) * (Fintype.card A).factorial := by
  let _ := Fintype.ofFinite (TriasSet A)
  rw [Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card, TriasSet.card]

/-- **The morphism `Dias → Trias`**, linearized: injective in every arity. -/
noncomputable def Dias.toTrias (R : Type u) [CommRing R] : SymOperadHom R (Dias R) (Trias R) :=
  DiasSet.toTrias.lin R

lemma Dias.toTrias_injective (R : Type u) [CommRing R] (A : Type) [Fintype A] [DecidableEq A] :
    Function.Injective ((Dias.toTrias R).app A) :=
  Finsupp.mapDomain_injective (DiasSet.toTrias_injective A)

end Operad
