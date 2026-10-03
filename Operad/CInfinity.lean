/-
# C∞-algebras

A **C∞-structure** is an A∞-structure in the bar convention (`Operad.AInf`) whose operations vanish
on the signed shuffles: for homogeneous words `x` and `y` of positive lengths,

  `∑_S ± b(z_S) = 0`,

the sum running over the interleavings `z_S` of `x` and `y`, with the inputs of `x` at the positions
of `S` (`CInf.merge`), and the sign being the Koszul sign of the unshuffle bringing `S` to the front
(`LInf.usgn`). It is the structure transferred from commutative dg algebras, and C∞-algebras are
the algebras over the minimal model of `Com`.

* `CInf.IsCInf`: C∞-structures.
* **A dg algebra is a C∞-algebra exactly when its product is commutative in the bar convention**,
  `μ(x, y) + σ(|x| |y|) μ(y, x) = 0` (`CInf.isCInf_dga_iff`): in arity two the shuffle condition is
  that identity, and the higher operations vanish.
-/
import Operad.AInfinity
import Operad.LInfinity

universe u v

namespace Operad

namespace CInf

open AInf GerBV LInf

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

/-- **The interleaving of two words**: `x` at the positions of `S` and `y` at the others, both in
order. -/
noncomputable def merge {a c : ℕ} (S : Finset (Fin (a + c))) (hS : S.card = a) {X : Type*}
    (x : Fin a → X) (y : Fin c → X) : Fin (a + c) → X :=
  fun t => if h : t ∈ S then x ((S.orderIsoOfFin hS).symm ⟨t, h⟩)
    else y ((Sᶜ.orderIsoOfFin (by rw [Finset.card_compl, Fintype.card_fin, hS]; omega)).symm
      ⟨t, Finset.mem_compl.2 h⟩)

lemma merge_of_mem {a c : ℕ} {S : Finset (Fin (a + c))} (hS : S.card = a) {X : Type*}
    (x : Fin a → X) (y : Fin c → X) {t : Fin (a + c)} (h : t ∈ S) :
    merge S hS x y t = x ((S.orderIsoOfFin hS).symm ⟨t, h⟩) :=
  dif_pos h

lemma merge_of_not_mem {a c : ℕ} {S : Finset (Fin (a + c))} (hS : S.card = a) {X : Type*}
    (x : Fin a → X) (y : Fin c → X) {t : Fin (a + c)} (h : t ∉ S) :
    ∃ j, merge S hS x y t = y j :=
  ⟨_, dif_neg h⟩

variable (ε : V →ₗ[R] V)

/-- **A C∞-structure**: an A∞-structure whose operations vanish on the signed shuffles of
homogeneous words of positive lengths. -/
structure IsCInf (b : Fam R V) : Prop extends IsAInf ε b where
  /-- The operations vanish on signed shuffles. -/
  shuffle : ∀ (a c : ℕ) (x : Fin (a + 1) → V) (y : Fin (c + 1) → V) (px : Fin (a + 1) → Bool)
    (py : Fin (c + 1) → Bool), (∀ i, IsPar ε (px i) (x i)) → (∀ j, IsPar ε (py j) (y j)) →
    ∑ S : {S : Finset (Fin (a + 1 + (c + 1))) // S.card = a + 1},
      (usgn (merge S.1 S.2 px py) S.1 : R) •
        b (a + c + 1) (merge S.1 S.2 x y ∘ Fin.cast (by omega)) = 0

/-- The two interleavings of two letters. -/
lemma sum_two {M : Type*} [AddCommMonoid M]
    (F : {S : Finset (Fin (0 + 1 + (0 + 1))) // S.card = 0 + 1} → M) :
    ∑ S, F S = F ⟨{0}, rfl⟩ + F ⟨{1}, rfl⟩ := by
  refine Fintype.sum_eq_add _ _ (fun h => by simpa using congrArg Subtype.val h) fun S hS => ?_
  exfalso
  obtain ⟨S, hS'⟩ := S
  obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp hS'
  fin_cases t
  · exact hS.1 rfl
  · exact hS.2 rfl

lemma merge_zero {X : Type*} (x y : Fin 1 → X) :
    merge (a := 1) (c := 1) {0} rfl x y = ![x 0, y 0] := by
  funext t
  fin_cases t
  · exact (merge_of_mem rfl x y (Finset.mem_singleton_self 0)).trans
      (congrArg x (Subsingleton.elim _ _))
  · obtain ⟨j, hj⟩ := merge_of_not_mem (S := {0}) rfl x y (t := 1) (by decide)
    exact hj.trans (congrArg y (Subsingleton.elim _ _))

lemma merge_one {X : Type*} (x y : Fin 1 → X) :
    merge (a := 1) (c := 1) {1} rfl x y = ![y 0, x 0] := by
  funext t
  fin_cases t
  · obtain ⟨j, hj⟩ := merge_of_not_mem (S := {1}) rfl x y (t := 0) (by decide)
    exact hj.trans (congrArg y (Subsingleton.elim _ _))
  · exact (merge_of_mem rfl x y (Finset.mem_singleton_self 1)).trans
      (congrArg x (Subsingleton.elim _ _))

/-- The shuffle condition on two letters. -/
lemma shuffle_two (b : Fam R V) (x y : V) (px py : Bool) :
    ∑ S : {S : Finset (Fin (0 + 1 + (0 + 1))) // S.card = 0 + 1},
      (usgn (merge S.1 S.2 ![px] ![py]) S.1 : R) •
        b (0 + 0 + 1) (merge S.1 S.2 ![x] ![y] ∘ Fin.cast (by omega))
      = b 1 ![x, y] + σ R (px && py) • b 1 ![y, x] := by
  rw [sum_two]
  dsimp only
  rw [merge_zero, merge_zero, merge_one, merge_one]
  have h0 : usgn (R := R) ![px, py] ({0} : Finset (Fin 2)) = 1 := by
    simp [usgn]
  have h1 : usgn (R := R) ![py, px] ({1} : Finset (Fin 2)) = σ R (px && py) := by
    have : (({1} : Finset (Fin 2))ᶜ.filter (· < 1)) = {0} := by decide
    simp [usgn, this]
  simp only [Matrix.cons_val_fin_one] at h0 h1 ⊢
  rw [h0, h1, one_smul]
  congr 2

/-- **A dg algebra is a C∞-algebra exactly when its product is commutative in the bar
convention**: `μ(x, y) + σ(|x| |y|) μ(y, x) = 0` on homogeneous elements. -/
theorem isCInf_dga_iff {d : End R V 1} {μ : End R V 2} :
    IsCInf ε (dga R V d μ) ↔ IsAInf ε (dga R V d μ) ∧
      ∀ (x y : V) (px py : Bool), IsPar ε px x → IsPar ε py y →
        μ ![x, y] + σ R (px && py) • μ ![y, x] = 0 := by
  constructor
  · intro h
    refine ⟨h.toIsAInf, fun x y px py hx hy => ?_⟩
    have := h.shuffle 0 0 ![x] ![y] ![px] ![py] (fun i => by fin_cases i; exact hx)
      (fun j => by fin_cases j; exact hy)
    rwa [shuffle_two] at this
  · rintro ⟨hA, hμ⟩
    refine ⟨hA, fun a c x y px py hx hy => ?_⟩
    rcases Nat.eq_zero_or_pos (a + c) with h | h
    · obtain ⟨rfl, rfl⟩ : a = 0 ∧ c = 0 := ⟨by omega, by omega⟩
      have hx' : x = ![x 0] := by funext i; fin_cases i; rfl
      have hy' : y = ![y 0] := by funext j; fin_cases j; rfl
      have hpx : px = ![px 0] := by funext i; fin_cases i; rfl
      have hpy : py = ![py 0] := by funext j; fin_cases j; rfl
      rw [hx', hy', hpx, hpy, shuffle_two]
      exact hμ _ _ _ _ (hx 0) (hy 0)
    · obtain ⟨k, hk⟩ : ∃ k, a + c + 1 = k + 2 := ⟨a + c - 1, by omega⟩
      refine Finset.sum_eq_zero fun S _ => ?_
      rw [show dga R V d μ (a + c + 1) = 0 by rw [hk]; rfl, MultilinearMap.zero_apply,
        smul_zero]

end CInf

end Operad
