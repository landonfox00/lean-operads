/-
# L∞-algebras

In the shifted convention, an **L∞[1]-structure** on a super module `(V, ε)` is a family `ℓ` of
operations, `ℓₖ` of arity `k`, which are odd and graded symmetric, with the **generalized Jacobi
identities**: for homogeneous inputs `v₀, …, v_{n-1}`,
`∑_S ± ℓ (ℓ (v_S), v_{Sᶜ}) = 0`, the sum running over the nonempty sets `S` of inputs, each of
`v_S` and `v_{Sᶜ}` taken in increasing order, and the sign being the Koszul sign of the unshuffle
bringing `S` to the front (`LInf.usgn`, `LInf.IsLInf`).

* **Two-term L∞[1]-algebras** (`LInf.isLInf_two_iff`): the structures concentrated in arities one
  and two are an odd differential `d` and an odd graded symmetric bracket `b` with `d² = 0`, the
  Leibniz rule `d b(x, y) + b(d x, y) + σ|x| b(x, d y) = 0` and the shifted Jacobi identity
  `b(b(x, y), z) + σ(|y| |z|) b(b(x, z), y) + σ(|x| (|y| + |z|)) b(b(y, z), x) = 0`.
* **dg Lie algebras are L∞-algebras** (`LInf.isLInf_of_dgLie`): a dg Lie superalgebra
  `(V, ε, d, [ , ])` gives an L∞[1]-structure on its parity shift `(V, -ε)`, with `ℓ₁ = d` and
  `ℓ₂(x, y) = [ε x, y] = σ|x| [x, y]`.
-/
import Operad.GerBV
import Operad.KoszulSign
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Powerset

universe u v

namespace Operad

namespace LInf

open GerBV End

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

variable (R V) in
/-- Families of operations of every arity. -/
abbrev LFam : Type v := ∀ k : ℕ, End R V k

/-! ## Signs -/

lemma σ_mul (a b : Bool) : σ R a * σ R b = σ R (xor a b) := by
  cases a <;> cases b <;> simp [σ]

lemma σ_mul_self (a : Bool) : σ R a * σ R a = 1 := by
  cases a <;> simp [σ]

lemma σ_not (a : Bool) : σ R (!a) = -σ R a := by
  cases a <;> simp [σ]

/-- **The Koszul sign of an unshuffle**: the inputs in `S` move to the front, across the inputs
before them which are not in `S`. -/
def usgn {n : ℕ} (p : Fin n → Bool) (S : Finset (Fin n)) : R :=
  ∏ i ∈ S, ∏ j ∈ Sᶜ.filter (· < i), σ R (p i && p j)

/-- **The inputs in a set**, in increasing order. -/
def restr {n : ℕ} (v : Fin n → V) (S : Finset (Fin n)) : Fin S.card → V :=
  fun a => v (S.orderEmbOfFin rfl a)

/-- **The generalized Jacobi expression** in arity `n`. -/
def jac (ℓ : LFam R V) {n : ℕ} (p : Fin n → Bool) (v : Fin n → V) : V :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.Nonempty),
    (usgn p S : R) • ℓ (Sᶜ.card + 1) (Fin.cons (ℓ S.card (restr v S)) (restr v Sᶜ))

variable (ε : V →ₗ[R] V)

/-- **An L∞[1]-structure** on a super module: odd, graded symmetric operations of every arity,
with the generalized Jacobi identities on homogeneous inputs. -/
structure IsLInf (ℓ : LFam R V) : Prop where
  /-- Every operation is odd. -/
  odd : ∀ k, IsHomog ε 1 (ℓ k)
  /-- Graded symmetry: exchanging two adjacent homogeneous inputs costs their Koszul sign. -/
  symm : ∀ k (p : Fin k → Bool) (v : Fin k → V), (∀ a, IsPar ε (p a) (v a)) →
    ∀ (i : ℕ) (h : i + 1 < k), ℓ k (v ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, h⟩) =
      σ R (p ⟨i, by omega⟩ && p ⟨i + 1, h⟩) • ℓ k v
  /-- The generalized Jacobi identities. -/
  jac : ∀ n (p : Fin n → Bool) (v : Fin n → V), (∀ a, IsPar ε (p a) (v a)) → jac ℓ p v = 0

/-! ## Computing the Jacobi expressions -/

lemma term_eq (ℓ : LFam R V) {n : ℕ} (v : Fin n → V) (S : Finset (Fin n)) {k m : ℕ}
    (hk : S.card = k) (hm : Sᶜ.card = m) :
    ℓ (Sᶜ.card + 1) (Fin.cons (ℓ S.card (restr v S)) (restr v Sᶜ)) =
      ℓ (m + 1) (Fin.cons (ℓ k fun a => v (S.orderEmbOfFin hk a))
        fun a => v (Sᶜ.orderEmbOfFin hm a)) := by
  subst hk
  subst hm
  rfl

lemma oe_eq {n k : ℕ} {S : Finset (Fin n)} (h : S.card = k) (f : Fin k → Fin n)
    (hf : ∀ x, f x ∈ S) (hm : StrictMono f) (a : Fin k) : S.orderEmbOfFin h a = f a :=
  (congrFun (Finset.orderEmbOfFin_unique h hf hm) a).symm

/-- The family with `d` in arity one, `b` in arity two and zero elsewhere. -/
def two (d : End R V 1) (b : End R V 2) : LFam R V
  | 1 => d
  | 2 => b
  | _ => 0

@[simp] lemma two_one (d : End R V 1) (b : End R V 2) : two d b 1 = d := rfl

@[simp] lemma two_two (d : End R V 1) (b : End R V 2) : two d b 2 = b := rfl

lemma two_of_ge (d : End R V 1) (b : End R V 2) {k : ℕ} (hk : 3 ≤ k) : two d b k = 0 := by
  match k, hk with
  | k + 3, _ => rfl

@[simp] lemma two_zero (d : End R V 1) (b : End R V 2) : two d b 0 = 0 := rfl

@[simp] lemma two_zero_add (d : End R V 1) (b : End R V 2) : two d b (0 + 1) = d := rfl

@[simp] lemma two_one_add (d : End R V 1) (b : End R V 2) : two d b (1 + 1) = b := rfl

lemma strictMono_fin_one {α : Type*} [Preorder α] (f : Fin 1 → α) : StrictMono f :=
  fun a b h => absurd h (by rw [Subsingleton.elim a b]; exact lt_irrefl b)

lemma strictMono_vec2 {n : ℕ} {i j : Fin n} (h : i < j) : StrictMono ![i, j] := by
  intro a b hab
  fin_cases a <;> fin_cases b
  · exact absurd hab (lt_irrefl _)
  · exact h
  · exact absurd hab (by decide)
  · exact absurd hab (lt_irrefl _)

omit [AddCommGroup V] in
/-- The inputs in a singleton. -/
lemma restr_one {n : ℕ} (v : Fin n → V) {S : Finset (Fin n)} (h : S.card = 1) {i : Fin n}
    (hi : i ∈ S) : (fun a => v (S.orderEmbOfFin h a)) = ![v i] := by
  funext a
  fin_cases a
  rw [oe_eq h ![i] (fun x => by fin_cases x; exact hi) (strictMono_fin_one _)]
  rfl

omit [AddCommGroup V] in
/-- The inputs in a pair. -/
lemma restr_two {n : ℕ} (v : Fin n → V) {S : Finset (Fin n)} (h : S.card = 2) {i j : Fin n}
    (hij : i < j) (hi : i ∈ S) (hj : j ∈ S) :
    (fun a => v (S.orderEmbOfFin h a)) = ![v i, v j] := by
  funext a
  rw [oe_eq h ![i, j] (fun x => by fin_cases x; exacts [hi, hj]) (strictMono_vec2 hij)]
  fin_cases a <;> rfl

/-- **The Jacobi expression in arity one**: `d (d x)`. -/
lemma jac_two_one (d : End R V 1) (b : End R V 2) (p : Fin 1 → Bool) (v : Fin 1 → V) :
    jac (two d b) p v = d ![d ![v 0]] := by
  have hS : (Finset.univ.filter fun S : Finset (Fin 1) => S.Nonempty) = {Finset.univ} := by
    decide
  rw [jac, hS, Finset.sum_singleton, term_eq _ v _ (k := 1) (m := 0) (by decide) (by decide)]
  have hu : usgn p (Finset.univ : Finset (Fin 1)) = (1 : R) := by
    simp [usgn]
  rw [hu, one_smul, two_one]
  congr 1
  ext i
  fin_cases i
  show d (fun a => v _) = d ![v 0]
  congr 1
  ext a
  fin_cases a
  exact congrArg v (Subsingleton.elim _ _)

/-- **The Jacobi expression in arity two.** -/
lemma jac_two_two (d : End R V 1) (b : End R V 2) (p : Fin 2 → Bool) (v : Fin 2 → V) :
    jac (two d b) p v =
      b ![d ![v 0], v 1] + σ R (p 1 && p 0) • b ![d ![v 1], v 0] + d ![b ![v 0, v 1]] := by
  have hS : (Finset.univ.filter fun S : Finset (Fin 2) => S.Nonempty) =
      {{0}, {1}, Finset.univ} := by decide
  rw [jac, hS, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, term_eq _ v {0} (k := 1) (m := 1) (by decide) (by decide),
    term_eq _ v {1} (k := 1) (m := 1) (by decide) (by decide),
    term_eq _ v Finset.univ (k := 2) (m := 0) (by decide) (by decide)]
  have h0 : usgn p ({0} : Finset (Fin 2)) = (1 : R) := by
    rw [usgn, Finset.prod_singleton,
      show (({0} : Finset (Fin 2))ᶜ).filter (· < 0) = ∅ from by decide, Finset.prod_empty]
  have h1 : usgn p ({1} : Finset (Fin 2)) = σ R (p 1 && p 0) := by
    rw [usgn, Finset.prod_singleton,
      show (({1} : Finset (Fin 2))ᶜ).filter (· < 1) = {0} from by decide, Finset.prod_singleton]
  have h2 : usgn p (Finset.univ : Finset (Fin 2)) = (1 : R) := by
    simp [usgn]
  simp only [h0, h1, h2, one_smul, two_one_add, two_zero_add]
  rw [restr_one v (S := {0}) _ (Finset.mem_singleton_self 0),
    restr_one v (S := ({0} : Finset (Fin 2))ᶜ) _ (i := 1) (by decide),
    restr_one v (S := {1}) _ (Finset.mem_singleton_self 1),
    restr_one v (S := ({1} : Finset (Fin 2))ᶜ) _ (i := 0) (by decide),
    restr_two v (S := Finset.univ) _ (i := 0) (j := 1) (by decide) (Finset.mem_univ _)
      (Finset.mem_univ _), add_assoc]
  congr 3
  funext a
  fin_cases a
  rfl

/-- **The Jacobi expression in arity three.** -/
lemma jac_two_three (d : End R V 1) (b : End R V 2) (p : Fin 3 → Bool) (v : Fin 3 → V) :
    jac (two d b) p v =
      b ![b ![v 0, v 1], v 2] + σ R (p 2 && p 1) • b ![b ![v 0, v 2], v 1] +
        (σ R (p 1 && p 0) * σ R (p 2 && p 0)) • b ![b ![v 1, v 2], v 0] := by
  have hS : (Finset.univ.filter fun S : Finset (Fin 3) => S.Nonempty) =
      {{0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, Finset.univ} := by decide
  have h3 : two d b (2 + 1) = 0 := two_of_ge d b (by norm_num)
  have hsing : ∀ i : Fin 3, (usgn p ({i} : Finset (Fin 3)) : R) •
      two d b (({i} : Finset (Fin 3))ᶜ.card + 1) (Fin.cons
        (two d b ({i} : Finset (Fin 3)).card (restr v {i})) (restr v ({i} : Finset (Fin 3))ᶜ))
        = 0 := fun i => by
    rw [term_eq _ v {i} (k := 1) (m := 2) (Finset.card_singleton i)
      (by rw [Finset.card_compl, Finset.card_singleton]; rfl), h3, MultilinearMap.zero_apply,
      smul_zero]
  rw [jac, hS, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, hsing, hsing, hsing, zero_add, zero_add,
    zero_add,
    term_eq _ v {0, 1} (k := 2) (m := 1) (by decide) (by decide),
    term_eq _ v {0, 2} (k := 2) (m := 1) (by decide) (by decide),
    term_eq _ v {1, 2} (k := 2) (m := 1) (by decide) (by decide),
    term_eq _ v Finset.univ (k := 3) (m := 0) (by decide) (by decide),
    two_of_ge d b (le_refl 3), MultilinearMap.zero_apply, two_zero_add,
    MultilinearMap.map_coord_zero d 0 (Fin.cons_zero _ _), smul_zero, add_zero, two_one_add]
  have h01 : usgn p ({0, 1} : Finset (Fin 3)) = (1 : R) := by
    rw [usgn, Finset.prod_pair (by decide),
      show (({0, 1} : Finset (Fin 3))ᶜ).filter (· < 0) = ∅ from by decide,
      show (({0, 1} : Finset (Fin 3))ᶜ).filter (· < 1) = ∅ from by decide]
    simp only [Finset.prod_empty, mul_one]
  have h02 : usgn p ({0, 2} : Finset (Fin 3)) = σ R (p 2 && p 1) := by
    rw [usgn, Finset.prod_pair (by decide),
      show (({0, 2} : Finset (Fin 3))ᶜ).filter (· < 0) = ∅ from by decide,
      show (({0, 2} : Finset (Fin 3))ᶜ).filter (· < 2) = {1} from by decide]
    simp only [Finset.prod_empty, Finset.prod_singleton, one_mul]
  have h12 : usgn p ({1, 2} : Finset (Fin 3)) = σ R (p 1 && p 0) * σ R (p 2 && p 0) := by
    rw [usgn, Finset.prod_pair (by decide),
      show (({1, 2} : Finset (Fin 3))ᶜ).filter (· < 1) = {0} from by decide,
      show (({1, 2} : Finset (Fin 3))ᶜ).filter (· < 2) = {0} from by decide]
    simp only [Finset.prod_singleton]
  rw [h01, h02, h12, one_smul,
    restr_two v (S := {0, 1}) _ (i := 0) (j := 1) (by decide) (by decide) (by decide),
    restr_two v (S := {0, 2}) _ (i := 0) (j := 2) (by decide) (by decide) (by decide),
    restr_two v (S := {1, 2}) _ (i := 1) (j := 2) (by decide) (by decide) (by decide),
    restr_one v (S := ({0, 1} : Finset (Fin 3))ᶜ) _ (i := 2) (by decide),
    restr_one v (S := ({0, 2} : Finset (Fin 3))ᶜ) _ (i := 1) (by decide),
    restr_one v (S := ({1, 2} : Finset (Fin 3))ᶜ) _ (i := 0) (by decide), add_assoc]
  rfl

/-- **The Jacobi expressions vanish in arities at least four** for a two-term family. -/
lemma jac_two_of_ge (d : End R V 1) (b : End R V 2) {n : ℕ} (hn : 4 ≤ n) (p : Fin n → Bool)
    (v : Fin n → V) : jac (two d b) p v = 0 := by
  refine Finset.sum_eq_zero fun S _ => ?_
  have hc : S.card + Sᶜ.card = n := by
    rw [Finset.card_compl, Fintype.card_fin]
    have := S.card_le_univ
    rw [Fintype.card_fin] at this
    omega
  by_cases hS : 3 ≤ S.card
  · rw [two_of_ge d b hS, MultilinearMap.zero_apply,
      MultilinearMap.map_coord_zero _ 0 (Fin.cons_zero _ _), smul_zero]
  · rw [two_of_ge d b (show 3 ≤ Sᶜ.card + 1 by omega), MultilinearMap.zero_apply, smul_zero]

lemma jac_zero (ℓ : LFam R V) (p : Fin 0 → Bool) (v : Fin 0 → V) : jac ℓ p v = 0 := by
  refine Finset.sum_eq_zero fun S hS => ?_
  exact absurd (Finset.mem_filter.1 hS).2 (by
    rw [Finset.eq_empty_of_isEmpty S]
    exact Finset.not_nonempty_empty)

/-! ## Two-term L∞[1]-algebras -/

lemma IsHomog.isPar_one {d : End R V 1} (hd : IsHomog ε 1 d) {p : Bool} {x : V}
    (hx : IsPar ε p x) : IsPar ε (!p) (d ![x]) := by
  have h := hd ![x]
  have e : (fun t => ε (![x] t)) = ![σ R p • x] := by
    funext t
    fin_cases t
    exact hx
  rw [e, show ![σ R p • x] = Function.update ![x] 0 (σ R p • x) by
    funext t; fin_cases t; rfl, MultilinearMap.map_update_smul,
    show Function.update ![x] 0 x = ![x] by funext t; fin_cases t; rfl] at h
  rw [IsPar, σ_not]
  have h' : ε (d ![x]) = -(σ R p • d ![x]) := by
    rw [h]
    simp
  rw [h', neg_smul]

omit [AddCommGroup V] in
lemma vec_swap {x y : V} : ![x, y] ∘ Equiv.swap (0 : Fin 2) 1 = ![y, x] := by
  funext t
  fin_cases t <;> rfl

/-- **Two-term L∞[1]-algebras**: an L∞[1]-structure concentrated in arities one and two is an odd
differential and an odd graded symmetric bracket with `d² = 0`, the Leibniz rule and the shifted
Jacobi identity. -/
theorem isLInf_two_iff (d : End R V 1) (b : End R V 2) :
    IsLInf ε (two d b) ↔ IsHomog ε 1 d ∧ IsHomog ε 1 b ∧
      (∀ p q x y, IsPar ε p x → IsPar ε q y → b ![y, x] = σ R (p && q) • b ![x, y]) ∧
      (∀ p x, IsPar ε p x → d ![d ![x]] = 0) ∧
      (∀ p q x y, IsPar ε p x → IsPar ε q y →
        d ![b ![x, y]] + b ![d ![x], y] + σ R p • b ![x, d ![y]] = 0) ∧
      (∀ p q r x y z, IsPar ε p x → IsPar ε q y → IsPar ε r z →
        b ![b ![x, y], z] + σ R (q && r) • b ![b ![x, z], y] +
          σ R (p && xor q r) • b ![b ![y, z], x] = 0) := by
  have e₁ : ∀ p q : Bool, σ R (q && p) * σ R (p && !q) = σ R p := fun p q => by
    rw [σ_mul]
    cases p <;> cases q <;> rfl
  have e₂ : ∀ p q r : Bool, σ R (q && p) * σ R (r && p) = σ R (p && xor q r) := fun p q r => by
    rw [σ_mul]
    cases p <;> cases q <;> cases r <;> rfl
  constructor
  · intro h
    have hd : IsHomog ε 1 d := h.odd 1
    have hb : IsHomog ε 1 b := h.odd 2
    have hsymm : ∀ p q x y, IsPar ε p x → IsPar ε q y → b ![y, x] = σ R (p && q) • b ![x, y] := by
      intro p q x y hx hy
      have := h.symm 2 ![p, q] ![x, y] (fun a => by fin_cases a; exacts [hx, hy]) 0
        (by norm_num)
      rw [show ![x, y] ∘ Equiv.swap ⟨0, by norm_num⟩ ⟨0 + 1, by norm_num⟩ = ![y, x] from
        vec_swap] at this
      exact this
    refine ⟨hd, hb, hsymm, fun p x hx => ?_, fun p q x y hx hy => ?_,
      fun p q r x y z hx hy hz => ?_⟩
    · have := h.jac 1 ![p] ![x] (fun a => by fin_cases a; exact hx)
      rw [jac_two_one] at this
      exact this
    · have := h.jac 2 ![p, q] ![x, y] (fun a => by fin_cases a; exacts [hx, hy])
      rw [jac_two_two] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      rw [hsymm p (!q) x (d ![y]) hx (IsHomog.isPar_one ε hd hy), smul_smul, e₁] at this
      calc d ![b ![x, y]] + b ![d ![x], y] + σ R p • b ![x, d ![y]]
          = b ![d ![x], y] + σ R p • b ![x, d ![y]] + d ![b ![x, y]] := by abel
        _ = 0 := this
    · have := h.jac 3 ![p, q, r] ![x, y, z] (fun a => by fin_cases a; exacts [hx, hy, hz])
      rw [jac_two_three] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at this
      rw [Bool.and_comm r q, e₂] at this
      exact this
  · rintro ⟨hd, hb, hsymm, hdd, hleib, hjac⟩
    have hz : ∀ k, IsHomog ε 1 (0 : End R V k) := fun k v => by simp
    refine ⟨fun k => ?_, fun k => ?_, fun n => ?_⟩
    · match k with
      | 0 => exact hz 0
      | 1 => exact hd
      | 2 => exact hb
      | k + 3 => exact hz (k + 3)
    · match k with
      | 0 => exact fun _ _ _ i hi => absurd hi (by omega)
      | 1 => exact fun _ _ _ i hi => absurd hi (by omega)
      | 2 =>
        intro p v hv i hi
        obtain rfl : i = 0 := by omega
        have ev : v = ![v 0, v 1] := by
          funext t
          fin_cases t <;> rfl
        rw [two_two, ev, show ![v 0, v 1] ∘ Equiv.swap ⟨0, by norm_num⟩ ⟨0 + 1, hi⟩ =
          ![v 1, v 0] from vec_swap]
        exact hsymm (p 0) (p 1) (v 0) (v 1) (hv 0) (hv 1)
      | k + 3 =>
        intro p v hv i hi
        rw [two_of_ge d b (by omega), MultilinearMap.zero_apply, MultilinearMap.zero_apply,
          smul_zero]
    · match n with
      | 0 => exact fun p v _ => jac_zero _ p v
      | 1 =>
        intro p v hv
        rw [jac_two_one]
        exact hdd (p 0) (v 0) (hv 0)
      | 2 =>
        intro p v hv
        rw [jac_two_two]
        have := hleib (p 0) (p 1) (v 0) (v 1) (hv 0) (hv 1)
        rw [hsymm (p 0) (!p 1) (v 0) (d ![v 1]) (hv 0) (IsHomog.isPar_one ε hd (hv 1)),
          smul_smul, e₁]
        calc b ![d ![v 0], v 1] + σ R (p 0) • b ![v 0, d ![v 1]] + d ![b ![v 0, v 1]]
            = d ![b ![v 0, v 1]] + b ![d ![v 0], v 1] + σ R (p 0) • b ![v 0, d ![v 1]] := by
              abel
          _ = 0 := this
      | 3 =>
        intro p v hv
        rw [jac_two_three, Bool.and_comm (p 2) (p 1), e₂]
        exact hjac (p 0) (p 1) (p 2) (v 0) (v 1) (v 2) (hv 0) (hv 1) (hv 2)
      | n + 4 => exact fun p v _ => jac_two_of_ge d b (by omega) p v

/-! ## dg Lie algebras -/

omit [AddCommGroup V] in
lemma vec_one_eq (v : Fin 1 → V) : v = ![v 0] := by
  funext t
  fin_cases t
  rfl

omit [AddCommGroup V] in
lemma vec_two_eq (v : Fin 2 → V) : v = ![v 0, v 1] := by
  funext t
  fin_cases t <;> rfl

lemma one_smul_arg (f : End R V 1) (c : R) (x : V) : f ![c • x] = c • f ![x] := by
  have := f.map_update_smul ![x] 0 c x
  rwa [show Function.update ![x] 0 (c • x) = ![c • x] by funext t; fin_cases t; rfl,
    show Function.update ![x] 0 x = ![x] by funext t; fin_cases t; rfl] at this

lemma two_smul_left (β : End R V 2) (c : R) (x y : V) : β ![c • x, y] = c • β ![x, y] := by
  have := β.map_update_smul ![x, y] 0 c x
  rwa [show Function.update ![x, y] 0 (c • x) = ![c • x, y] by funext t; fin_cases t <;> rfl,
    show Function.update ![x, y] 0 x = ![x, y] by funext t; fin_cases t <;> rfl] at this

lemma two_smul_right (β : End R V 2) (c : R) (x y : V) : β ![x, c • y] = c • β ![x, y] := by
  have := β.map_update_smul ![x, y] 1 c y
  rwa [show Function.update ![x, y] 1 (c • y) = ![x, c • y] by funext t; fin_cases t <;> rfl,
    show Function.update ![x, y] 1 y = ![x, y] by funext t; fin_cases t <;> rfl] at this

lemma neg_eq_smul (x : V) : -x = (-1 : R) • x := by rw [neg_one_smul]

/-- **A dg Lie superalgebra**: an odd differential `d` and an even bracket `[ , ]` with `d² = 0`,
graded antisymmetry, the graded Jacobi identity and the Leibniz rule, on homogeneous elements. -/
structure IsDGLie (d : End R V 1) (β : End R V 2) : Prop where
  /-- The differential is odd. -/
  d_odd : IsHomog ε 1 d
  /-- The bracket is even. -/
  β_even : IsHomog ε 0 β
  /-- The differential squares to zero. -/
  dd : ∀ x, d ![d ![x]] = 0
  /-- Graded antisymmetry. -/
  antisymm : ∀ p q x y, IsPar ε p x → IsPar ε q y → β ![y, x] = -(σ R (p && q) • β ![x, y])
  /-- The Leibniz rule. -/
  leibniz : ∀ p x y, IsPar ε p x → d ![β ![x, y]] = β ![d ![x], y] + σ R p • β ![x, d ![y]]
  /-- The graded Jacobi identity. -/
  jacobi : ∀ p q x y z, IsPar ε p x → IsPar ε q y →
    β ![x, β ![y, z]] = β ![β ![x, y], z] + σ R (p && q) • β ![y, β ![x, z]]

/-- **The bracket of the parity shift**: `ℓ₂(x, y) = [ε x, y]`. -/
def shiftb (β : End R V 2) : End R V 2 := β.compLinearMap ![ε, LinearMap.id]

lemma shiftb_apply (β : End R V 2) (x y : V) : shiftb ε β ![x, y] = β ![ε x, y] := by
  rw [shiftb, MultilinearMap.compLinearMap_apply]
  congr 1
  funext t
  fin_cases t <;> rfl

lemma isPar_neg_iff {p : Bool} {x : V} : IsPar (-ε) p x ↔ IsPar ε (!p) x := by
  rw [IsPar, IsPar, LinearMap.neg_apply, σ_not, neg_smul, neg_eq_iff_eq_neg]

lemma IsHomog.isPar_two_zero {β : End R V 2} (hβ : IsHomog ε 0 β) {p q : Bool} {x y : V}
    (hx : IsPar ε p x) (hy : IsPar ε q y) : IsPar ε (xor p q) (β ![x, y]) := by
  have h := hβ ![x, y]
  rw [show (fun t => ε (![x, y] t)) = ![σ R p • x, σ R q • y] by
    funext t; fin_cases t; exacts [hx, hy], two_smul_left, two_smul_right, smul_smul, σ_mul,
    pow_zero, one_smul] at h
  exact h.symm

/-- **dg Lie algebras are L∞-algebras**: a dg Lie superalgebra gives an L∞[1]-structure on its
parity shift `(V, -ε)`, with `ℓ₁ = d` and `ℓ₂(x, y) = [ε x, y]`. -/
theorem isLInf_of_dgLie (hε : ∀ x, ε (ε x) = x) {d : End R V 1} {β : End R V 2}
    (h : IsDGLie ε d β) : IsLInf (-ε) (two d (shiftb ε β)) := by
  have hd := h.d_odd
  have hβ := h.β_even
  have εs : ∀ (c : R) (x : V), ε (c • x) = c • ε x := fun c x => map_smul ε c x
  rw [isLInf_two_iff]
  refine ⟨fun v => ?_, fun v => ?_, fun p q x y hx hy => ?_, fun p x _ => h.dd x,
    fun p q x y hx hy => ?_, fun p q r x y z hx hy hz => ?_⟩
  · -- `d` is odd for the shifted parity
    rw [vec_one_eq v]
    have e := hd ![v 0]
    rw [show (fun t => ε (![v 0] t)) = ![ε (v 0)] by funext t; fin_cases t; rfl] at e
    rw [show (fun t => (-ε) (![v 0] t)) = ![(-1 : R) • ε (v 0)] by
      funext t; fin_cases t; exact (neg_one_smul R _).symm, one_smul_arg, e]
    simp
  · -- the shifted bracket is odd
    rw [vec_two_eq v]
    have e := hβ ![ε (v 0), v 1]
    rw [show (fun t => ε (![ε (v 0), v 1] t)) = ![v 0, ε (v 1)] by
      funext t; fin_cases t; exacts [hε (v 0), rfl], pow_zero, one_smul] at e
    rw [show (fun t => (-ε) (![v 0, v 1] t)) = ![(-1 : R) • ε (v 0), (-1 : R) • ε (v 1)] by
      funext t; fin_cases t <;> exact (neg_one_smul R _).symm, shiftb_apply, shiftb_apply,
      εs, hε, two_smul_left, two_smul_right, smul_smul, e]
    simp
  · -- graded symmetry
    rw [isPar_neg_iff] at hx hy
    rw [shiftb_apply, shiftb_apply, hy, hx, two_smul_left, two_smul_left,
      h.antisymm (!p) (!q) x y hx hy, smul_neg, smul_smul, smul_smul, ← neg_smul]
    congr 1
    cases p <;> cases q <;> simp [σ]
  · -- the Leibniz rule
    rw [isPar_neg_iff] at hx hy
    have hdx := IsHomog.isPar_one ε hd hx
    rw [Bool.not_not] at hdx
    have ex : ε x = σ R (!p) • x := hx
    have edx : ε (d ![x]) = σ R p • d ![x] := hdx
    rw [shiftb_apply, shiftb_apply, shiftb_apply, ex, edx, two_smul_left, two_smul_left,
      two_smul_left, one_smul_arg, h.leibniz (!p) x y hx, σ_not, smul_add, smul_smul, smul_smul,
      neg_mul_neg, σ_mul_self, mul_neg, σ_mul_self]
    module
  · -- the Jacobi identity
    rw [isPar_neg_iff] at hx hy hz
    have hxy := IsHomog.isPar_two_zero ε hβ hx hy
    have hxz := IsHomog.isPar_two_zero ε hβ hx hz
    have hyz := IsHomog.isPar_two_zero ε hβ hy hz
    have hJ := h.jacobi (!p) (!q) x y z hx hy
    rw [h.antisymm (xor (!q) (!r)) (!p) (β ![y, z]) x hyz hx,
      h.antisymm (xor (!p) (!r)) (!q) (β ![x, z]) y hxz hy] at hJ
    have ex : ε x = σ R (!p) • x := hx
    have ey : ε y = σ R (!q) • y := hy
    have exy : ε (β ![x, y]) = σ R (xor (!p) (!q)) • β ![x, y] := hxy
    have exz : ε (β ![x, z]) = σ R (xor (!p) (!r)) • β ![x, z] := hxz
    have eyz : ε (β ![y, z]) = σ R (xor (!q) (!r)) • β ![y, z] := hyz
    simp only [shiftb_apply, ex, ey, two_smul_left, exy, exz, eyz, smul_smul]
    cases p <;> cases q <;> cases r <;>
      simp only [σ, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true,
        Bool.and_false, Bool.and_true, Bool.xor_self, if_true, if_false,
        Bool.false_eq_true] at hJ ⊢ <;>
      first
      | linear_combination (norm := module) hJ
      | linear_combination (norm := module) (-1 : R) • hJ

end LInf

end Operad
