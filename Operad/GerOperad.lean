/-
# The Gerstenhaber and Batalin–Vilkovisky operads

**Planar composition** in a graded operad inserts an operation at an input and lists the inputs
in order (`GrOperad.nsc`). In the graded endomorphism operad, at the standard orders, it is the
Koszul composite (`EndGr.sv_nsc`), and relabelling by a permutation carries the Koszul sign of the
permutation (`EndGr.sv_map_apply`).

* **`Ger`** (`GerOp`) is presented by an even product and an odd bracket, both binary, subject to
  the graded commutativity of the product, the graded symmetry of the bracket, associativity, the
  Leibniz rule and the Jacobi identity (`Ger.relOf`), with the Koszul signs of the graded operad.
  **Its algebras are the Gerstenhaber algebras** (`Ger.algebraEquiv`, `Ger.IsGer`): the relators
  vanish in `End_V` exactly on the Gerstenhaber structures (`Ger.relOf_eq_zero_iff`). The bracket
  `[x, y] = σ|x| l(x, y)` satisfies the usual graded antisymmetry, Poisson rule and Jacobi identity
  (`Ger.IsGer.brk_antisymm`, `Ger.IsGer.brk_mul`, `Ger.IsGer.brk_jacobi`), in the conventions of
  `Operad.GerBV`.
* **`BV`** (`BVOp`) is presented by an even binary product and an odd unary operator `Δ`, subject
  to the commutativity and associativity of the product, `Δ² = 0` and the order condition: the
  deviation `Δ ∘ μ - μ ∘₀ Δ - μ ∘₁ Δ` (`BV.devOf`) is a derivation of the product in its second
  argument. **Its algebras are the BV algebras** (`BV.algebraEquiv`, `BV.IsBV`,
  `BV.relOf_eq_zero_iff`).
-/
import Operad.GradedEnd
import Operad.SymNS

universe u v w

namespace Operad

open Sym GerBV GrEnd

/-! ## Planar composition in a graded operad -/

section Planar

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]

variable (R) in
/-- **Planar composition**: `y` inserted at the input `a` of `x`, the inputs listed in order. -/
def GrOperad.nsc (a b : ℕ) {n : ℕ} (x : P (Fin (a + 1 + b))) (y : P (Fin n)) :
    P (Fin (a + n + b)) :=
  GrOperad.map (R := R) (insertEquiv a b n)
    (GrOperad.comp (R := R) (⟨a, by omega⟩ : Fin (a + 1 + b)) x y)

lemma GrOperad.nsc_sub_left (a b : ℕ) {n : ℕ} (x x' : P (Fin (a + 1 + b))) (y : P (Fin n)) :
    GrOperad.nsc R a b (x - x') y = GrOperad.nsc R a b x y - GrOperad.nsc R a b x' y := by
  simp only [GrOperad.nsc, map_sub, LinearMap.sub_apply]

lemma GrOperadHom.app_nsc (φ : GrOperadHom R P Q) (a b : ℕ) {n : ℕ} (x : P (Fin (a + 1 + b)))
    (y : P (Fin n)) :
    φ.app _ (GrOperad.nsc R a b x y) = GrOperad.nsc R a b (φ.app _ x) (φ.app _ y) := by
  rw [GrOperad.nsc, φ.app_map, φ.app_comp]
  rfl

/-- **A planar composite of homogeneous operations is homogeneous.** -/
lemma GrOperad.par_nsc (a b : ℕ) {n : ℕ} {p q : Bool} {x : P (Fin (a + 1 + b))} {y : P (Fin n)}
    (hx : GrOperad.par (R := R) p x = x) (hy : GrOperad.par (R := R) q y = y) :
    GrOperad.par (R := R) (xor p q) (GrOperad.nsc R a b x y) = GrOperad.nsc R a b x y := by
  rw [GrOperad.nsc, ← GrOperad.map_par]
  congr 1
  conv_lhs => rw [← hx, ← hy]
  rw [GrOperad.comp_par, hx, hy]

end Planar

/-! ## Values in the graded endomorphism operad at the standard orders -/

namespace EndGr

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V] [SuperMod R V]

/-- **The value of an operation at the standard order** of its inputs. -/
def sv {n : ℕ} (F : EndGr R V (Fin n)) : EndOp R V (Fin n) := F.fam (LinOrd.std n)

lemma sv_sub {n : ℕ} (F G : EndGr R V (Fin n)) : sv (F - G) = sv F - sv G := rfl

lemma sv_add {n : ℕ} (F G : EndGr R V (Fin n)) : sv (F + G) = sv F + sv G := rfl

/-- **Operations are determined by their values at the standard order.** -/
lemma ext_sv {n : ℕ} {F G : EndGr R V (Fin n)} (h : sv F = sv G) : F = G :=
  ext (LinOrd.std n) h

lemma eq_zero_iff_sv {n : ℕ} (F : EndGr R V (Fin n)) : F = 0 ↔ sv F = 0 :=
  ⟨fun h => h ▸ rfl, fun h => ext_sv h⟩

lemma sv_par {n : ℕ} (b : Bool) (F : EndGr R V (Fin n)) :
    sv (GrOperad.par (R := R) b F) = parML R V b (sv F) := rfl

/-- **Planar composition at the standard orders** is the Koszul composite. -/
lemma sv_nsc (a b : ℕ) {n : ℕ} (F : EndGr R V (Fin (a + 1 + b))) (G : EndGr R V (Fin n)) :
    sv (GrOperad.nsc R a b F G) = EndOp.mapL R V (insertEquiv a b n)
      (kcomp R V (LinOrd.std _) (⟨a, by omega⟩ : Fin (a + 1 + b)) (sv F) (sv G)) := by
  have h : LinOrd.map (insertEquiv a b n).symm (LinOrd.std (a + n + b))
      = LinOrd.comp (⟨a, by omega⟩ : Fin (a + 1 + b)) (LinOrd.std _) (LinOrd.std n) := by
    rw [← LinOrd.map_insertEquiv_comp_std a b n, lo_map_symm_map]
  show EndOp.mapL R V (insertEquiv a b n) (compFam _ F G
    (LinOrd.map (insertEquiv a b n).symm (LinOrd.std (a + n + b)))) = _
  rw [h, compFam_comp]
  rfl

/-- **Relabelling at the standard order**, on homogeneous inputs: the Koszul sign of the
permutation. -/
lemma sv_map_apply {n : ℕ} (e : Fin n ≃ Fin n) (F : EndGr R V (Fin n)) {c : Fin n → Bool}
    {x : Fin n → V} (hx : IsHom (R := R) c x) :
    sv (GrOperad.map (R := R) e F) x
      = rsg R (LinOrd.std n) (LinOrd.map e.symm (LinOrd.std n)) (fun a => c (e a))
        • sv F fun a => x (e a) := by
  show EndOp.mapL R V e (F.fam (LinOrd.map e.symm (LinOrd.std n))) x = _
  rw [fam_compat F (LinOrd.std n), EndOp.mapL_apply, twist_apply_hom (fun a => hx (e a))]
  rfl

/-! ### Binary and ternary operations -/

/-- Homogeneous elements of parity `p`. -/
def IsP (p : Bool) (x : V) : Prop := SuperMod.pr (R := R) p x = x

lemma isHom_two {p q : Bool} {x y : V} (hx : IsP (R := R) p x) (hy : IsP (R := R) q y) :
    IsHom (R := R) ![p, q] ![x, y] := by
  intro a
  fin_cases a
  · exact hx
  · exact hy

lemma isHom_three {p q r : Bool} {x y z : V} (hx : IsP (R := R) p x) (hy : IsP (R := R) q y)
    (hz : IsP (R := R) r z) : IsHom (R := R) ![p, q, r] ![x, y, z] := by
  intro a
  fin_cases a
  · exact hx
  · exact hy
  · exact hz

lemma bsg_std_zero {n : ℕ} (q : Bool) (c : Fin (n + 1) → Bool) :
    bsg R (LinOrd.std (n + 1)) 0 q c = 1 :=
  Finset.prod_eq_one fun a _ => if_neg (Fin.not_lt_zero a)

lemma bsg_std_one (q : Bool) (c : Fin 2 → Bool) : bsg R (LinOrd.std 2) 1 q c = σ R (q && c 0) := by
  unfold bsg
  rw [Fin.prod_univ_two, if_pos (show (LinOrd.std 2).lt 0 1 from (by decide : (0 : Fin 2) < 1)),
    if_neg (show ¬ (LinOrd.std 2).lt 1 1 from (by decide : ¬ (1 : Fin 2) < 1)), mul_one]

lemma rsg_swap_two (d : Fin 2 → Bool) :
    rsg R (LinOrd.std 2) (LinOrd.map (Equiv.swap (0 : Fin 2) 1).symm (LinOrd.std 2)) d
      = σ R (d 0 && d 1) := by
  unfold rsg
  simp only [Fin.prod_univ_two, LinOrd.map_lt, LinOrd.std_lt, Equiv.symm_symm,
    Equiv.swap_apply_left, Equiv.swap_apply_right, lt_self_iff_false, false_and, if_false,
    one_mul, mul_one]
  rw [if_pos (by decide), if_neg (by decide), mul_one]

lemma rsg_swap_three (d : Fin 3 → Bool) :
    rsg R (LinOrd.std 3) (LinOrd.map (Equiv.swap (0 : Fin 3) 1).symm (LinOrd.std 3)) d
      = σ R (d 0 && d 1) := by
  unfold rsg
  simp only [Fin.prod_univ_three, LinOrd.map_lt, LinOrd.std_lt, Equiv.symm_symm,
    lt_self_iff_false, false_and, if_false, one_mul, mul_one]
  rw [Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)]
  rw [if_pos (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide)]
  simp

/-- **The transposition of two inputs**, with its Koszul sign. -/
lemma sv_swap_two (F : EndGr R V (Fin 2)) {p q : Bool} {x y : V} (hx : IsP (R := R) p x)
    (hy : IsP (R := R) q y) :
    sv (GrOperad.map (R := R) (Equiv.swap (0 : Fin 2) 1) F) ![x, y]
      = σ R (p && q) • sv F ![y, x] := by
  rw [sv_map_apply _ F (isHom_two hx hy), rsg_swap_two]
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [Bool.and_comm]
  congr 2
  funext a
  fin_cases a <;> rfl

lemma bsg_std_first {n : ℕ} (h : 0 < n) (q : Bool) (c : Fin n → Bool) :
    bsg R (LinOrd.std n) ⟨0, h⟩ q c = 1 :=
  Finset.prod_eq_one fun a _ => if_neg fun h' : a < ⟨0, h⟩ => Nat.not_lt_zero _ h'

lemma bsg_std_second (h : 1 < 2) (q : Bool) (c : Fin 2 → Bool) :
    bsg R (LinOrd.std 2) ⟨1, h⟩ q c = σ R (q && c 0) :=
  bsg_std_one q c

/-- **Composing into the first input** of a binary operation. -/
lemma sv_nsc01 (F : EndGr R V (Fin 2)) {n : ℕ} {q : Bool} (G : EndGr R V (Fin n))
    (hG : parML R V q (sv G) = sv G) {c : Fin (0 + n + 1) → Bool} {v : Fin (0 + n + 1) → V}
    (hv : IsHom (R := R) c v) :
    sv (GrOperad.nsc R 0 1 F G) v
      = sv F ![sv G fun j => v ⟨j, by omega⟩, v ⟨n, by omega⟩] := by
  rw [sv_nsc, EndOp.mapL_apply, kcomp_apply_hom _ _ _ hG (fun u => hv _), bsg_std_first,
    one_smul]
  congr 1
  funext a
  fin_cases a
  · show sv G _ = sv G _
    congr 1
    funext j
    congr 1
    exact Fin.ext (show 0 + (j : ℕ) = j by omega)
  · show v _ = v _
    congr 1
    exact Fin.ext (show 1 + n - 1 = n by omega)

/-- **Composing into the second input** of a binary operation, with the Koszul sign of moving
past the first. -/
lemma sv_nsc10 (F : EndGr R V (Fin 2)) {n : ℕ} {q : Bool} (G : EndGr R V (Fin n))
    (hG : parML R V q (sv G) = sv G) {c : Fin (1 + n + 0) → Bool} {v : Fin (1 + n + 0) → V}
    (hv : IsHom (R := R) c v) :
    sv (GrOperad.nsc R 1 0 F G) v
      = σ R (q && c ⟨0, by omega⟩)
        • sv F ![v ⟨0, by omega⟩, sv G fun j => v ⟨1 + j, by omega⟩] := by
  rw [sv_nsc, EndOp.mapL_apply, kcomp_apply_hom _ _ _ hG (fun u => hv _), bsg_std_second]
  congr 1
  congr 1
  funext a
  fin_cases a
  · rfl
  · rfl

/-- **The transposition of the first two of three inputs**, with its Koszul sign. -/
lemma sv_swap_three (H : EndGr R V (Fin 3)) {c : Fin 3 → Bool} {v : Fin 3 → V}
    (hv : IsHom (R := R) c v) :
    sv (GrOperad.map (R := R) (Equiv.swap (0 : Fin 3) 1) H) v
      = σ R (c 0 && c 1) • sv H ![v 1, v 0, v 2] := by
  rw [sv_map_apply _ H hv, rsg_swap_three]
  rw [Equiv.swap_apply_left, Equiv.swap_apply_right, Bool.and_comm]
  congr 2
  funext a
  fin_cases a
  · rfl
  · rfl
  · show v (Equiv.swap (0 : Fin 3) 1 2) = v 2
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]

omit [AddCommGroup V] [Module R V] [SuperMod R V] in
lemma vec_two (v : Fin 2 → V) : v = ![v 0, v 1] := by
  funext a
  fin_cases a <;> rfl

omit [AddCommGroup V] [Module R V] [SuperMod R V] in
lemma vec_three (v : Fin 3 → V) : v = ![v 0, v 1, v 2] := by
  funext a
  fin_cases a <;> rfl

lemma isP_of_isHom {n : ℕ} {c : Fin n → Bool} {v : Fin n → V} (hv : IsHom (R := R) c v)
    (a : Fin n) : IsP (R := R) (c a) (v a) :=
  hv a

/-- A multilinear map vanishes when it vanishes on homogeneous inputs. -/
lemma eq_zero_iff_hom {n : ℕ} (f : EndOp R V (Fin n)) :
    f = 0 ↔ ∀ (c : Fin n → Bool) (v : Fin n → V), IsHom (R := R) c v → f v = 0 :=
  ⟨fun h c v _ => by rw [h, MultilinearMap.zero_apply],
    fun h => ext_hom fun c v hv => by rw [h c v hv, MultilinearMap.zero_apply]⟩

/-- Composing into the first input, on three homogeneous inputs. -/
lemma sv01_three (F G : EndGr R V (Fin 2)) {q : Bool} (hG : parML R V q (sv G) = sv G)
    {p₁ p₂ p₃ : Bool} {x y z : V} (hx : IsP (R := R) p₁ x) (hy : IsP (R := R) p₂ y)
    (hz : IsP (R := R) p₃ z) :
    sv (GrOperad.nsc R 0 1 F G) ![x, y, z] = sv F ![sv G ![x, y], z] := by
  rw [sv_nsc01 F G hG (isHom_three hx hy hz)]
  have e : (fun j : Fin 2 => ![x, y, z] ⟨j, by omega⟩) = ![x, y] := by
    funext j
    fin_cases j <;> rfl
  rw [e]
  rfl

/-- Composing into the second input, on three homogeneous inputs. -/
lemma sv10_three (F G : EndGr R V (Fin 2)) {q : Bool} (hG : parML R V q (sv G) = sv G)
    {p₁ p₂ p₃ : Bool} {x y z : V} (hx : IsP (R := R) p₁ x) (hy : IsP (R := R) p₂ y)
    (hz : IsP (R := R) p₃ z) :
    sv (GrOperad.nsc R 1 0 F G) ![x, y, z] = σ R (q && p₁) • sv F ![x, sv G ![y, z]] := by
  rw [sv_nsc10 F G hG (isHom_three hx hy hz)]
  have e : (fun j : Fin 2 => ![x, y, z] ⟨1 + j, by omega⟩) = ![y, z] := by
    funext j
    fin_cases j <;> rfl
  rw [e]
  rfl

/-- The transposition of the first two inputs, on three homogeneous inputs. -/
lemma swap_three (H : EndGr R V (Fin 3)) {p₁ p₂ p₃ : Bool} {x y z : V}
    (hx : IsP (R := R) p₁ x) (hy : IsP (R := R) p₂ y) (hz : IsP (R := R) p₃ z) :
    sv (GrOperad.map (R := R) (Equiv.swap (0 : Fin 3) 1) H) ![x, y, z]
      = σ R (p₁ && p₂) • sv H ![y, x, z] := by
  rw [sv_swap_three H (isHom_three hx hy hz)]
  rfl

/-- **Composing into a unary operation.** -/
lemma sv_nsc00 (F : EndGr R V (Fin 1)) {n : ℕ} {q : Bool} (G : EndGr R V (Fin n))
    (hG : parML R V q (sv G) = sv G) {c : Fin (0 + n + 0) → Bool} {v : Fin (0 + n + 0) → V}
    (hv : IsHom (R := R) c v) :
    sv (GrOperad.nsc R 0 0 F G) v = sv F ![sv G fun j => v ⟨j, by omega⟩] := by
  rw [sv_nsc, EndOp.mapL_apply, kcomp_apply_hom _ _ _ hG (fun u => hv _), bsg_std_first,
    one_smul]
  congr 1
  funext a
  fin_cases a
  show sv G _ = sv G _
  congr 1
  funext j
  congr 1
  exact Fin.ext (show 0 + (j : ℕ) = j by omega)

lemma sv00_two (F : EndGr R V (Fin 1)) (G : EndGr R V (Fin 2)) {q : Bool}
    (hG : parML R V q (sv G) = sv G) {p₁ p₂ : Bool} {x y : V} (hx : IsP (R := R) p₁ x)
    (hy : IsP (R := R) p₂ y) :
    sv (GrOperad.nsc R 0 0 F G) ![x, y] = sv F ![sv G ![x, y]] := by
  rw [sv_nsc00 F G hG (isHom_two hx hy)]

lemma sv00_one (F G : EndGr R V (Fin 1)) {q : Bool} (hG : parML R V q (sv G) = sv G) {p : Bool}
    {x : V} (hx : IsP (R := R) p x) :
    sv (GrOperad.nsc R 0 0 F G) ![x] = sv F ![sv G ![x]] := by
  rw [sv_nsc00 F G hG (c := ![p]) (fun a => by fin_cases a; exact hx)]

lemma sv01_two (F : EndGr R V (Fin 2)) (G : EndGr R V (Fin 1)) {q : Bool}
    (hG : parML R V q (sv G) = sv G) {p₁ p₂ : Bool} {x y : V} (hx : IsP (R := R) p₁ x)
    (hy : IsP (R := R) p₂ y) :
    sv (GrOperad.nsc R 0 1 F G) ![x, y] = sv F ![sv G ![x], y] := by
  rw [sv_nsc01 F G hG (isHom_two hx hy)]
  have e : (fun j : Fin 1 => ![x, y] ⟨j, by omega⟩) = ![x] := by
    funext j
    fin_cases j
    rfl
  rw [e]
  rfl

lemma sv10_two (F : EndGr R V (Fin 2)) (G : EndGr R V (Fin 1)) {q : Bool}
    (hG : parML R V q (sv G) = sv G) {p₁ p₂ : Bool} {x y : V} (hx : IsP (R := R) p₁ x)
    (hy : IsP (R := R) p₂ y) :
    sv (GrOperad.nsc R 1 0 F G) ![x, y] = σ R (q && p₁) • sv F ![x, sv G ![y]] := by
  rw [sv_nsc10 F G hG (isHom_two hx hy)]
  have e : (fun j : Fin 1 => ![x, y] ⟨1 + j, by omega⟩) = ![y] := by
    funext j
    fin_cases j
    rfl
  rw [e]
  rfl

end EndGr

/-! ## The Gerstenhaber operad -/

/-- **The generators of `Ger`**: a product and a bracket, both binary. -/
inductive GerGen : ℕ → Type
  /-- The product. -/
  | mul : GerGen 2
  /-- The bracket. -/
  | br : GerGen 2

/-- The product is even and the bracket odd. -/
def gerPar : ∀ k, GerGen k → Bool
  | _, .mul => false
  | _, .br => true

namespace Ger

/-- **The relations of `Ger`**: the symmetries of the product and the bracket, associativity, the
Leibniz rule and the Jacobi identity. -/
inductive Rel : ℕ → Type
  /-- The product is graded commutative. -/
  | comm : Rel 2
  /-- The bracket is graded symmetric. -/
  | symm : Rel 2
  /-- The product is associative. -/
  | assoc : Rel 3
  /-- The bracket is a derivation of the product. -/
  | leibniz : Rel 3
  /-- The Jacobi identity. -/
  | jacobi : Rel 3

section

variable (R : Type u) [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]

/-- **The relators**, in a graded operad with a product `m` and a bracket `l`. -/
def relOf (m l : P (Fin 2)) : ∀ {n : ℕ}, Rel n → P (Fin n)
  | _, .comm => GrOperad.map (R := R) (Equiv.swap 0 1) m - m
  | _, .symm => GrOperad.map (R := R) (Equiv.swap 0 1) l - l
  | _, .assoc => GrOperad.nsc R 0 1 m m - GrOperad.nsc R 1 0 m m
  | _, .leibniz => GrOperad.nsc R 1 0 l m - GrOperad.nsc R 0 1 m l
      - GrOperad.map (R := R) (Equiv.swap (0 : Fin 3) 1) (GrOperad.nsc R 1 0 m l)
  | _, .jacobi => GrOperad.nsc R 0 1 l l + GrOperad.nsc R 1 0 l l
      + GrOperad.map (R := R) (Equiv.swap (0 : Fin 3) 1) (GrOperad.nsc R 1 0 l l)

lemma app_relOf {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
    (φ : GrOperadHom R P Q) (m l : P (Fin 2)) {n : ℕ} (r : Rel n) :
    φ.app _ (relOf R m l r) = relOf R (φ.app _ m) (φ.app _ l) r := by
  have h01 : ∀ x y : P (Fin 2), φ.app (Fin 3) (GrOperad.nsc R 0 1 x y)
      = GrOperad.nsc R 0 1 (φ.app _ x) (φ.app _ y) := fun x y => φ.app_nsc 0 1 x y
  have h10 : ∀ x y : P (Fin 2), φ.app (Fin 3) (GrOperad.nsc R 1 0 x y)
      = GrOperad.nsc R 1 0 (φ.app _ x) (φ.app _ y) := fun x y => φ.app_nsc 1 0 x y
  cases r <;> simp only [relOf, map_sub, map_add, φ.app_map, h01, h10]

end

variable (R : Type u) [CommRing R]

/-- The product, in the free graded operad. -/
noncomputable def μ : FreeGr R gerPar (Fin 2) := FreeGr.gen GerGen.mul

/-- The bracket, in the free graded operad. -/
noncomputable def β : FreeGr R gerPar (Fin 2) := FreeGr.gen GerGen.br

/-- **The relators of `Ger`.** -/
def rel (n : ℕ) : Set (FreeGr R gerPar (Fin n)) := Set.range (relOf R (μ R) (β R) (n := n))

end Ger

variable (R : Type u) [CommRing R] in
/-- **The Gerstenhaber operad**, generated by an even commutative product and an odd symmetric
bracket, subject to associativity, the Leibniz rule and the Jacobi identity. -/
abbrev GerOp := (GrOperadIdeal.span R (Ger.rel R)).Quot

namespace Ger

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V] [SuperMod R V]

open EndGr

/-- **A Gerstenhaber algebra**, in the operadic normalization: an even graded commutative
associative product `m` and an odd graded symmetric bracket `l`, a derivation of the product,
satisfying the Jacobi identity; the signs are the Koszul signs of the operations and inputs moved.
The usual bracket is `[x, y] = σ|x| l(x, y)` (`Ger.isGer_iff_bracket`). -/
structure IsGer (m l : EndOp R V (Fin 2)) : Prop where
  par_m : parML R V false m = m
  par_l : parML R V true l = l
  comm : ∀ p q (x y : V), IsP (R := R) p x → IsP (R := R) q y →
    m ![x, y] = σ R (p && q) • m ![y, x]
  symm : ∀ p q (x y : V), IsP (R := R) p x → IsP (R := R) q y →
    l ![x, y] = σ R (p && q) • l ![y, x]
  assoc : ∀ p q r (x y z : V), IsP (R := R) p x → IsP (R := R) q y → IsP (R := R) r z →
    m ![m ![x, y], z] = m ![x, m ![y, z]]
  leibniz : ∀ p q r (x y z : V), IsP (R := R) p x → IsP (R := R) q y → IsP (R := R) r z →
    l ![x, m ![y, z]] = m ![l ![x, y], z] + σ R ((!p) && q) • m ![y, l ![x, z]]
  jacobi : ∀ p q r (x y z : V), IsP (R := R) p x → IsP (R := R) q y → IsP (R := R) r z →
    l ![l ![x, y], z] + σ R p • l ![x, l ![y, z]] + σ R ((!p) && q) • l ![y, l ![x, z]] = 0

lemma σ_and_not (p q : Bool) : σ R (p && q) * σ R (true && q) = σ R ((!p) && q) := by
  cases p <;> cases q <;> simp

/-- **The relators vanish exactly on the Gerstenhaber structures.** -/
theorem relOf_eq_zero_iff (M Λ : EndGr R V (Fin 2)) (hM : parML R V false (sv M) = sv M)
    (hΛ : parML R V true (sv Λ) = sv Λ) :
    (∀ {n : ℕ} (r : Rel n), relOf R M Λ r = 0) ↔ IsGer (sv M) (sv Λ) := by
  constructor
  · intro h
    refine ⟨hM, hΛ, fun p q x y hx hy => ?_, fun p q x y hx hy => ?_,
      fun p q r x y z hx hy hz => ?_, fun p q r x y z hx hy hz => ?_,
      fun p q r x y z hx hy hz => ?_⟩
    · have h1 := (eq_zero_iff_hom _).1 ((eq_zero_iff_sv _).1 (h Rel.comm)) _ _ (isHom_two hx hy)
      rw [relOf, sv_sub, MultilinearMap.sub_apply, sv_swap_two M hx hy, sub_eq_zero] at h1
      exact h1.symm
    · have h1 := (eq_zero_iff_hom _).1 ((eq_zero_iff_sv _).1 (h Rel.symm)) _ _ (isHom_two hx hy)
      rw [relOf, sv_sub, MultilinearMap.sub_apply, sv_swap_two Λ hx hy, sub_eq_zero] at h1
      exact h1.symm
    · have h1 := (eq_zero_iff_hom _).1 ((eq_zero_iff_sv _).1 (h Rel.assoc)) _ _
        (isHom_three hx hy hz)
      rw [relOf, sv_sub, MultilinearMap.sub_apply, sv01_three M M hM hx hy hz,
        sv10_three M M hM hx hy hz, Bool.false_and, σ_false, one_smul, sub_eq_zero] at h1
      exact h1
    · have h1 := (eq_zero_iff_hom _).1 ((eq_zero_iff_sv _).1 (h Rel.leibniz)) _ _
        (isHom_three hx hy hz)
      rw [relOf, sv_sub, sv_sub, MultilinearMap.sub_apply, MultilinearMap.sub_apply,
        sv10_three Λ M hM hx hy hz, sv01_three M Λ hΛ hx hy hz, swap_three _ hx hy hz,
        sv10_three M Λ hΛ hy hx hz, Bool.false_and, σ_false, one_smul, smul_smul,
        σ_and_not] at h1
      rw [← sub_eq_zero, ← h1]
      abel
    · have h1 := (eq_zero_iff_hom _).1 ((eq_zero_iff_sv _).1 (h Rel.jacobi)) _ _
        (isHom_three hx hy hz)
      rw [relOf, sv_add, sv_add, MultilinearMap.add_apply, MultilinearMap.add_apply,
        sv01_three Λ Λ hΛ hx hy hz, sv10_three Λ Λ hΛ hx hy hz, swap_three _ hx hy hz,
        sv10_three Λ Λ hΛ hy hx hz, smul_smul, σ_and_not, Bool.true_and] at h1
      exact h1
  · intro hG n r
    rw [eq_zero_iff_sv, eq_zero_iff_hom]
    intro c v hv
    cases r
    · rw [vec_two v] at hv ⊢
      rw [show c = ![c 0, c 1] from vec_two c] at hv
      have hx : IsP (R := R) (c 0) (v 0) := hv 0
      have hy : IsP (R := R) (c 1) (v 1) := hv 1
      rw [relOf, sv_sub, MultilinearMap.sub_apply, sv_swap_two M hx hy, ← hG.comm _ _ _ _ hx hy,
        sub_self]
    · rw [vec_two v] at hv ⊢
      have hx : IsP (R := R) (c 0) (v 0) := hv 0
      have hy : IsP (R := R) (c 1) (v 1) := hv 1
      rw [relOf, sv_sub, MultilinearMap.sub_apply, sv_swap_two Λ hx hy, ← hG.symm _ _ _ _ hx hy,
        sub_self]
    · rw [vec_three v]
      have hx : IsP (R := R) (c 0) (v 0) := hv 0
      have hy : IsP (R := R) (c 1) (v 1) := hv 1
      have hz : IsP (R := R) (c 2) (v 2) := hv 2
      rw [relOf, sv_sub, MultilinearMap.sub_apply, sv01_three M M hM hx hy hz,
        sv10_three M M hM hx hy hz, Bool.false_and, σ_false, one_smul,
        hG.assoc _ _ _ _ _ _ hx hy hz, sub_self]
    · rw [vec_three v]
      have hx : IsP (R := R) (c 0) (v 0) := hv 0
      have hy : IsP (R := R) (c 1) (v 1) := hv 1
      have hz : IsP (R := R) (c 2) (v 2) := hv 2
      rw [relOf, sv_sub, sv_sub, MultilinearMap.sub_apply, MultilinearMap.sub_apply,
        sv10_three Λ M hM hx hy hz, sv01_three M Λ hΛ hx hy hz, swap_three _ hx hy hz,
        sv10_three M Λ hΛ hy hx hz, Bool.false_and, σ_false, one_smul, smul_smul,
        σ_and_not, hG.leibniz _ _ _ _ _ _ hx hy hz]
      abel
    · rw [vec_three v]
      have hx : IsP (R := R) (c 0) (v 0) := hv 0
      have hy : IsP (R := R) (c 1) (v 1) := hv 1
      have hz : IsP (R := R) (c 2) (v 2) := hv 2
      rw [relOf, sv_add, sv_add, MultilinearMap.add_apply, MultilinearMap.add_apply,
        sv01_three Λ Λ hΛ hx hy hz, sv10_three Λ Λ hΛ hx hy hz, swap_three _ hx hy hz,
        sv10_three Λ Λ hΛ hy hx hz, smul_smul, σ_and_not, Bool.true_and]
      exact hG.jacobi _ _ _ _ _ _ hx hy hz

/-- Values on the generators of `Ger`. -/
def genVal {X : ℕ → Type*} (a b : X 2) : ∀ k, GerGen k → X k
  | _, .mul => a
  | _, .br => b

@[simp] lemma genVal_mul {X : ℕ → Type*} (a b : X 2) : genVal a b 2 GerGen.mul = a := rfl

@[simp] lemma genVal_br {X : ℕ → Type*} (a b : X 2) : genVal a b 2 GerGen.br = b := rfl

lemma sv_par_eq_iff {n : ℕ} (b : Bool) (F : EndGr R V (Fin n)) :
    GrOperad.par (R := R) b F = F ↔ parML R V b (sv F) = sv F :=
  ⟨fun h => congrArg sv h, fun h => ext_sv h⟩

/-- **Algebras over `Ger` are the Gerstenhaber algebras**: a morphism of graded operads
`Ger → End_V` is an even product and an odd bracket on `V` satisfying the identities of
`Ger.IsGer`. -/
noncomputable def algebraEquiv :
    GrAlgebra R V (GerOp R)
      ≃ {ml : EndOp R V (Fin 2) × EndOp R V (Fin 2) // IsGer ml.1 ml.2} where
  toFun φ := by
    refine ⟨(sv (φ.app _ (FreeGr.presGen (rel R) GerGen.mul)),
      sv (φ.app _ (FreeGr.presGen (rel R) GerGen.br))), ?_⟩
    let Φ := φ.comp (GrOperadIdeal.span R (rel R)).projHom
    have hpar : ∀ (e : GerGen 2), GrOperad.par (R := R) (gerPar 2 e)
        (Φ.app (Fin 2) (FreeGr.gen e)) = Φ.app (Fin 2) (FreeGr.gen e) := fun e => by
      rw [← Φ.app_par, FreeGr.par_gen]
    refine (relOf_eq_zero_iff (Φ.app _ (μ R)) (Φ.app _ (β R))
      ((sv_par_eq_iff _ _).1 (hpar .mul)) ((sv_par_eq_iff _ _).1 (hpar .br))).1 fun r => ?_
    rw [← app_relOf]
    show φ.app _ ((GrOperadIdeal.span R (rel R)).proj _ _) = 0
    rw [((GrOperadIdeal.span R (rel R)).proj_eq_zero_iff _).2
      (GrOperadIdeal.subset_span _ ⟨r, rfl⟩), map_zero]
  invFun ml := by
    refine FreeGr.presHomEquiv.symm ⟨⟨genVal (X := fun k => EndGr R V (Fin k))
      (ofFam (LinOrd.std 2) ml.1.1) (ofFam (LinOrd.std 2) ml.1.2), ?_⟩, ?_⟩
    · intro k e
      cases e
      · exact (sv_par_eq_iff _ _).2 (by
          rw [genVal_mul, sv, ofFam_fam]
          exact ml.2.par_m)
      · exact (sv_par_eq_iff _ _).2 (by
          rw [genVal_br, sv, ofFam_fam]
          exact ml.2.par_l)
    · rintro n _ ⟨r, rfl⟩
      rw [app_relOf, μ, β, FreeGr.homEquiv_symm_gen, FreeGr.homEquiv_symm_gen]
      refine (relOf_eq_zero_iff _ _ ?_ ?_).2 ?_ r
      · show parML R V false (sv (ofFam (LinOrd.std 2) ml.1.1))
          = sv (ofFam (LinOrd.std 2) ml.1.1)
        rw [sv, ofFam_fam]
        exact ml.2.par_m
      · show parML R V true (sv (ofFam (LinOrd.std 2) ml.1.2))
          = sv (ofFam (LinOrd.std 2) ml.1.2)
        rw [sv, ofFam_fam]
        exact ml.2.par_l
      · show IsGer (sv (ofFam (LinOrd.std 2) ml.1.1)) (sv (ofFam (LinOrd.std 2) ml.1.2))
        rw [sv, sv, ofFam_fam, ofFam_fam]
        exact ml.2
  left_inv φ := FreeGr.pres_hom_ext fun k e => by
    rw [FreeGr.presHomEquiv_symm_gen]
    cases e
    · exact ofFam_eq _ _
    · exact ofFam_eq _ _
  right_inv ml := Subtype.ext (Prod.ext (by
      show sv ((FreeGr.presHomEquiv.symm _).app _ (FreeGr.presGen (rel R) GerGen.mul)) = _
      rw [FreeGr.presHomEquiv_symm_gen]
      exact ofFam_fam _ _) (by
      show sv ((FreeGr.presHomEquiv.symm _).app _ (FreeGr.presGen (rel R) GerGen.br)) = _
      rw [FreeGr.presHomEquiv_symm_gen]
      exact ofFam_fam _ _))

/-! ### The usual bracket -/

omit [SuperMod R V] in
lemma apply_smul_left (f : EndOp R V (Fin 2)) (c : R) (a b : V) :
    f ![c • a, b] = c • f ![a, b] := by
  have h := f.map_update_smul ![a, b] 0 c a
  rwa [show Function.update ![a, b] 0 (c • a) = ![c • a, b] by
      funext i; fin_cases i <;> rfl,
    show Function.update ![a, b] 0 a = ![a, b] by funext i; fin_cases i <;> rfl] at h

omit [SuperMod R V] in
lemma apply_smul_right (f : EndOp R V (Fin 2)) (c : R) (a b : V) :
    f ![a, c • b] = c • f ![a, b] := by
  have h := f.map_update_smul ![a, b] 1 c b
  rwa [show Function.update ![a, b] 1 (c • b) = ![a, c • b] by
      funext i; fin_cases i <;> rfl,
    show Function.update ![a, b] 1 b = ![a, b] by funext i; fin_cases i <;> rfl] at h

lemma tot_two (p q : Bool) : tot ![p, q] = xor p q := by
  cases p <;> cases q <;> rfl

lemma IsGer.isP_l {m l : EndOp R V (Fin 2)} (h : IsGer m l) {p q : Bool} {x y : V}
    (hx : IsP (R := R) p x) (hy : IsP (R := R) q y) :
    IsP (R := R) (!(xor p q)) (l ![x, y]) := by
  have := pr_apply_hom (isHom_two hx hy) h.par_l
  rwa [tot_two, Bool.true_xor] at this

/-- **The Gerstenhaber bracket** `[x, y] = σ|x| l(x, y)`, for `x` of parity `p`. -/
def brk (l : EndOp R V (Fin 2)) (p : Bool) (x y : V) : V := σ R p • l ![x, y]

/-- **The bracket is graded antisymmetric**: `[x, y] = -σ((|x| + 1)(|y| + 1)) [y, x]`. -/
theorem IsGer.brk_antisymm {m l : EndOp R V (Fin 2)} (h : IsGer m l) {p q : Bool} {x y : V}
    (hx : IsP (R := R) p x) (hy : IsP (R := R) q y) :
    brk l p x y = -σ R ((!p) && (!q)) • brk l q y x := by
  unfold brk
  rw [h.symm p q x y hx hy, smul_smul, smul_smul]
  cases p <;> cases q <;> simp

/-- **The Poisson rule**: `[x, y z] = [x, y] z + σ((|x| + 1)|y|) y [x, z]`. -/
theorem IsGer.brk_mul {m l : EndOp R V (Fin 2)} (h : IsGer m l) {p q r : Bool} {x y z : V}
    (hx : IsP (R := R) p x) (hy : IsP (R := R) q y) (hz : IsP (R := R) r z) :
    brk l p x (m ![y, z]) = m ![brk l p x y, z] + σ R ((!p) && q) • m ![y, brk l p x z] := by
  unfold brk
  rw [h.leibniz p q r x y z hx hy hz, apply_smul_left, apply_smul_right, smul_add, smul_comm]

/-- **The graded Jacobi identity**:
`[x, [y, z]] = [[x, y], z] + σ((|x| + 1)(|y| + 1)) [y, [x, z]]`. -/
theorem IsGer.brk_jacobi {m l : EndOp R V (Fin 2)} (h : IsGer m l) {p q r : Bool} {x y z : V}
    (hx : IsP (R := R) p x) (hy : IsP (R := R) q y) (hz : IsP (R := R) r z) :
    brk l p x (brk l q y z)
      = brk l (!(xor p q)) (brk l p x y) z + σ R ((!p) && (!q)) • brk l q y (brk l p x z) := by
  unfold brk
  have hj := h.jacobi p q r x y z hx hy hz
  rw [apply_smul_right, apply_smul_left, apply_smul_right]
  cases p <;> cases q <;> simp at hj ⊢ <;>
    first
    | linear_combination (norm := module) hj
    | linear_combination (norm := module) -hj

end Ger

/-! ## The Batalin–Vilkovisky operad -/

/-- **The generators of `BV`**: a binary product and a unary operator. -/
inductive BVGen : ℕ → Type
  /-- The product. -/
  | mul : BVGen 2
  /-- The operator. -/
  | op : BVGen 1

/-- The product is even and the operator odd. -/
def bvPar : ∀ k, BVGen k → Bool
  | _, .mul => false
  | _, .op => true

namespace BV

/-- **The relations of `BV`**: the product is commutative and associative, the operator squares
to zero and is of order at most two. -/
inductive Rel : ℕ → Type
  /-- The product is graded commutative. -/
  | comm : Rel 2
  /-- The product is associative. -/
  | assoc : Rel 3
  /-- The operator squares to zero. -/
  | sq : Rel 1
  /-- The operator is of order at most two. -/
  | order : Rel 3

section

variable (R : Type u) [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]

/-- **The deviation** of the operator `d` from being a derivation of the product `m`:
`d ∘ m - m ∘₀ d - m ∘₁ d`. -/
def devOf (m : P (Fin 2)) (d : P (Fin 1)) : P (Fin 2) :=
  GrOperad.nsc R 0 0 d m - GrOperad.nsc R 0 1 m d - GrOperad.nsc R 1 0 m d

/-- **The relators**, in a graded operad with a product `m` and an operator `d`. -/
def relOf (m : P (Fin 2)) (d : P (Fin 1)) : ∀ {n : ℕ}, Rel n → P (Fin n)
  | _, .comm => GrOperad.map (R := R) (Equiv.swap 0 1) m - m
  | _, .assoc => GrOperad.nsc R 0 1 m m - GrOperad.nsc R 1 0 m m
  | _, .sq => GrOperad.nsc R 0 0 d d
  | _, .order => GrOperad.nsc R 1 0 (devOf R m d) m - GrOperad.nsc R 0 1 m (devOf R m d)
      - GrOperad.map (R := R) (Equiv.swap (0 : Fin 3) 1) (GrOperad.nsc R 1 0 m (devOf R m d))

/-- **The deviation is odd.** -/
lemma par_devOf {m : P (Fin 2)} {d : P (Fin 1)} (hm : GrOperad.par (R := R) false m = m)
    (hd : GrOperad.par (R := R) true d = d) :
    GrOperad.par (R := R) true (devOf R m d) = devOf R m d := by
  have h1 := GrOperad.par_nsc 0 0 hd hm
  have h2 := GrOperad.par_nsc 0 1 hm hd
  have h3 := GrOperad.par_nsc 1 0 hm hd
  simp only [Bool.true_xor, Bool.false_xor, Bool.not_false] at h1 h2 h3
  rw [devOf, map_sub, map_sub, h1, h2, h3]

lemma app_devOf {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
    (φ : GrOperadHom R P Q) (m : P (Fin 2)) (d : P (Fin 1)) :
    φ.app _ (devOf R m d) = devOf R (φ.app _ m) (φ.app _ d) := by
  have h00 : φ.app (Fin 2) (GrOperad.nsc R 0 0 d m)
      = GrOperad.nsc R 0 0 (φ.app _ d) (φ.app _ m) := φ.app_nsc 0 0 d m
  have h01 : φ.app (Fin 2) (GrOperad.nsc R 0 1 m d)
      = GrOperad.nsc R 0 1 (φ.app _ m) (φ.app _ d) := φ.app_nsc 0 1 m d
  have h10 : φ.app (Fin 2) (GrOperad.nsc R 1 0 m d)
      = GrOperad.nsc R 1 0 (φ.app _ m) (φ.app _ d) := φ.app_nsc 1 0 m d
  rw [devOf, map_sub, map_sub, h00, h01, h10, devOf]

lemma app_relOf {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
    (φ : GrOperadHom R P Q) (m : P (Fin 2)) (d : P (Fin 1)) {n : ℕ} (r : Rel n) :
    φ.app _ (relOf R m d r) = relOf R (φ.app _ m) (φ.app _ d) r := by
  have h01 : ∀ (x y : P (Fin 2)), φ.app (Fin 3) (GrOperad.nsc R 0 1 x y)
      = GrOperad.nsc R 0 1 (φ.app (Fin 2) x) (φ.app (Fin 2) y) := fun x y => φ.app_nsc 0 1 x y
  have h10 : ∀ (x y : P (Fin 2)), φ.app (Fin 3) (GrOperad.nsc R 1 0 x y)
      = GrOperad.nsc R 1 0 (φ.app (Fin 2) x) (φ.app (Fin 2) y) := fun x y => φ.app_nsc 1 0 x y
  have h00 : φ.app (Fin 1) (GrOperad.nsc R 0 0 d d)
      = GrOperad.nsc R 0 0 (φ.app (Fin 1) d) (φ.app (Fin 1) d) := φ.app_nsc 0 0 d d
  cases r <;> simp only [relOf, map_sub, φ.app_map, h01, h10, h00, app_devOf]

end

variable (R : Type u) [CommRing R]

/-- The product, in the free graded operad. -/
noncomputable def μ : FreeGr R bvPar (Fin 2) := FreeGr.gen BVGen.mul

/-- The operator, in the free graded operad. -/
noncomputable def Δ : FreeGr R bvPar (Fin 1) := FreeGr.gen BVGen.op

/-- **The relators of `BV`.** -/
def rel (n : ℕ) : Set (FreeGr R bvPar (Fin n)) := Set.range (relOf R (μ R) (Δ R) (n := n))

end BV

variable (R : Type u) [CommRing R] in
/-- **The Batalin–Vilkovisky operad**, generated by an even commutative product and an odd unary
operator, subject to associativity, `Δ² = 0` and the order condition: the deviation of `Δ` is a
derivation in its second argument. -/
abbrev BVOp := (GrOperadIdeal.span R (BV.rel R)).Quot

namespace BV

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V] [SuperMod R V]

open EndGr

/-- **The deviation** of `d` from being a derivation of `m`, on elements:
`⟨x, y⟩ = d(x y) - (d x) y - σ|x| x (d y)` for `x` of parity `p`. -/
def dv (m : EndOp R V (Fin 2)) (d : EndOp R V (Fin 1)) (p : Bool) (x y : V) : V :=
  d ![m ![x, y]] - m ![d ![x], y] - σ R p • m ![x, d ![y]]

/-- **A Batalin–Vilkovisky algebra**: an even graded commutative associative product `m` and an
odd operator `d` with `d² = 0`, of order at most two: the deviation is a derivation of the
product in its second argument. -/
structure IsBV (m : EndOp R V (Fin 2)) (d : EndOp R V (Fin 1)) : Prop where
  par_m : parML R V false m = m
  par_d : parML R V true d = d
  comm : ∀ p q (x y : V), IsP (R := R) p x → IsP (R := R) q y →
    m ![x, y] = σ R (p && q) • m ![y, x]
  assoc : ∀ p q r (x y z : V), IsP (R := R) p x → IsP (R := R) q y → IsP (R := R) r z →
    m ![m ![x, y], z] = m ![x, m ![y, z]]
  sq : ∀ p (x : V), IsP (R := R) p x → d ![d ![x]] = 0
  order : ∀ p q r (x y z : V), IsP (R := R) p x → IsP (R := R) q y → IsP (R := R) r z →
    dv m d p x (m ![y, z]) = m ![dv m d p x y, z] + σ R ((!p) && q) • m ![y, dv m d p x z]

lemma isP_m {m : EndOp R V (Fin 2)} (hm : parML R V false m = m) {p q : Bool} {x y : V}
    (hx : IsP (R := R) p x) (hy : IsP (R := R) q y) : IsP (R := R) (xor p q) (m ![x, y]) := by
  have := pr_apply_hom (isHom_two hx hy) hm
  rwa [Ger.tot_two, Bool.false_xor] at this

/-- The deviation, in the graded endomorphism operad, on homogeneous inputs. -/
lemma sv_devOf (M : EndGr R V (Fin 2)) (D : EndGr R V (Fin 1))
    (hM : parML R V false (sv M) = sv M) (hD : parML R V true (sv D) = sv D) {p q : Bool}
    {x y : V} (hx : IsP (R := R) p x) (hy : IsP (R := R) q y) :
    sv (devOf R M D) ![x, y] = dv (sv M) (sv D) p x y := by
  rw [devOf, sv_sub, sv_sub, MultilinearMap.sub_apply, MultilinearMap.sub_apply,
    sv00_two D M hM hx hy, sv01_two M D hD hx hy, sv10_two M D hD hx hy, Bool.true_and]
  rfl

/-- The order relator, first term. -/
lemma sv_order₁ (M : EndGr R V (Fin 2)) (D : EndGr R V (Fin 1))
    (hM : parML R V false (sv M) = sv M) (hD : parML R V true (sv D) = sv D) {p q r : Bool}
    {x y z : V} (hx : IsP (R := R) p x) (hy : IsP (R := R) q y) (hz : IsP (R := R) r z) :
    sv (GrOperad.nsc R 1 0 (devOf R M D) M) ![x, y, z]
      = dv (sv M) (sv D) p x (sv M ![y, z]) := by
  rw [sv10_three (devOf R M D) M hM hx hy hz, Bool.false_and, σ_false, one_smul,
    sv_devOf M D hM hD hx (isP_m hM hy hz)]

/-- The order relator, second term. -/
lemma sv_order₂ (M : EndGr R V (Fin 2)) (D : EndGr R V (Fin 1))
    (hM : parML R V false (sv M) = sv M) (hD : parML R V true (sv D) = sv D)
    (hDv : parML R V true (sv (devOf R M D)) = sv (devOf R M D)) {p q r : Bool}
    {x y z : V} (hx : IsP (R := R) p x) (hy : IsP (R := R) q y) (hz : IsP (R := R) r z) :
    sv (GrOperad.nsc R 0 1 M (devOf R M D)) ![x, y, z] = sv M ![dv (sv M) (sv D) p x y, z] := by
  rw [sv01_three M (devOf R M D) hDv hx hy hz, sv_devOf M D hM hD hx hy]

/-- The order relator, third term. -/
lemma sv_order₃ (M : EndGr R V (Fin 2)) (D : EndGr R V (Fin 1))
    (hM : parML R V false (sv M) = sv M) (hD : parML R V true (sv D) = sv D)
    (hDv : parML R V true (sv (devOf R M D)) = sv (devOf R M D)) {p q r : Bool}
    {x y z : V} (hx : IsP (R := R) p x) (hy : IsP (R := R) q y) (hz : IsP (R := R) r z) :
    sv (GrOperad.map (R := R) (Equiv.swap (0 : Fin 3) 1) (GrOperad.nsc R 1 0 M (devOf R M D)))
        ![x, y, z]
      = σ R ((!p) && q) • sv M ![y, dv (sv M) (sv D) p x z] := by
  rw [swap_three _ hx hy hz, sv10_three M (devOf R M D) hDv hy hx hz, smul_smul,
    Ger.σ_and_not, sv_devOf M D hM hD hx hz]

/-- **The relators vanish exactly on the BV structures.** -/
theorem relOf_eq_zero_iff (M : EndGr R V (Fin 2)) (D : EndGr R V (Fin 1))
    (hM : parML R V false (sv M) = sv M) (hD : parML R V true (sv D) = sv D) :
    (∀ {n : ℕ} (r : Rel n), relOf R M D r = 0) ↔ IsBV (sv M) (sv D) := by
  have hDv : parML R V true (sv (devOf R M D)) = sv (devOf R M D) :=
    (Ger.sv_par_eq_iff _ _).1 (par_devOf R ((Ger.sv_par_eq_iff _ _).2 hM)
      ((Ger.sv_par_eq_iff _ _).2 hD))
  constructor
  · intro h
    refine ⟨hM, hD, fun p q x y hx hy => ?_, fun p q r x y z hx hy hz => ?_,
      fun p x hx => ?_, fun p q r x y z hx hy hz => ?_⟩
    · have h1 := (eq_zero_iff_hom _).1 ((eq_zero_iff_sv _).1 (h Rel.comm)) _ _ (isHom_two hx hy)
      rw [relOf, sv_sub, MultilinearMap.sub_apply, sv_swap_two M hx hy, sub_eq_zero] at h1
      exact h1.symm
    · have h1 := (eq_zero_iff_hom _).1 ((eq_zero_iff_sv _).1 (h Rel.assoc)) _ _
        (isHom_three hx hy hz)
      rw [relOf, sv_sub, MultilinearMap.sub_apply, sv01_three M M hM hx hy hz,
        sv10_three M M hM hx hy hz, Bool.false_and, σ_false, one_smul, sub_eq_zero] at h1
      exact h1
    · have h1 := (eq_zero_iff_hom _).1 ((eq_zero_iff_sv _).1 (h Rel.sq)) ![p] ![x]
        (fun a => by fin_cases a; exact hx)
      rwa [relOf, sv00_one D D hD hx] at h1
    · have h1 := (eq_zero_iff_hom _).1 ((eq_zero_iff_sv _).1 (h Rel.order)) _ _
        (isHom_three hx hy hz)
      simp only [relOf, sv_sub, MultilinearMap.sub_apply, sv_order₁ M D hM hD hx hy hz,
        sv_order₂ M D hM hD hDv hx hy hz, sv_order₃ M D hM hD hDv hx hy hz] at h1
      rw [← sub_eq_zero, ← h1]
      abel
  · intro hG n r
    rw [eq_zero_iff_sv, eq_zero_iff_hom]
    intro c v hv
    cases r
    · rw [vec_two v]
      have hx : IsP (R := R) (c 0) (v 0) := hv 0
      have hy : IsP (R := R) (c 1) (v 1) := hv 1
      rw [relOf, sv_sub, MultilinearMap.sub_apply, sv_swap_two M hx hy,
        ← hG.comm _ _ _ _ hx hy, sub_self]
    · rw [vec_three v]
      have hx : IsP (R := R) (c 0) (v 0) := hv 0
      have hy : IsP (R := R) (c 1) (v 1) := hv 1
      have hz : IsP (R := R) (c 2) (v 2) := hv 2
      rw [relOf, sv_sub, MultilinearMap.sub_apply, sv01_three M M hM hx hy hz,
        sv10_three M M hM hx hy hz, Bool.false_and, σ_false, one_smul,
        hG.assoc _ _ _ _ _ _ hx hy hz, sub_self]
    · rw [show v = ![v 0] by funext a; fin_cases a; rfl]
      have hx : IsP (R := R) (c 0) (v 0) := hv 0
      rw [relOf, sv00_one D D hD hx]
      exact hG.sq _ _ hx
    · rw [vec_three v]
      have hx : IsP (R := R) (c 0) (v 0) := hv 0
      have hy : IsP (R := R) (c 1) (v 1) := hv 1
      have hz : IsP (R := R) (c 2) (v 2) := hv 2
      simp only [relOf, sv_sub, MultilinearMap.sub_apply, sv_order₁ M D hM hD hx hy hz,
        sv_order₂ M D hM hD hDv hx hy hz, sv_order₃ M D hM hD hDv hx hy hz,
        hG.order _ _ _ _ _ _ hx hy hz]
      abel

/-- Values on the generators of `BV`. -/
def genVal {X : ℕ → Type*} (a : X 2) (b : X 1) : ∀ k, BVGen k → X k
  | _, .mul => a
  | _, .op => b

/-- **Algebras over `BV` are the Batalin–Vilkovisky algebras**: a morphism of graded operads
`BV → End_V` is an even product and an odd operator on `V` satisfying the identities of
`BV.IsBV`. -/
noncomputable def algebraEquiv :
    GrAlgebra R V (BVOp R)
      ≃ {md : EndOp R V (Fin 2) × EndOp R V (Fin 1) // IsBV md.1 md.2} where
  toFun φ := by
    refine ⟨(sv (φ.app _ (FreeGr.presGen (rel R) BVGen.mul)),
      sv (φ.app _ (FreeGr.presGen (rel R) BVGen.op))), ?_⟩
    let Φ := φ.comp (GrOperadIdeal.span R (rel R)).projHom
    have hpar : ∀ {k : ℕ} (e : BVGen k), GrOperad.par (R := R) (bvPar k e)
        (Φ.app (Fin k) (FreeGr.gen e)) = Φ.app (Fin k) (FreeGr.gen e) := fun e => by
      rw [← Φ.app_par, FreeGr.par_gen]
    refine (relOf_eq_zero_iff (Φ.app _ (μ R)) (Φ.app _ (Δ R))
      ((Ger.sv_par_eq_iff _ _).1 (hpar .mul)) ((Ger.sv_par_eq_iff _ _).1 (hpar .op))).1
      fun r => ?_
    rw [← app_relOf]
    show φ.app _ ((GrOperadIdeal.span R (rel R)).proj _ _) = 0
    rw [((GrOperadIdeal.span R (rel R)).proj_eq_zero_iff _).2
      (GrOperadIdeal.subset_span _ ⟨r, rfl⟩), map_zero]
  invFun md := by
    refine FreeGr.presHomEquiv.symm ⟨⟨genVal (X := fun k => EndGr R V (Fin k))
      (ofFam (LinOrd.std 2) md.1.1) (ofFam (LinOrd.std 1) md.1.2), ?_⟩, ?_⟩
    · intro k e
      cases e
      · exact (Ger.sv_par_eq_iff _ _).2 (by
          show parML R V false (sv (ofFam (LinOrd.std 2) md.1.1))
            = sv (ofFam (LinOrd.std 2) md.1.1)
          rw [sv, ofFam_fam]
          exact md.2.par_m)
      · exact (Ger.sv_par_eq_iff _ _).2 (by
          show parML R V true (sv (ofFam (LinOrd.std 1) md.1.2))
            = sv (ofFam (LinOrd.std 1) md.1.2)
          rw [sv, ofFam_fam]
          exact md.2.par_d)
    · rintro n _ ⟨r, rfl⟩
      rw [app_relOf, μ, Δ, FreeGr.homEquiv_symm_gen, FreeGr.homEquiv_symm_gen]
      refine (relOf_eq_zero_iff _ _ ?_ ?_).2 ?_ r
      · show parML R V false (sv (ofFam (LinOrd.std 2) md.1.1))
          = sv (ofFam (LinOrd.std 2) md.1.1)
        rw [sv, ofFam_fam]
        exact md.2.par_m
      · show parML R V true (sv (ofFam (LinOrd.std 1) md.1.2))
          = sv (ofFam (LinOrd.std 1) md.1.2)
        rw [sv, ofFam_fam]
        exact md.2.par_d
      · show IsBV (sv (ofFam (LinOrd.std 2) md.1.1)) (sv (ofFam (LinOrd.std 1) md.1.2))
        rw [sv, sv, ofFam_fam, ofFam_fam]
        exact md.2
  left_inv φ := FreeGr.pres_hom_ext fun k e => by
    rw [FreeGr.presHomEquiv_symm_gen]
    cases e
    · exact ofFam_eq _ _
    · exact ofFam_eq _ _
  right_inv md := Subtype.ext (Prod.ext (by
      show sv ((FreeGr.presHomEquiv.symm _).app _ (FreeGr.presGen (rel R) BVGen.mul)) = _
      rw [FreeGr.presHomEquiv_symm_gen]
      exact ofFam_fam _ _) (by
      show sv ((FreeGr.presHomEquiv.symm _).app _ (FreeGr.presGen (rel R) BVGen.op)) = _
      rw [FreeGr.presHomEquiv_symm_gen]
      exact ofFam_fam _ _))

end BV

end Operad
