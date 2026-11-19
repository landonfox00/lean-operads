/-
# The hypercommutative operad in arity five: thirty-four operations span

**Thirty-four operations span `HyperCom(5)`**, over any commutative ring
(`HyperCom.span_basis34`). They are (`HyperCom.basis34`): the iterated product; `m₅`;
`m₃(x₀ x₁ x₂, x₃, x₄)`; `m₄(x₀ x₁, x₂, x₃, x₄)`; the ten operations `m₃(x_S) · x_d · x_e`, for
the triples `S` of inputs; the ten operations `m₃(m₃(x_S), x_d, x_e)`; the five operations
`m₂(m₃(m₂(x_i, x_j), x_k, x_l), x_e)`; and the five operations `m₂(m₄(…), x_k)`. They are
independent over a field in which `2` and `3` are invertible (`Operad.HyperComFiveDim`).

* **Decomposition** (`HyperCom.mem_span_dec`). An operation of arity five is a combination of
  relabellings of `m₅` and of composites `x ∘ᵢ y` of two operations with at least two inputs
  each: these span a suboperad containing the generators.
* **Composites of two totally symmetric operations** (`SymOperad.twoOp`). A relabelling of
  `x ∘ᵢ y`, for `x` and `y` totally symmetric, only depends on the set `S` of the images of the
  inner inputs (`SymOperad.map_comp_eq_twoOp`), and relabelling moves `S`
  (`SymOperad.map_twoOp`). The WDVV composites are of this form
  (`HyperCom.proj_wTerm_eq_twoOp`), and the WDVV relation of arity five reads
  `m₄(m₂(xᵢ, xⱼ), …) + m₃(m₃(xᵢ, xⱼ, x_l), …) + m₃(m₃(xᵢ, xⱼ, x_m), …) + m₂(m₄(…), x_k)`
  symmetric in `j` and `k` (`HyperCom.wdvv_five`).
* **A span stable under relabelling** (`HyperCom.sp0`, `HyperCom.map_mem_sp0`): the iterated
  product, `m₅`, the products `m₂(y, x_e)` of an operation `y` of arity four with an input, the
  operations `m₃(x_S) · x_d · x_e` and `m₃(m₃(x_S), x_d, x_e)`. With the seven operations
  spanning arity four, every composite is in this span or is a relabelling of
  `m₃(x_a x_b x_c, x_d, x_e)` or of `m₄(x_a x_b, …)`, up to the span (`HyperCom.mem_spP`): `m₂`
  at an input of `m₂(m₃(…), x_a)` is in the span, by the two associativity axioms
  (`HyperCom.comp_tOp_m2_mem`), and `m₂` at an input of `m₃(m₂(xᵢ, xⱼ), …)` other than `i` and
  `j` is reduced to the input `i` by the WDVV relation of arity four
  (`HyperCom.comp_pOp_m2_mem`).
* **The two remaining families.** The operations `m₄(x_a x_b, …)` agree modulo the span, by the
  WDVV relation of arity five (`HyperCom.pOp5_sub_mem_sp0`). The operations
  `m₃(x_a x_b x_c, x_d, x_e)` agree modulo the span (`HyperCom.bq5_sub_mem_sp0`): the WDVV
  relation of arity four with `m₂` at the input `i` exchanges an input of the product with an
  input outside it (`HyperCom.bq5_cross`), so the relabellings moving such an operation by an
  element of the span form a subgroup containing every transposition
  (`HyperCom.bqStab_eq_top`).
* **The span is in the span of the thirty-four** (`HyperCom.sp0_le_sp34`): a product
  `m₂(y, x_e)` is reduced to `y` among the seven operations of arity four
  (`HyperCom.mE_mem34`).
-/
import Operad.HyperComFour
import Operad.HyperComCubic

universe u

namespace Operad

open Sym Finset SetOperad

namespace HyperCom

variable {R : Type u} [CommRing R]

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-! ## Decomposable operations -/

variable (R) in
/-- **The decomposable operations** with inputs `A`: the relabellings of the composites of two
operations with at least two inputs each. -/
def dec (A : Type) [Fintype A] [DecidableEq A] : Set (HyperComOp R A) :=
  {z | ∃ (a b : ℕ) (i : Fin a) (x : HyperComOp R (Fin a)) (y : HyperComOp R (Fin b))
    (e : Without (Fin a) i ⊕ Fin b ≃ A), 2 ≤ a ∧ 2 ≤ b ∧
      z = SymOperad.map (R := R) e (SymOperad.comp (R := R) i x y)}

variable (R) in
/-- The relabellings of the generator `m₅`. -/
def gen5 (A : Type) [Fintype A] [DecidableEq A] : Set (HyperComOp R A) :=
  {z | ∃ e : Fin 5 ≃ A, z = SymOperad.map (R := R) e (opGen 5 (by norm_num))}

variable (R) in
/-- The suboperad of the decomposition in arity five: spanned by the relabellings of `m₅` and
the decomposable operations in arity five, and everything in the other arities. -/
noncomputable def dec5 (A : Type) [Fintype A] [DecidableEq A] : Submodule R (HyperComOp R A) :=
  if Fintype.card A = 5 then Submodule.span R (gen5 R A ∪ dec R A) else ⊤

lemma map_mem_dec (e : A ≃ B) {z : HyperComOp R A} (hz : z ∈ dec R A) :
    SymOperad.map (R := R) e z ∈ dec R B := by
  obtain ⟨a, b, i, x, y, f, ha, hb, rfl⟩ := hz
  exact ⟨a, b, i, x, y, f.trans e, ha, hb, (SymOperad.map_trans (R := R) f e _).symm⟩

lemma map_mem_dec5 (e : A ≃ B) {z : HyperComOp R A} (hz : z ∈ dec5 R A) :
    SymOperad.map (R := R) e z ∈ dec5 R B := by
  have hc := Fintype.card_congr e
  unfold dec5 at hz ⊢
  split_ifs at hz ⊢ with h₁ h₂ h₂
  · refine (Submodule.span_le.2 ?_ : Submodule.span R (gen5 R A ∪ dec R A) ≤
      (Submodule.span R (gen5 R B ∪ dec R B)).comap (SymOperad.map (R := R) e)) hz
    rintro y (⟨f, rfl⟩ | hy)
    · exact Submodule.subset_span
        (Or.inl ⟨f.trans e, (SymOperad.map_trans (R := R) f e _).symm⟩)
    · exact Submodule.subset_span (Or.inr (map_mem_dec e hy))
  · exact absurd (hc ▸ h₁) h₂
  · exact Submodule.mem_top
  · exact Submodule.mem_top

lemma comp_mem_dec5 (i : A) {x : HyperComOp R A} {y : HyperComOp R B} (hx : x ∈ dec5 R A)
    (hy : y ∈ dec5 R B) : SymOperad.comp (R := R) i x y ∈ dec5 R (Without A i ⊕ B) := by
  have hc := card_comp (Y := B) i
  by_cases h5 : Fintype.card (Without A i ⊕ B) = 5
  swap
  · unfold dec5
    rw [if_neg h5]
    exact Submodule.mem_top
  have hA1 := Fintype.card_pos_iff.2 ⟨i⟩
  by_cases hB0 : Fintype.card B = 0
  · haveI := subsingleton_of_card (R := R) hB0
    rw [Subsingleton.elim y 0, map_zero]
    exact zero_mem _
  by_cases hA : Fintype.card A = 1
  · haveI : Subsingleton A := Fintype.card_le_one_iff_subsingleton.1 (by omega)
    have hx' := mem_span_basic (R := R) (by omega) x
    refine (Submodule.span_le.2 ?_ : Submodule.span R (basic R A) ≤
      (dec5 R (Without A i ⊕ B)).comap ((SymOperad.comp (R := R) i).flip y)) hx'
    rintro z (⟨e, rfl⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩)
    · show SymOperad.comp (R := R) i (SymOperad.map (R := R) e (SymOperad.one R)) y
        ∈ dec5 R (Without A i ⊕ B)
      obtain rfl : e () = i := Subsingleton.elim _ _
      have h1 := SymOperad.map_comp (R := R) e (Equiv.refl B) () (SymOperad.one R) y
      rw [SymOperad.map_refl] at h1
      have h2 := congrArg (SymOperad.map (R := R) (leftUnitEquiv B).symm)
        (SymOperad.one_comp (R := R) y)
      rw [SymOperad.map_symm_map] at h2
      rw [← h1, h2]
      exact map_mem_dec5 _ (map_mem_dec5 _ hy)
    · exact absurd (Fintype.card_congr e) (by simp [hA])
    · exact absurd (Fintype.card_congr e) (by simp [hA])
    · exact absurd (Fintype.card_congr e) (by rw [card_W, hA]; norm_num)
  by_cases hB : Fintype.card B = 1
  · have hy' := mem_span_basic (R := R) (by omega) y
    refine (Submodule.span_le.2 ?_ : Submodule.span R (basic R B) ≤
      (dec5 R (Without A i ⊕ B)).comap (SymOperad.comp (R := R) i x)) hy'
    rintro z (⟨e, rfl⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩)
    · show SymOperad.comp (R := R) i x (SymOperad.map (R := R) e (SymOperad.one R))
        ∈ dec5 R (Without A i ⊕ B)
      have h1 := SymOperad.map_comp (R := R) (Equiv.refl A) e i x (SymOperad.one R)
      rw [SymOperad.map_refl] at h1
      have h2 := congrArg (SymOperad.map (R := R) (rightUnitEquiv i).symm)
        (SymOperad.comp_one (R := R) i x)
      rw [SymOperad.map_symm_map] at h2
      have h3 : SymOperad.comp (R := R) i x (SymOperad.map (R := R) e (SymOperad.one R))
          = SymOperad.map (R := R) (compEquiv (Equiv.refl A) e i)
            (SymOperad.map (R := R) (rightUnitEquiv i).symm x) := by
        rw [← h2]
        exact h1.symm
      rw [h3]
      exact map_mem_dec5 _ (map_mem_dec5 _ hx)
    · exact absurd (Fintype.card_congr e) (by simp [hB])
    · exact absurd (Fintype.card_congr e) (by simp [hB])
    · exact absurd (Fintype.card_congr e) (by rw [card_W, hB]; norm_num)
  unfold dec5
  rw [if_pos h5]
  refine Submodule.subset_span (Or.inr ⟨Fintype.card A, Fintype.card B, Fintype.equivFin A i,
    SymOperad.map (R := R) (Fintype.equivFin A) x, SymOperad.map (R := R) (Fintype.equivFin B) y,
    (compEquiv (Fintype.equivFin A) (Fintype.equivFin B) i).symm, by omega, by omega, ?_⟩)
  rw [← SymOperad.map_comp, SymOperad.map_symm_map]

variable (R) in
/-- **The suboperad of the decomposition in arity five.** -/
noncomputable def dec5Sub : SymSuboperad R (HyperComOp R) where
  sub := dec5 R
  map_mem e _ hx := map_mem_dec5 e hx
  one_mem := by
    unfold dec5
    rw [if_neg (by simp)]
    exact Submodule.mem_top
  comp_mem i _ _ hx hy := comp_mem_dec5 i hx hy

/-- **An operation of arity five is a combination of relabellings of `m₅` and of decomposable
operations.** -/
theorem mem_span_dec (hA : Fintype.card A = 5) (x : HyperComOp R A) :
    x ∈ Submodule.span R (gen5 R A ∪ dec R A) := by
  have h : x ∈ dec5 R A := by
    refine SymSuboperad.mem_of_presGen (dec5Sub R) (fun n g => ?_) x
    obtain ⟨hg⟩ := g
    show opGen n hg ∈ dec5 R (Fin n)
    unfold dec5
    split_ifs with h
    · have h5 : n = 5 := by simpa using h
      subst h5
      exact Submodule.subset_span
        (Or.inl ⟨Equiv.refl _, (SymOperad.map_refl (R := R) _).symm⟩)
    · exact Submodule.mem_top
  unfold dec5 at h
  rwa [if_pos hA] at h

end HyperCom

/-! ## Composites of two symmetric operations -/

namespace SymOperad

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]

/-- **A composite at any input of a totally symmetric operation is a relabelling of the composite
at a given input**, the inner inputs staying in place. -/
lemma comp_eq_map_comp {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {x : P X} (hx : ∀ σ : Equiv.Perm X, map (R := R) σ x = x) (i j : X) (y : P Y) :
    ∃ E : Without X i ⊕ Y ≃ Without X j ⊕ Y,
      comp (R := R) j x y = map (R := R) E (comp (R := R) i x y) ∧
        ∀ b, E (Sum.inr b) = Sum.inr b := by
  obtain ⟨σ, rfl⟩ : ∃ σ : Equiv.Perm X, σ i = j := ⟨Equiv.swap i j, Equiv.swap_apply_left _ _⟩
  have h := map_comp (R := R) σ (Equiv.refl Y) i x y
  rw [hx, map_refl] at h
  exact ⟨compEquiv σ (Equiv.refl Y) i, h.symm, fun b => by simp⟩

/-- Composing with a relabelled operation, the outer inputs staying in place. -/
lemma comp_map_right_sum {X Y Y' : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [Fintype Y'] [DecidableEq Y'] (τ : Y ≃ Y') (i : X) (x : P X) (y : P Y) :
    comp (R := R) i x (map (R := R) τ y)
      = map (R := R) (Equiv.sumCongr (Equiv.refl (Without X i)) τ) (comp (R := R) i x y) := by
  rw [comp_map_right_of_eq]
  exact congrArg (fun e => map (R := R) e (comp (R := R) i x y))
    (Equiv.ext fun w => by rcases w with ⟨a, ha⟩ | b <;> rfl)

variable {p q n : ℕ}

/-- **The composite of two totally symmetric operations with the inner inputs at a set `S`**:
a relabelling of `x ∘ᵢ y` sending the inputs of `y` onto `S`, and zero if there is none. It does
not depend on the relabelling (`SymOperad.map_comp_eq_twoOp`). -/
noncomputable def twoOp (x : P (Fin p)) (y : P (Fin q)) (i : Fin p) (S : Finset (Fin n)) :
    P (Fin n) :=
  @dite _ (∃ E : Without (Fin p) i ⊕ Fin q ≃ Fin n,
      Finset.univ.image (fun b => E (Sum.inr b)) = S) (Classical.propDecidable _)
    (fun h => map (R := R) h.choose (comp (R := R) i x y)) (fun _ => 0)

/-- **A relabelling of a composite of two totally symmetric operations is the composite with the
inner inputs at their image.** -/
theorem map_comp_eq_twoOp {x : P (Fin p)} {y : P (Fin q)}
    (hx : ∀ σ : Equiv.Perm (Fin p), map (R := R) σ x = x)
    (hy : ∀ τ : Equiv.Perm (Fin q), map (R := R) τ y = y) (i : Fin p)
    (E : Without (Fin p) i ⊕ Fin q ≃ Fin n) :
    map (R := R) E (comp (R := R) i x y)
      = twoOp (R := R) x y i (Finset.univ.image fun b => E (Sum.inr b)) := by
  have h : ∃ E' : Without (Fin p) i ⊕ Fin q ≃ Fin n,
      Finset.univ.image (fun b => E' (Sum.inr b))
        = Finset.univ.image (fun b => E (Sum.inr b)) := ⟨E, rfl⟩
  rw [twoOp, dif_pos h]
  refine map_comp_eq_of_symm i hx hy E _ fun b => ?_
  have hb : E (Sum.inr b) ∈ Finset.univ.image (fun b => h.choose (Sum.inr b)) := by
    rw [h.choose_spec]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ b)
  obtain ⟨b', -, hb'⟩ := Finset.mem_image.1 hb
  exact ⟨b', hb'.symm⟩

/-- The same at any input of the outer operation. -/
theorem map_comp_eq_twoOp' {x : P (Fin p)} {y : P (Fin q)}
    (hx : ∀ σ : Equiv.Perm (Fin p), map (R := R) σ x = x)
    (hy : ∀ τ : Equiv.Perm (Fin q), map (R := R) τ y = y) (i j : Fin p)
    (E : Without (Fin p) j ⊕ Fin q ≃ Fin n) :
    map (R := R) E (comp (R := R) j x y)
      = twoOp (R := R) x y i (Finset.univ.image fun b => E (Sum.inr b)) := by
  obtain ⟨F, hF, hF'⟩ := comp_eq_map_comp (R := R) hx i j y
  rw [hF, ← map_trans, map_comp_eq_twoOp hx hy]
  congr 1
  refine Finset.image_congr fun b _ => ?_
  show E (F (Sum.inr b)) = E (Sum.inr b)
  rw [hF']

/-- **Relabelling the composite moves the set of the inner inputs.** -/
theorem map_twoOp {x : P (Fin p)} {y : P (Fin q)}
    (hx : ∀ σ : Equiv.Perm (Fin p), map (R := R) σ x = x)
    (hy : ∀ τ : Equiv.Perm (Fin q), map (R := R) τ y = y) (i : Fin p)
    (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    map (R := R) σ (twoOp (R := R) x y i S) = twoOp (R := R) x y i (S.image σ) := by
  by_cases h : ∃ E : Without (Fin p) i ⊕ Fin q ≃ Fin n,
      Finset.univ.image (fun b => E (Sum.inr b)) = S
  · obtain ⟨E, rfl⟩ := h
    rw [← map_comp_eq_twoOp hx hy, ← map_trans, map_comp_eq_twoOp hx hy, Finset.image_image]
    rfl
  · have h' : ¬∃ E : Without (Fin p) i ⊕ Fin q ≃ Fin n,
        Finset.univ.image (fun b => E (Sum.inr b)) = S.image σ := by
      rintro ⟨E, hE⟩
      refine h ⟨E.trans σ.symm, ?_⟩
      have := congrArg (Finset.image σ.symm) hE
      rw [Finset.image_image, Finset.image_image] at this
      simpa using this
    rw [twoOp, dif_neg h, map_zero, twoOp, dif_neg h']

omit [SymOperad R P] in
lemma card_image_inr {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {i : X} (E : Without X i ⊕ Y ≃ Fin n) :
    (Finset.univ.image fun b => E (Sum.inr b)).card = Fintype.card Y := by
  rw [Finset.card_image_of_injective _ (fun a b h => Sum.inr_injective (E.injective h)),
    Finset.card_univ]

/-- The composite with the inner inputs at a set of the wrong size is zero. -/
lemma twoOp_eq_zero (x : P (Fin p)) (y : P (Fin q)) (i : Fin p) {S : Finset (Fin n)}
    (h : S.card ≠ q) : twoOp (R := R) x y i S = 0 := by
  rw [twoOp, dif_neg]
  rintro ⟨E, rfl⟩
  exact h ((card_image_inr E).trans (Fintype.card_fin q))

end SymOperad

/-! ## The WDVV relation of arity five -/

namespace HyperCom

open HCAlg

variable {R : Type u} [CommRing R]

local notation "I" => SymOperadIdeal.span R (hcRel R)

/-- **A WDVV composite, in the operad**: the relabelling of `m_{|Sᶜ|+1} ∘₀ m_{|S|}` sending
the inner inputs to `S` and the others to `Sᶜ`, in increasing order. -/
lemma proj_wTerm_gen {n : ℕ} (S : Finset (Fin n)) (h : 2 ≤ S.card ∧ 1 ≤ Sᶜ.card) :
    (I).proj _ (wTerm (R := R) S)
      = SymOperad.map (R := R) (wEquiv S)
        (SymOperad.comp (R := R) (0 : Fin (Sᶜ.card + 1)) (opGen (Sᶜ.card + 1) (by omega))
          (opGen S.card h.1)) := by
  unfold wTerm
  rw [dif_pos h]
  have h0 : (Finsupp.single (Pres.mk (.map (wEquiv S)
      (.comp 0 (gen (Sᶜ.card + 1) (by omega)) (gen S.card h.1)))) (1 : R) : FreeHC R (Fin n))
      = SymOperad.map (R := R) (P := FreeHC R) (wEquiv S)
        (SymOperad.comp (R := R) (0 : Fin (Sᶜ.card + 1))
          (Finsupp.single (Pres.gen (⟨by omega⟩ : HCGen (Sᶜ.card + 1))) 1)
          (Finsupp.single (Pres.gen (⟨h.1⟩ : HCGen S.card)) 1)) := by
    show _ = Lin.mapL R (wEquiv S) (Lin.compL R 0 _ _)
    rw [Lin.compL_single, Lin.mapL_single, mul_one]
    rfl
  rw [h0, ← SymOperadIdeal.projHom_app, SymOperadHom.app_map, SymOperadHom.app_comp]
  rfl

lemma image_wEquiv_inr {n : ℕ} (S : Finset (Fin n)) :
    Finset.univ.image (fun b => wEquiv S (Sum.inr b)) = S := by
  simp only [wEquiv_inr]
  exact Finset.image_orderEmbOfFin_univ S rfl

/-- **A WDVV composite is the composite of two generators with the inner inputs at `S`.** -/
lemma proj_wTerm_eq_twoOp {n p q : ℕ} (S : Finset (Fin n)) (hq : S.card = q)
    (hp : Sᶜ.card + 1 = p) (h2 : 2 ≤ q) (hp2 : 2 ≤ p) (i : Fin p) :
    (I).proj _ (wTerm (R := R) S)
      = SymOperad.twoOp (R := R) (opGen p hp2) (opGen q h2) i S := by
  subst hq hp
  rw [proj_wTerm_gen S ⟨h2, by omega⟩, SymOperad.map_comp_eq_twoOp' (fun σ => map_opGen _ σ)
    (fun τ => map_opGen _ τ) i 0, image_wEquiv_inr]

variable (R) in
/-- **The operation `m₄(m₂(x_S), …)`**, for a pair `S` of inputs. -/
noncomputable def pOp5 (S : Finset (Fin 5)) : HyperComOp R (Fin 5) :=
  SymOperad.twoOp (R := R) (opGen 4 (by norm_num)) (opGen 2 le_rfl) 0 S

variable (R) in
/-- **The operation `m₃(m₃(x_S), …)`**, for a triple `S` of inputs. -/
noncomputable def qOp5 (S : Finset (Fin 5)) : HyperComOp R (Fin 5) :=
  SymOperad.twoOp (R := R) (opGen 3 (by norm_num)) (opGen 3 (by norm_num)) 0 S

variable (R) in
/-- **The operation `m₂(m₄(x_S), x_k)`**, for the complement `S` of an input `k`. -/
noncomputable def tOp5 (S : Finset (Fin 5)) : HyperComOp R (Fin 5) :=
  SymOperad.twoOp (R := R) (opGen 2 le_rfl) (opGen 4 (by norm_num)) 0 S

/-- **One side of the WDVV relator of arity five**, in the operad. -/
lemma proj_wdvv_side {i j k l m : Fin 5} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hlm : l ≠ m) (hil : i ≠ l) (him : i ≠ m) (hjl : j ≠ l) (hjm : j ≠ m) (hkl : k ≠ l)
    (hkm : k ≠ m) :
    ∑ S ∈ univ.filter (fun S : Finset (Fin 5) => i ∈ S ∧ j ∈ S ∧ k ∉ S),
        (I).proj _ (wTerm (R := R) S)
      = pOp5 R {i, j} + (qOp5 R {i, j, l} + (qOp5 R {i, j, m} + tOp5 R {k}ᶜ)) := by
  obtain ⟨c1, c2, c3, c4, n1, n2, n3⟩ := fin5_sets i j k l m hij hik hjk hlm hil him hjl hjm
    hkl hkm
  have e1 : (I).proj _ (wTerm (R := R) {i, j}) = pOp5 R {i, j} :=
    proj_wTerm_eq_twoOp _ (Finset.card_pair hij) (by rw [c1, card_three hkl hkm hlm]) _ _ 0
  have e2 : (I).proj _ (wTerm (R := R) {i, j, l}) = qOp5 R {i, j, l} :=
    proj_wTerm_eq_twoOp _ (card_three hij hil hjl) (by rw [c2, Finset.card_pair hkm]) _ _ 0
  have e3 : (I).proj _ (wTerm (R := R) {i, j, m}) = qOp5 R {i, j, m} :=
    proj_wTerm_eq_twoOp _ (card_three hij him hjm) (by rw [c3, Finset.card_pair hkl]) _ _ 0
  have e4 : (I).proj _ (wTerm (R := R) ({k}ᶜ : Finset (Fin 5))) = tOp5 R {k}ᶜ :=
    proj_wTerm_eq_twoOp _ (by rw [c4, card_four hij hil him hjl hjm hlm])
      (by rw [compl_compl, Finset.card_singleton]) _ _ 0
  rw [filter_fin5 i j k l m hij hik hjk hlm hil him hjl hjm hkl hkm, Finset.sum_insert n1,
    Finset.sum_insert n2, Finset.sum_pair n3, e1, e2, e3, e4]

/-- **The WDVV relation of arity five**: for distinct inputs `i, j, k, l, m`,
`m₄(m₂(xᵢ, xⱼ), …) + m₃(m₃(xᵢ, xⱼ, x_l), …) + m₃(m₃(xᵢ, xⱼ, x_m), …) + m₂(m₄(…), x_k)` is
symmetric in `j` and `k`. -/
theorem wdvv_five {i j k l m : Fin 5} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hlm : l ≠ m) (hil : i ≠ l) (him : i ≠ m) (hjl : j ≠ l) (hjm : j ≠ m) (hkl : k ≠ l)
    (hkm : k ≠ m) :
    pOp5 R {i, j} + (qOp5 R {i, j, l} + (qOp5 R {i, j, m} + tOp5 R {k}ᶜ))
      = pOp5 R {i, k} + (qOp5 R {i, k, l} + (qOp5 R {i, k, m} + tOp5 R {j}ᶜ)) := by
  have hrel : wdvv (R := R) i j k ∈ (I).sub (Fin 5) :=
    SymOperadIdeal.subset_span (R := R) 5 (Or.inr ⟨i, j, k, hij, hik, hjk, rfl⟩)
  rw [← SymOperadIdeal.proj_eq_zero_iff, wdvv, map_sub, map_sum, map_sum, sub_eq_zero,
    proj_wdvv_side hij hik hjk hlm hil him hjl hjm hkl hkm,
    proj_wdvv_side hik hij hjk.symm hlm hil him hkl hkm hjl hjm] at hrel
  exact hrel

/-! ## The operations of arity five and their span -/

lemma IsBin.map_perm {A : Type} [Fintype A] [DecidableEq A] {z : HyperComOp R A}
    (hz : IsBin z) (σ : Equiv.Perm A) : SymOperad.map (R := R) σ z = z :=
  (hz.map σ).eq hz

lemma isBin_t3 : IsBin (t3 R) := isBin_c22.map _

variable (R) in
/-- **The binary operation of arity five**: the iterated product of five inputs. -/
noncomputable def bin5 : HyperComOp R (Fin 5) :=
  (ofCom R).app (Fin 5) (Finsupp.single ⟨⟨0⟩⟩ 1)

lemma isBin_bin5 : IsBin (bin5 R) := ⟨_, rfl⟩

variable (R) in
/-- **The operation `m₃(x_S) · x_d · x_e`**, for a triple `S` of inputs with complement
`{d, e}`. -/
noncomputable def tt5 (S : Finset (Fin 5)) : HyperComOp R (Fin 5) :=
  SymOperad.twoOp (R := R) (t3 R) (opGen 3 (by norm_num)) 0 S

variable (R) in
/-- **The operation `m₃(x_a x_b x_c, x_d, x_e)`**, for a triple `S = {a, b, c}` of inputs. -/
noncomputable def bq5 (S : Finset (Fin 5)) : HyperComOp R (Fin 5) :=
  SymOperad.twoOp (R := R) (opGen 3 (by norm_num)) (t3 R) 0 S

/-- **A composite of a binary operation of arity three with `m₃`** is `tt5` at the image of the
inner inputs. -/
lemma map_comp_bin_m3 {X : Type} [Fintype X] [DecidableEq X] (hX : Fintype.card X = 3)
    {b : HyperComOp R X} (hb : IsBin b) (i : X) (E : Without X i ⊕ Fin 3 ≃ Fin 5) :
    SymOperad.map (R := R) E (SymOperad.comp (R := R) i b (opGen 3 (by norm_num)))
      = tt5 R (Finset.univ.image fun t => E (Sum.inr t)) := by
  have hb' : b = SymOperad.map (R := R) (Fintype.equivFinOfCardEq hX).symm (t3 R) :=
    SymOperad.eq_map_symm_of_eq (R := R) _ ((hb.map _).eq isBin_t3).symm
  rw [hb', SymOperad.comp_map_left_of_eq (R := R) (Fintype.equivFinOfCardEq hX).symm
    (Equiv.symm_apply_apply _ i), ← SymOperad.map_trans, tt5,
    SymOperad.map_comp_eq_twoOp' (fun σ => isBin_t3.map_perm σ) (fun τ => map_opGen _ τ) 0]
  rfl

/-- **A composite of `m₃` with a binary operation of arity three** is `bq5` at the image of the
inner inputs. -/
lemma map_comp_m3_bin {X : Type} [Fintype X] [DecidableEq X] (hX : Fintype.card X = 3)
    {b : HyperComOp R X} (hb : IsBin b) (i : Fin 3) (E : Without (Fin 3) i ⊕ X ≃ Fin 5) :
    SymOperad.map (R := R) E (SymOperad.comp (R := R) i (opGen 3 (by norm_num)) b)
      = bq5 R (Finset.univ.image fun w => E (Sum.inr w)) := by
  have hb' : b = SymOperad.map (R := R) (Fintype.equivFinOfCardEq hX).symm (t3 R) :=
    SymOperad.eq_map_symm_of_eq (R := R) _ ((hb.map _).eq isBin_t3).symm
  rw [hb', SymOperad.comp_map_right_sum (R := R), ← SymOperad.map_trans, bq5,
    SymOperad.map_comp_eq_twoOp' (fun σ => map_opGen _ σ) (fun τ => isBin_t3.map_perm τ) 0]
  congr 1
  have h := Finset.image_image (s := (Finset.univ : Finset (Fin 3)))
    (f := (Fintype.equivFinOfCardEq hX).symm) (g := fun w => E (Sum.inr w))
  rw [Finset.image_univ_equiv] at h
  exact h.symm

variable (R) in
/-- **The products with an input**: the relabellings of `m₂(y, x_e)`, for an operation `y` of
arity four. -/
def mset : Set (HyperComOp R (Fin 5)) :=
  {z | ∃ (j : Fin 2) (y : HyperComOp R (Fin 4)) (E : Without (Fin 2) j ⊕ Fin 4 ≃ Fin 5),
    z = SymOperad.map (R := R) E (SymOperad.comp (R := R) j (opGen 2 le_rfl) y)}

lemma mem_mset {Y : Type} [Fintype Y] [DecidableEq Y] (hY : Fintype.card Y = 4) (j : Fin 2)
    (y : HyperComOp R Y) (E : Without (Fin 2) j ⊕ Y ≃ Fin 5) :
    SymOperad.map (R := R) E (SymOperad.comp (R := R) j (opGen 2 le_rfl) y) ∈ mset R := by
  have hy : y = SymOperad.map (R := R) (Fintype.equivFinOfCardEq hY).symm
      (SymOperad.map (R := R) (Fintype.equivFinOfCardEq hY) y) :=
    SymOperad.eq_map_symm_of_eq (R := R) _ rfl
  rw [hy, SymOperad.comp_map_right_sum (R := R), ← SymOperad.map_trans]
  exact ⟨j, _, _, rfl⟩

variable (R) in
/-- **The span of the operations of arity five other than the relabellings of
`m₃(x_a x_b x_c, x_d, x_e)` and `m₄(x_a x_b, …)`**: it is stable under relabelling. -/
noncomputable def sp0 : Submodule R (HyperComOp R (Fin 5)) :=
  Submodule.span R (({bin5 R, opGen 5 (by norm_num)} ∪ mset R)
    ∪ (Set.range (tt5 R) ∪ Set.range (qOp5 R)))

lemma bin5_mem_sp0 : bin5 R ∈ sp0 R :=
  Submodule.subset_span (Or.inl (Or.inl (Or.inl rfl)))

lemma m5_mem_sp0 : opGen (R := R) 5 (by norm_num) ∈ sp0 R :=
  Submodule.subset_span (Or.inl (Or.inl (Or.inr rfl)))

lemma mset_subset_sp0 {z : HyperComOp R (Fin 5)} (hz : z ∈ mset R) : z ∈ sp0 R :=
  Submodule.subset_span (Or.inl (Or.inr hz))

lemma tt5_mem_sp0 (S : Finset (Fin 5)) : tt5 R S ∈ sp0 R :=
  Submodule.subset_span (Or.inr (Or.inl ⟨S, rfl⟩))

lemma qOp5_mem_sp0 (S : Finset (Fin 5)) : qOp5 R S ∈ sp0 R :=
  Submodule.subset_span (Or.inr (Or.inr ⟨S, rfl⟩))

/-- **The span is stable under relabelling.** -/
lemma map_mem_sp0 (σ : Equiv.Perm (Fin 5)) {z : HyperComOp R (Fin 5)} (hz : z ∈ sp0 R) :
    SymOperad.map (R := R) σ z ∈ sp0 R := by
  refine (Submodule.span_le.2 ?_ : sp0 R ≤ (sp0 R).comap (SymOperad.map (R := R) σ)) hz
  rintro y (((rfl | rfl) | ⟨j, y, E, rfl⟩) | (⟨S, rfl⟩ | ⟨S, rfl⟩))
  · show SymOperad.map (R := R) σ (bin5 R) ∈ sp0 R
    rw [isBin_bin5.map_perm]
    exact bin5_mem_sp0
  · show SymOperad.map (R := R) σ (opGen 5 (by norm_num)) ∈ sp0 R
    rw [map_opGen]
    exact m5_mem_sp0
  · exact mset_subset_sp0 ⟨j, y, E.trans σ, (SymOperad.map_trans (R := R) E σ _).symm⟩
  · show SymOperad.map (R := R) σ (tt5 R S) ∈ sp0 R
    rw [tt5, SymOperad.map_twoOp (fun σ => isBin_t3.map_perm σ) (fun τ => map_opGen _ τ)]
    exact tt5_mem_sp0 _
  · show SymOperad.map (R := R) σ (qOp5 R S) ∈ sp0 R
    rw [qOp5, SymOperad.map_twoOp (fun σ => map_opGen _ σ) (fun τ => map_opGen _ τ)]
    exact qOp5_mem_sp0 _

/-- **`m₂` at an input of `m₂(m₃(…), x_a)`** gives an operation of the span. -/
lemma comp_tOp_m2_mem (a s : Fin 4) (E : Without (Fin 4) s ⊕ Fin 2 ≃ Fin 5) :
    SymOperad.map (R := R) E (SymOperad.comp (R := R) s (tOp R a) (opGen 2 le_rfl))
      ∈ sp0 R := by
  obtain ⟨w, hw⟩ := (eT a).surjective s
  rcases w with x | t
  · obtain rfl := eq_slotOne x
    have hp := SymOperad.comp_par_eq (R := R) (show (0 : Fin 2) ≠ 1 by decide)
      (opGen (R := R) 2 le_rfl) (opGen (R := R) 3 (by norm_num)) (opGen (R := R) 2 le_rfl)
    have hc : Fintype.card (Without (Fin 2) 1 ⊕ Fin 2) = 3 := by
      have := card_comp (X := Fin 2) (Y := Fin 2) (1 : Fin 2)
      rw [Fintype.card_fin] at this
      omega
    rw [tOp, SymOperad.comp_map_left_of_eq (R := R) (eT a) hw]
    show SymOperad.map (R := R) E (SymOperad.map (R := R) _
      (SymOperad.comp (R := R) (Sum.inl ⟨1, _⟩)
        (SymOperad.comp (R := R) (0 : Fin 2) (opGen 2 le_rfl) (opGen 3 (by norm_num)))
        (opGen 2 le_rfl))) ∈ sp0 R
    rw [hp, ← SymOperad.map_trans, ← SymOperad.map_trans,
      map_comp_bin_m3 hc (isBin_m2.comp isBin_m2 1)]
    exact tt5_mem_sp0 _
  · have hs := SymOperad.comp_seq_eq (R := R) (0 : Fin 2) t (opGen (R := R) 2 le_rfl)
      (opGen (R := R) 3 (by norm_num)) (opGen (R := R) 2 le_rfl)
    rw [tOp, SymOperad.comp_map_left_of_eq (R := R) (eT a) hw]
    show SymOperad.map (R := R) E (SymOperad.map (R := R) _
      (SymOperad.comp (R := R) (Sum.inr t)
        (SymOperad.comp (R := R) (0 : Fin 2) (opGen 2 le_rfl) (opGen 3 (by norm_num)))
        (opGen 2 le_rfl))) ∈ sp0 R
    rw [hs, ← SymOperad.map_trans, ← SymOperad.map_trans]
    exact mset_subset_sp0 (mem_mset (card_W32 t) 0 _ _)

/-! ### `m₂` at an input of `m₃(m₂(xᵢ, xⱼ), …)` -/

/-- The relabelling of `m₃ ∘₀ (m₂ ∘₀ m₂)` for `m₂` at the input `i` of `m₃(m₂(xᵢ, xⱼ), …)`. -/
noncomputable def fB {i j : Fin 4} (hij : i ≠ j) (E : Without (Fin 4) i ⊕ Fin 2 ≃ Fin 5) :
    Without (Fin 3) 0 ⊕ W ≃ Fin 5 :=
  (seqEquiv (0 : Fin 3) (0 : Fin 2) (Fin 2)).symm.trans
    ((compEquiv' (eP i j) (Equiv.refl (Fin 2)) (eP_zero hij)).trans E)

lemma fB_inr_inr {i j : Fin 4} (hij : i ≠ j) (E : Without (Fin 4) i ⊕ Fin 2 ≃ Fin 5)
    (t : Fin 2) : fB hij E (Sum.inr (Sum.inr t)) = E (Sum.inr t) := rfl

lemma fB_inr_inl {i j : Fin 4} (hij : i ≠ j) (E : Without (Fin 4) i ⊕ Fin 2 ≃ Fin 5) :
    fB hij E (Sum.inr (Sum.inl slotOne)) = E (Sum.inl ⟨j, hij.symm⟩) :=
  congrArg E (congrArg Sum.inl (Subtype.ext (eP_one i j)))

lemma fB_inl {i j : Fin 4} (hij : i ≠ j) (E : Without (Fin 4) i ⊕ Fin 2 ≃ Fin 5)
    (a : Without (Fin 3) 0) :
    ∃ (k : Fin 4) (hk : k ≠ i), k ≠ j ∧ fB hij E (Sum.inl a) = E (Sum.inl ⟨k, hk⟩) := by
  refine ⟨eP i j (Sum.inl a), fun h => ?_, fun h => ?_, rfl⟩
  · exact Sum.inl_ne_inr ((eP i j).injective (h.trans (eP_zero hij).symm))
  · exact Sum.inl_ne_inr ((eP i j).injective (h.trans (eP_one i j).symm))

/-- **`m₂` at the input `i` of `m₃(m₂(xᵢ, xⱼ), …)`** is `m₃` of a product of three inputs. -/
lemma comp_pOp_m2_inner {i j : Fin 4} (hij : i ≠ j) (E : Without (Fin 4) i ⊕ Fin 2 ≃ Fin 5) :
    SymOperad.map (R := R) E (SymOperad.comp (R := R) i (pOp R i j) (opGen 2 le_rfl))
      = bq5 R (Finset.univ.image fun w => fB hij E (Sum.inr w)) := by
  have hs := SymOperad.comp_seq_eq (R := R) (0 : Fin 3) (0 : Fin 2)
    (opGen (R := R) 3 (by norm_num)) (opGen (R := R) 2 le_rfl) (opGen (R := R) 2 le_rfl)
  rw [pOp, SymOperad.comp_map_left_of_eq (R := R) (eP i j) (eP_zero hij)]
  show SymOperad.map (R := R) E (SymOperad.map (R := R) _
    (SymOperad.comp (R := R) (Sum.inr 0)
      (SymOperad.comp (R := R) (0 : Fin 3) (opGen 3 (by norm_num)) (opGen 2 le_rfl))
      (opGen 2 le_rfl))) = _
  rw [hs, ← SymOperad.map_trans, ← SymOperad.map_trans]
  exact map_comp_m3_bin card_W isBin_c22 0 _

variable (R) in
/-- The span, with the operations `m₃(x_a x_b x_c, x_d, x_e)`. -/
noncomputable def spB : Submodule R (HyperComOp R (Fin 5)) :=
  sp0 R ⊔ Submodule.span R (Set.range (bq5 R))

variable (R) in
/-- The span, with the operations `m₃(x_a x_b x_c, x_d, x_e)` and `m₄(x_a x_b, …)`. -/
noncomputable def spP : Submodule R (HyperComOp R (Fin 5)) :=
  spB R ⊔ Submodule.span R (Set.range (pOp5 R))

lemma sp0_le_spB : sp0 R ≤ spB R := le_sup_left

lemma bq5_mem_spB (S : Finset (Fin 5)) : bq5 R S ∈ spB R :=
  (le_sup_right : _ ≤ spB R) (Submodule.subset_span ⟨S, rfl⟩)

lemma spB_le_spP : spB R ≤ spP R := le_sup_left

lemma pOp5_mem_spP (S : Finset (Fin 5)) : pOp5 R S ∈ spP R :=
  (le_sup_right : _ ≤ spP R) (Submodule.subset_span ⟨S, rfl⟩)

/-- **`m₂` at an input of `m₃(m₂(xᵢ, xⱼ), …)`** is in the span with the operations
`m₃(x_a x_b x_c, x_d, x_e)`: at an input other than `i` and `j`, by the WDVV relation of arity
four. -/
lemma comp_pOp_m2_mem {i j : Fin 4} (hij : i ≠ j) (s : Fin 4)
    (E : Without (Fin 4) s ⊕ Fin 2 ≃ Fin 5) :
    SymOperad.map (R := R) E (SymOperad.comp (R := R) s (pOp R i j) (opGen 2 le_rfl))
      ∈ spB R := by
  by_cases hi : s = i
  · subst hi
    rw [comp_pOp_m2_inner hij]
    exact bq5_mem_spB _
  by_cases hj : s = j
  · subst hj
    rw [pOp_comm hij, comp_pOp_m2_inner hij.symm]
    exact bq5_mem_spB _
  have hrel := pOp_add_tOp (R := R) hij (Ne.symm hi) (Ne.symm hj)
  have h1 : pOp R i j = pOp R s i + tOp R j - tOp R s := by
    rw [pOp_comm (R := R) hi, eq_sub_iff_add_eq]
    exact hrel
  rw [h1, map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply, map_sub, map_add,
    comp_pOp_m2_inner hi]
  exact sub_mem (add_mem (bq5_mem_spB _) (sp0_le_spB (comp_tOp_m2_mem j s E)))
    (sp0_le_spB (comp_tOp_m2_mem s s E))

/-- **`m₂` at an input of an operation of arity four** is in the span with the two families. -/
lemma comp_m2_mem (x : HyperComOp R (Fin 4)) (s : Fin 4)
    (E : Without (Fin 4) s ⊕ Fin 2 ≃ Fin 5) :
    SymOperad.map (R := R) E (SymOperad.comp (R := R) s x (opGen 2 le_rfl)) ∈ spP R := by
  have hx : x ∈ Submodule.span R (Set.range (seven R)) := by
    rw [span_seven]
    exact Submodule.mem_top
  refine (Submodule.span_le.2 ?_ : Submodule.span R (Set.range (seven R)) ≤
    (spP R).comap ((SymOperad.map (R := R) E).comp
      ((SymOperad.comp (R := R) s).flip (opGen 2 le_rfl)))) hx
  rintro _ ⟨r, rfl⟩
  show SymOperad.map (R := R) E (SymOperad.comp (R := R) s (seven R r) (opGen 2 le_rfl))
    ∈ spP R
  fin_cases r
  · show SymOperad.map (R := R) E (SymOperad.comp (R := R) s (opGen 4 (by norm_num))
      (opGen 2 le_rfl)) ∈ spP R
    rw [SymOperad.map_comp_eq_twoOp' (fun σ => map_opGen _ σ) (fun τ => map_opGen _ τ) 0]
    exact pOp5_mem_spP _
  · show SymOperad.map (R := R) E (SymOperad.comp (R := R) s (bin4 R) (opGen 2 le_rfl))
      ∈ spP R
    rw [((isBin_bin4.comp isBin_m2 s).map E).eq isBin_bin5]
    exact spB_le_spP (sp0_le_spB bin5_mem_sp0)
  · exact spB_le_spP (comp_pOp_m2_mem (by decide) s E)
  · exact spB_le_spP (sp0_le_spB (comp_tOp_m2_mem 0 s E))
  · exact spB_le_spP (sp0_le_spB (comp_tOp_m2_mem 1 s E))
  · exact spB_le_spP (sp0_le_spB (comp_tOp_m2_mem 2 s E))
  · exact spB_le_spP (sp0_le_spB (comp_tOp_m2_mem 3 s E))

/-- **A product with an operation of arity four** is in the span. -/
lemma comp_two_four_mem (i : Fin 2) (x : HyperComOp R (Fin 2)) (y : HyperComOp R (Fin 4))
    (E : Without (Fin 2) i ⊕ Fin 4 ≃ Fin 5) :
    SymOperad.map (R := R) E (SymOperad.comp (R := R) i x y) ∈ sp0 R := by
  have hx : x ∈ Submodule.span R ({opGen 2 le_rfl} : Set (HyperComOp R (Fin 2))) :=
    Submodule.span_mono basic_two (mem_span_basic (by simp) x)
  refine (Submodule.span_le.2 ?_ : Submodule.span R ({opGen 2 le_rfl} : Set _) ≤
    (sp0 R).comap ((SymOperad.map (R := R) E).comp ((SymOperad.comp (R := R) i).flip y))) hx
  rintro _ rfl
  exact mset_subset_sp0 ⟨i, y, E, rfl⟩

/-- **A composite of two operations of arity three** is in the span with the operations
`m₃(x_a x_b x_c, x_d, x_e)`. -/
lemma comp_three_three_mem (i : Fin 3) (x y : HyperComOp R (Fin 3))
    (E : Without (Fin 3) i ⊕ Fin 3 ≃ Fin 5) :
    SymOperad.map (R := R) E (SymOperad.comp (R := R) i x y) ∈ spB R := by
  have h3 : ∀ z : HyperComOp R (Fin 3),
      z ∈ Submodule.span R (Set.range ![opGen (R := R) 3 (by norm_num), t3 R]) := fun z =>
    Submodule.span_mono basic_three (mem_span_basic (by simp) z)
  refine (Submodule.span_le.2 ?_ : Submodule.span R (Set.range ![opGen (R := R) 3
    (by norm_num), t3 R]) ≤ (spB R).comap ((SymOperad.map (R := R) E).comp
      ((SymOperad.comp (R := R) i).flip y))) (h3 x)
  rintro _ ⟨r, rfl⟩
  show SymOperad.map (R := R) E (SymOperad.comp (R := R) i
    (![opGen (R := R) 3 (by norm_num), t3 R] r) y) ∈ spB R
  refine (Submodule.span_le.2 ?_ : Submodule.span R (Set.range ![opGen (R := R) 3
    (by norm_num), t3 R]) ≤ (spB R).comap ((SymOperad.map (R := R) E).comp
      (SymOperad.comp (R := R) i (![opGen (R := R) 3 (by norm_num), t3 R] r)))) (h3 y)
  rintro _ ⟨r', rfl⟩
  show SymOperad.map (R := R) E (SymOperad.comp (R := R) i
    (![opGen (R := R) 3 (by norm_num), t3 R] r)
    (![opGen (R := R) 3 (by norm_num), t3 R] r')) ∈ spB R
  fin_cases r <;> fin_cases r'
  · show SymOperad.map (R := R) E (SymOperad.comp (R := R) i (opGen 3 (by norm_num))
      (opGen 3 (by norm_num))) ∈ spB R
    rw [SymOperad.map_comp_eq_twoOp' (fun σ => map_opGen _ σ) (fun τ => map_opGen _ τ) 0]
    exact sp0_le_spB (qOp5_mem_sp0 _)
  · show SymOperad.map (R := R) E (SymOperad.comp (R := R) i (opGen 3 (by norm_num))
      (t3 R)) ∈ spB R
    rw [map_comp_m3_bin (by simp) isBin_t3]
    exact bq5_mem_spB _
  · show SymOperad.map (R := R) E (SymOperad.comp (R := R) i (t3 R)
      (opGen 3 (by norm_num))) ∈ spB R
    rw [map_comp_bin_m3 (by simp) isBin_t3]
    exact sp0_le_spB (tt5_mem_sp0 _)
  · show SymOperad.map (R := R) E (SymOperad.comp (R := R) i (t3 R) (t3 R)) ∈ spB R
    rw [((isBin_t3.comp isBin_t3 i).map E).eq isBin_bin5]
    exact sp0_le_spB bin5_mem_sp0

/-- **Every operation of arity five is in the span with the two families.** -/
theorem mem_spP (x : HyperComOp R (Fin 5)) : x ∈ spP R := by
  refine (Submodule.span_le.2 ?_ : Submodule.span R (gen5 R (Fin 5) ∪ dec R (Fin 5)) ≤ spP R)
    (mem_span_dec (by simp) x)
  rintro z (⟨e, rfl⟩ | ⟨a, b, i, x, y, e, ha, hb, rfl⟩)
  · rw [map_opGen]
    exact spB_le_spP (sp0_le_spB m5_mem_sp0)
  · have hc := card_comp (X := Fin a) (Y := Fin b) i
    rw [Fintype.card_congr e, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin] at hc
    obtain rfl | rfl | rfl : a = 2 ∨ a = 3 ∨ a = 4 := by omega
    · obtain rfl : b = 4 := by omega
      exact spB_le_spP (sp0_le_spB (comp_two_four_mem i x y e))
    · obtain rfl : b = 3 := by omega
      exact spB_le_spP (comp_three_three_mem i x y e)
    · obtain rfl : b = 2 := by omega
      have hy : y ∈ Submodule.span R ({opGen 2 le_rfl} : Set (HyperComOp R (Fin 2))) :=
        Submodule.span_mono basic_two (mem_span_basic (by simp) y)
      refine (Submodule.span_le.2 ?_ : Submodule.span R ({opGen 2 le_rfl} : Set _) ≤
        (spP R).comap ((SymOperad.map (R := R) e).comp (SymOperad.comp (R := R) i x))) hy
      rintro _ rfl
      exact comp_m2_mem x i e

/-! ### The operations `m₄(x_a x_b, …)` agree modulo the span -/

lemma tOp5_mem_sp0 (S : Finset (Fin 5)) : tOp5 R S ∈ sp0 R := by
  unfold tOp5 SymOperad.twoOp
  by_cases h : ∃ E : Without (Fin 2) 0 ⊕ Fin 4 ≃ Fin 5,
      Finset.univ.image (fun b => E (Sum.inr b)) = S
  · rw [dif_pos h]
    exact mset_subset_sp0 ⟨0, _, _, rfl⟩
  · rw [dif_neg h]
    exact zero_mem _

lemma pOp5_sub_mem {i j k : Fin 5} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    pOp5 R {i, j} - pOp5 R {i, k} ∈ sp0 R := by
  obtain ⟨l, m, hlm, hil, him, hjl, hjm, hkl, hkm⟩ := fin5_others i j k hij hik hjk
  have h := wdvv_five (R := R) hij hik hjk hlm hil him hjl hjm hkl hkm
  have h' : pOp5 R {i, j} - pOp5 R {i, k}
      = (qOp5 R {i, k, l} + (qOp5 R {i, k, m} + tOp5 R {j}ᶜ))
        - (qOp5 R {i, j, l} + (qOp5 R {i, j, m} + tOp5 R {k}ᶜ)) := by
    rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
  rw [h']
  exact sub_mem (add_mem (qOp5_mem_sp0 _) (add_mem (qOp5_mem_sp0 _) (tOp5_mem_sp0 _)))
    (add_mem (qOp5_mem_sp0 _) (add_mem (qOp5_mem_sp0 _) (tOp5_mem_sp0 _)))

lemma pOp5_zero_sub_mem {a : Fin 5} (ha : a ≠ 0) :
    pOp5 R {0, a} - pOp5 R {0, 1} ∈ sp0 R := by
  by_cases h1 : a = 1
  · rw [h1, sub_self]
    exact zero_mem _
  · exact pOp5_sub_mem (Ne.symm ha) (by decide) h1

/-- **The operations `m₄(x_a x_b, …)` agree modulo the span**, by the WDVV relations of arity
five. -/
theorem pOp5_sub_mem_sp0 {a b : Fin 5} (hab : a ≠ b) :
    pOp5 R {a, b} - pOp5 R {0, 1} ∈ sp0 R := by
  by_cases ha : a = 0
  · subst ha
    exact pOp5_zero_sub_mem (Ne.symm hab)
  by_cases hb : b = 0
  · subst hb
    rw [Finset.pair_comm]
    exact pOp5_zero_sub_mem ha
  have h1 := pOp5_sub_mem (R := R) hab ha hb
  have h2 := pOp5_zero_sub_mem (R := R) ha
  have h : pOp5 R {a, b} - pOp5 R {0, 1}
      = (pOp5 R {a, b} - pOp5 R {a, 0}) + (pOp5 R {0, a} - pOp5 R {0, 1}) := by
    rw [Finset.pair_comm a 0]
    abel
  rw [h]
  exact add_mem h1 h2

lemma image_fin_two {α : Type*} [DecidableEq α] (f : Fin 2 → α) :
    Finset.univ.image f = {f 0, f 1} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Fin.exists_fin_two,
    Finset.mem_insert, Finset.mem_singleton]
  exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩

/-- **Every operation `m₄(x_a x_b, …)` is in the span with one of them.** -/
lemma pOp5_mem (S : Finset (Fin 5)) :
    pOp5 R S ∈ sp0 R ⊔ Submodule.span R {pOp5 R {0, 1}} := by
  by_cases h : ∃ E : Without (Fin 4) 0 ⊕ Fin 2 ≃ Fin 5,
      Finset.univ.image (fun b => E (Sum.inr b)) = S
  · obtain ⟨E, rfl⟩ := h
    rw [image_fin_two]
    have hne : E (Sum.inr 0) ≠ E (Sum.inr 1) := fun h => by simpa using E.injective h
    rw [← sub_add_cancel (pOp5 R {E (Sum.inr 0), E (Sum.inr 1)}) (pOp5 R {0, 1})]
    exact add_mem (Submodule.mem_sup_left (pOp5_sub_mem_sp0 hne))
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  · have h0 : pOp5 R S = 0 := by
      unfold pOp5 SymOperad.twoOp
      rw [dif_neg h]
    rw [h0]
    exact zero_mem _

/-! ### The operations `m₃(x_a x_b x_c, x_d, x_e)` agree modulo the span -/

lemma image_fB {i j : Fin 4} (hij : i ≠ j) (E : Without (Fin 4) i ⊕ Fin 2 ≃ Fin 5) :
    Finset.univ.image (fun w => fB hij E (Sum.inr w))
      = {E (Sum.inl ⟨j, hij.symm⟩), E (Sum.inr 0), E (Sum.inr 1)} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨w, rfl⟩
    rcases w with a | t
    · rw [eq_slotOne a, fB_inr_inl]
      exact Or.inl rfl
    · rw [fB_inr_inr]
      fin_cases t
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨Sum.inl slotOne, fB_inr_inl hij E⟩
    · exact ⟨Sum.inr 0, fB_inr_inr hij E 0⟩
    · exact ⟨Sum.inr 1, fB_inr_inr hij E 1⟩

/-- **Exchanging an input of the product with an input outside it** changes
`m₃(x_a x_b x_c, x_d, x_e)` by an operation of the span: the WDVV relation of arity four, with
`m₂` at the input `i`. -/
lemma bq5_cross {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (E : Without (Fin 4) i ⊕ Fin 2 ≃ Fin 5) :
    bq5 R {E (Sum.inl ⟨j, hij.symm⟩), E (Sum.inr 0), E (Sum.inr 1)}
      - bq5 R {E (Sum.inl ⟨k, hik.symm⟩), E (Sum.inr 0), E (Sum.inr 1)} ∈ sp0 R := by
  have hrel := pOp_add_tOp (R := R) hij hik hjk
  have h1 : pOp R i j - pOp R i k = tOp R j - tOp R k :=
    sub_eq_sub_iff_add_eq_add.2 (hrel.trans (add_comm _ _))
  have h2 := congrArg (fun z => SymOperad.map (R := R) E
    (SymOperad.comp (R := R) i z (opGen 2 le_rfl))) h1
  simp only [map_sub, LinearMap.sub_apply] at h2
  rw [comp_pOp_m2_inner hij, comp_pOp_m2_inner hik, image_fB, image_fB] at h2
  rw [h2]
  exact sub_mem (comp_tOp_m2_mem j i E) (comp_tOp_m2_mem k i E)

lemma map_bq5 (σ : Equiv.Perm (Fin 5)) (S : Finset (Fin 5)) :
    SymOperad.map (R := R) σ (bq5 R S) = bq5 R (S.image σ) :=
  SymOperad.map_twoOp (fun σ => map_opGen _ σ) (fun τ => isBin_t3.map_perm τ) 0 σ S

variable (R) in
/-- **The relabellings moving `m₃(x_S, …)`, for a triple `S`, by an operation of the span.** -/
def bqStab (S : Finset (Fin 5)) : Subgroup (Equiv.Perm (Fin 5)) where
  carrier := {σ | bq5 R (S.image σ) - bq5 R S ∈ sp0 R}
  mul_mem' {σ τ} hσ hτ := by
    show bq5 R (S.image (σ * τ)) - bq5 R S ∈ sp0 R
    have h : bq5 R (S.image (σ * τ)) - bq5 R S
        = SymOperad.map (R := R) σ (bq5 R (S.image τ) - bq5 R S)
          + (bq5 R (S.image σ) - bq5 R S) := by
      rw [map_sub, map_bq5, map_bq5, Finset.image_image, ← Equiv.Perm.coe_mul]
      abel
    rw [h]
    exact add_mem (map_mem_sp0 σ hτ) hσ
  one_mem' := by
    show bq5 R (S.image (1 : Equiv.Perm (Fin 5))) - bq5 R S ∈ sp0 R
    rw [Equiv.Perm.coe_one, Finset.image_id, sub_self]
    exact zero_mem _
  inv_mem' {σ} hσ := by
    show bq5 R (S.image (σ⁻¹ : Equiv.Perm (Fin 5))) - bq5 R S ∈ sp0 R
    have h : bq5 R (S.image (σ⁻¹ : Equiv.Perm (Fin 5))) - bq5 R S
        = -SymOperad.map (R := R) σ⁻¹ (bq5 R (S.image σ) - bq5 R S) := by
      rw [map_sub, map_bq5, map_bq5, Finset.image_image, ← Equiv.Perm.coe_mul,
        inv_mul_cancel, Equiv.Perm.coe_one, Finset.image_id, neg_sub]
    rw [h]
    exact neg_mem (map_mem_sp0 _ hσ)

lemma image_eq_of_mapsTo {S : Finset (Fin 5)} (σ : Equiv.Perm (Fin 5))
    (h : ∀ y ∈ S, σ y ∈ S) : S.image σ = S :=
  Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.2 h)
    (Finset.card_image_of_injective S σ.injective).ge

lemma image_swap_of_mem {S : Finset (Fin 5)} {a b : Fin 5} (ha : a ∈ S) (hb : b ∈ S) :
    S.image (Equiv.swap a b) = S :=
  image_eq_of_mapsTo _ fun y hy => by
    by_cases h1 : y = a
    · rw [h1, Equiv.swap_apply_left]
      exact hb
    by_cases h2 : y = b
    · rw [h2, Equiv.swap_apply_right]
      exact ha
    rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
    exact hy

lemma image_swap_of_notMem {S : Finset (Fin 5)} {a b : Fin 5} (ha : a ∉ S) (hb : b ∉ S) :
    S.image (Equiv.swap a b) = S :=
  image_eq_of_mapsTo _ fun y hy => by
    rw [Equiv.swap_apply_of_ne_of_ne (fun h => ha (by rw [← h]; exact hy))
      (fun h => hb (by rw [← h]; exact hy))]
    exact hy

/-- The triple of the inputs of the product for `m₂` at the input `0` of
`m₃(m₂(x₀, x₁), x₂, x₃)`, relabelled by `E`. -/
def sE (E : Without (Fin 4) 0 ⊕ Fin 2 ≃ Fin 5) : Finset (Fin 5) :=
  {E (Sum.inl ⟨1, by decide⟩), E (Sum.inr 0), E (Sum.inr 1)}

lemma cross_mem_bqStab (E : Without (Fin 4) 0 ⊕ Fin 2 ≃ Fin 5) {a b : Fin 5} (ha : a ∈ sE E)
    (hb : b ∉ sE E) : Equiv.swap a b ∈ bqStab R (sE E) := by
  obtain ⟨w, rfl⟩ := E.surjective b
  rcases w with ⟨c, hc⟩ | t
  swap
  · exfalso
    apply hb
    fin_cases t
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hc1 : c ≠ 1 := fun h => hb (by
    subst h
    exact Finset.mem_insert_self _ _)
  have hu : ∀ (t : Fin 2) (d : Without (Fin 4) 0), E (Sum.inr t) ≠ E (Sum.inl d) :=
    fun t d h => Sum.inr_ne_inl (E.injective h)
  have hxy : E (Sum.inl ⟨1, by decide⟩) ≠ E (Sum.inl ⟨c, hc⟩) := fun h =>
    hc1 (congrArg Subtype.val (Sum.inl_injective (E.injective h))).symm
  have hx : Equiv.swap (E (Sum.inl ⟨1, by decide⟩)) (E (Sum.inl ⟨c, hc⟩))
      ∈ bqStab R (sE E) := by
    show bq5 R ((sE E).image _) - bq5 R (sE E) ∈ sp0 R
    have himg : (sE E).image (Equiv.swap (E (Sum.inl ⟨1, by decide⟩)) (E (Sum.inl ⟨c, hc⟩)))
        = {E (Sum.inl ⟨c, hc⟩), E (Sum.inr 0), E (Sum.inr 1)} := by
      rw [sE, Finset.image_insert, Finset.image_insert, Finset.image_singleton,
        Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (hu 0 _) (hu 0 _),
        Equiv.swap_apply_of_ne_of_ne (hu 1 _) (hu 1 _)]
    rw [himg, ← neg_sub]
    exact neg_mem (bq5_cross (R := R) (i := 0) (j := 1) (k := c) (by decide) (Ne.symm hc)
      (Ne.symm hc1) E)
  by_cases hax : a = E (Sum.inl ⟨1, by decide⟩)
  · rw [hax]
    exact hx
  · have hab : E (Sum.inl ⟨c, hc⟩) ≠ a := fun h => hb (h ▸ ha)
    have hxa : Equiv.swap (E (Sum.inl ⟨1, by decide⟩)) a ∈ bqStab R (sE E) := by
      show bq5 R ((sE E).image _) - bq5 R (sE E) ∈ sp0 R
      rw [image_swap_of_mem (S := sE E) (Finset.mem_insert_self _ _) ha, sub_self]
      exact zero_mem _
    have h := Equiv.swap_mul_swap_mul_swap (x := E (Sum.inl ⟨c, hc⟩))
      (y := E (Sum.inl ⟨1, by decide⟩)) (z := a) (Ne.symm hxy) hab
    rw [← h]
    refine mul_mem (mul_mem hxa ?_) hxa
    rw [Equiv.swap_comm]
    exact hx

lemma swap_mem_bqStab (E : Without (Fin 4) 0 ⊕ Fin 2 ≃ Fin 5) (a b : Fin 5) :
    Equiv.swap a b ∈ bqStab R (sE E) := by
  by_cases ha : a ∈ sE E <;> by_cases hb : b ∈ sE E
  · show bq5 R ((sE E).image _) - bq5 R (sE E) ∈ sp0 R
    rw [image_swap_of_mem ha hb, sub_self]
    exact zero_mem _
  · exact cross_mem_bqStab E ha hb
  · rw [Equiv.swap_comm]
    exact cross_mem_bqStab E hb ha
  · show bq5 R ((sE E).image _) - bq5 R (sE E) ∈ sp0 R
    rw [image_swap_of_notMem ha hb, sub_self]
    exact zero_mem _

/-- **Every relabelling moves `m₃(x_a x_b x_c, x_d, x_e)` by an operation of the span.** -/
theorem bqStab_eq_top (E : Without (Fin 4) 0 ⊕ Fin 2 ≃ Fin 5) : bqStab R (sE E) = ⊤ := by
  rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
  rintro σ ⟨a, b, -, rfl⟩
  exact swap_mem_bqStab E a b

lemma exists_equiv_image {p q n : ℕ} (S : Finset (Fin n)) (hq : S.card = q)
    (hp : Sᶜ.card = p) :
    ∃ E : Without (Fin (p + 1)) 0 ⊕ Fin q ≃ Fin n,
      Finset.univ.image (fun b => E (Sum.inr b)) = S := by
  subst hq hp
  exact ⟨wEquiv S, image_wEquiv_inr S⟩

lemma exists_perm_image {S S' : Finset (Fin 5)} {q : ℕ} (h : S.card = q) (h' : S'.card = q) :
    ∃ σ : Equiv.Perm (Fin 5), S.image σ = S' := by
  obtain ⟨p, hp⟩ : ∃ p, Sᶜ.card = p := ⟨_, rfl⟩
  have hp' : S'ᶜ.card = p := by
    rw [← hp, Finset.card_compl, Finset.card_compl, h, h']
  obtain ⟨F, hF⟩ := exists_equiv_image S h hp
  obtain ⟨F', hF'⟩ := exists_equiv_image S' h' hp'
  refine ⟨F.symm.trans F', ?_⟩
  rw [← hF, ← hF', Finset.image_image]
  refine Finset.image_congr fun b _ => ?_
  simp

lemma card_sE (E : Without (Fin 4) 0 ⊕ Fin 2 ≃ Fin 5) : (sE E).card = 3 :=
  card_three (fun h => Sum.inl_ne_inr (E.injective h)) (fun h => Sum.inl_ne_inr (E.injective h))
    (fun h => by simpa using E.injective h)

/-- **The operations `m₃(x_a x_b x_c, x_d, x_e)` agree modulo the span.** -/
theorem bq5_sub_mem_sp0 {S S' : Finset (Fin 5)} (h : S.card = 3) (h' : S'.card = 3) :
    bq5 R S - bq5 R S' ∈ sp0 R := by
  have hc : Fintype.card (Without (Fin 4) 0 ⊕ Fin 2) = 5 := by
    have := card_comp (X := Fin 4) (Y := Fin 2) (0 : Fin 4)
    rw [Fintype.card_fin, Fintype.card_fin] at this
    omega
  obtain ⟨σ, hσ⟩ := exists_perm_image (card_sE (Fintype.equivFinOfCardEq hc)) h
  obtain ⟨σ', hσ'⟩ := exists_perm_image (card_sE (Fintype.equivFinOfCardEq hc)) h'
  have e1 : σ ∈ bqStab R (sE (Fintype.equivFinOfCardEq hc)) := by
    rw [bqStab_eq_top]
    exact Subgroup.mem_top _
  have e2 : σ' ∈ bqStab R (sE (Fintype.equivFinOfCardEq hc)) := by
    rw [bqStab_eq_top]
    exact Subgroup.mem_top _
  have e1' : bq5 R ((sE (Fintype.equivFinOfCardEq hc)).image σ)
      - bq5 R (sE (Fintype.equivFinOfCardEq hc)) ∈ sp0 R := e1
  have e2' : bq5 R ((sE (Fintype.equivFinOfCardEq hc)).image σ')
      - bq5 R (sE (Fintype.equivFinOfCardEq hc)) ∈ sp0 R := e2
  rw [hσ] at e1'
  rw [hσ'] at e2'
  have h3 : bq5 R S - bq5 R S' = (bq5 R S - bq5 R (sE (Fintype.equivFinOfCardEq hc)))
      - (bq5 R S' - bq5 R (sE (Fintype.equivFinOfCardEq hc))) := by abel
  rw [h3]
  exact sub_mem e1' e2'

/-- **Every operation `m₃(x_a x_b x_c, x_d, x_e)` is in the span with one of them.** -/
lemma bq5_mem (S : Finset (Fin 5)) :
    bq5 R S ∈ sp0 R ⊔ Submodule.span R {bq5 R {0, 1, 2}} := by
  by_cases h : S.card = 3
  · rw [← sub_add_cancel (bq5 R S) (bq5 R {0, 1, 2})]
    exact add_mem (Submodule.mem_sup_left (bq5_sub_mem_sp0 h (by decide)))
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  · have h0 : bq5 R S = 0 := SymOperad.twoOp_eq_zero _ _ _ h
    rw [h0]
    exact zero_mem _

/-! ## The thirty-four operations -/

/-- The triples of inputs. -/
abbrev Tri := {S : Finset (Fin 5) // S.card = 3}

lemma card_W24 : Fintype.card (Without (Fin 2) 0 ⊕ Fin 4) = 5 := by
  have := card_comp (X := Fin 2) (Y := Fin 4) (0 : Fin 2)
  rw [Fintype.card_fin, Fintype.card_fin] at this
  omega

/-- A relabelling of the inputs of `m₂ ∘₀ y`, for `y` of arity four, sending the outer input to
`e`. -/
noncomputable def eE (e : Fin 5) : Without (Fin 2) 0 ⊕ Fin 4 ≃ Fin 5 :=
  (Fintype.equivFinOfCardEq card_W24).trans
    (Equiv.swap ((Fintype.equivFinOfCardEq card_W24) (Sum.inl slotOne)) e)

lemma eE_outer (e : Fin 5) : eE e (Sum.inl slotOne) = e := by
  rw [eE, Equiv.trans_apply, Equiv.swap_apply_left]

variable (R) in
/-- **The operation `m₂(m₃(m₂(x_i, x_j), x_k, x_l), x_e)`**, for an input `e` and an order of
the others. -/
noncomputable def eOp5 (e : Fin 5) : HyperComOp R (Fin 5) :=
  SymOperad.map (R := R) (eE e)
    (SymOperad.comp (R := R) (0 : Fin 2) (opGen 2 le_rfl) (pOp R 0 1))

variable (R) in
/-- **The thirty-four operations of arity five**: the iterated product, `m₅`,
`m₃(x₀ x₁ x₂, x₃, x₄)`, `m₄(x₀ x₁, x₂, x₃, x₄)`, the ten operations `m₃(x_S) · x_d · x_e`, the
ten operations `m₃(m₃(x_S), x_d, x_e)`, the five operations
`m₂(m₃(m₂(x_i, x_j), x_k, x_l), x_e)` and the five operations `m₂(m₄(…), x_k)`. -/
noncomputable def basis34 : Fin 4 ⊕ (Tri ⊕ Tri) ⊕ (Fin 5 ⊕ Fin 5) → HyperComOp R (Fin 5) :=
  Sum.elim ![bin5 R, opGen 5 (by norm_num), bq5 R {0, 1, 2}, pOp5 R {0, 1}]
    (Sum.elim (Sum.elim (fun S : Tri => tt5 R S.1) (fun S : Tri => qOp5 R S.1))
      (Sum.elim (eOp5 R) (fun k => tOp5 R {k}ᶜ)))

variable (R) in
/-- The span of the thirty-four operations. -/
noncomputable def sp34 : Submodule R (HyperComOp R (Fin 5)) :=
  Submodule.span R (Set.range (basis34 R))

lemma bin5_mem34 : bin5 R ∈ sp34 R := Submodule.subset_span ⟨Sum.inl 0, rfl⟩

lemma m5_mem34 : opGen (R := R) 5 (by norm_num) ∈ sp34 R :=
  Submodule.subset_span ⟨Sum.inl 1, rfl⟩

lemma bq5_mem34 : bq5 R {0, 1, 2} ∈ sp34 R := Submodule.subset_span ⟨Sum.inl 2, rfl⟩

lemma pOp5_mem34 : pOp5 R {0, 1} ∈ sp34 R := Submodule.subset_span ⟨Sum.inl 3, rfl⟩

lemma tt5_mem34 (S : Finset (Fin 5)) : tt5 R S ∈ sp34 R := by
  by_cases h : S.card = 3
  · exact Submodule.subset_span ⟨Sum.inr (Sum.inl (Sum.inl ⟨S, h⟩)), rfl⟩
  · have h0 : tt5 R S = 0 := SymOperad.twoOp_eq_zero _ _ _ h
    rw [h0]
    exact zero_mem _

lemma qOp5_mem34 (S : Finset (Fin 5)) : qOp5 R S ∈ sp34 R := by
  by_cases h : S.card = 3
  · exact Submodule.subset_span ⟨Sum.inr (Sum.inl (Sum.inr ⟨S, h⟩)), rfl⟩
  · have h0 : qOp5 R S = 0 := SymOperad.twoOp_eq_zero _ _ _ h
    rw [h0]
    exact zero_mem _

lemma eOp5_mem34 (e : Fin 5) : eOp5 R e ∈ sp34 R :=
  Submodule.subset_span ⟨Sum.inr (Sum.inr (Sum.inl e)), rfl⟩

lemma tOp5_mem34 (k : Fin 5) : tOp5 R {k}ᶜ ∈ sp34 R :=
  Submodule.subset_span ⟨Sum.inr (Sum.inr (Sum.inr k)), rfl⟩

/-- The product of an operation of arity four with an input, relabelled by `E`. -/
noncomputable def mE (E : Without (Fin 2) 0 ⊕ Fin 4 ≃ Fin 5) :
    HyperComOp R (Fin 4) →ₗ[R] HyperComOp R (Fin 5) :=
  (SymOperad.map (R := R) E).comp (SymOperad.comp (R := R) (0 : Fin 2) (opGen 2 le_rfl))

lemma mE_apply (E : Without (Fin 2) 0 ⊕ Fin 4 ≃ Fin 5) (y : HyperComOp R (Fin 4)) :
    mE E y = SymOperad.map (R := R) E
      (SymOperad.comp (R := R) (0 : Fin 2) (opGen 2 le_rfl) y) := rfl

/-- The product of `m₂(m₃(…), x_a)` with an input is `m₃` of a triple times the two others. -/
lemma mE_tOp (E : Without (Fin 2) 0 ⊕ Fin 4 ≃ Fin 5) (a : Fin 4) :
    mE (R := R) E (tOp R a) ∈ sp34 R := by
  have hs := SymOperad.comp_assoc_seq (R := R) (0 : Fin 2) (0 : Fin 2)
    (opGen (R := R) 2 le_rfl) (opGen (R := R) 2 le_rfl) (opGen (R := R) 3 (by norm_num))
  rw [mE_apply, tOp, SymOperad.comp_map_right_sum (R := R)]
  show SymOperad.map (R := R) E (SymOperad.map (R := R) _
    (SymOperad.comp (R := R) (0 : Fin 2) (opGen 2 le_rfl)
      (SymOperad.comp (R := R) (0 : Fin 2) (opGen 2 le_rfl) (opGen 3 (by norm_num)))))
    ∈ sp34 R
  rw [← hs, ← SymOperad.map_trans, ← SymOperad.map_trans,
    map_comp_bin_m3 card_W (isBin_m2.comp isBin_m2 0)]
  exact tt5_mem34 _

instance : Subsingleton (Without (Fin 2) 0) :=
  ⟨fun a b => (eq_slotOne a).trans (eq_slotOne b).symm⟩

/-- Two relabellings with the same outer input differ by a relabelling of the operation of arity
four. -/
lemma mE_eq (E E' : Without (Fin 2) 0 ⊕ Fin 4 ≃ Fin 5)
    (h : E (Sum.inl slotOne) = E' (Sum.inl slotOne)) :
    ∃ τ : Equiv.Perm (Fin 4), ∀ y : HyperComOp R (Fin 4),
      mE E y = mE E' (SymOperad.map (R := R) τ y) := by
  have hl : Set.MapsTo (E.trans E'.symm) (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro _ ⟨x, rfl⟩
    refine ⟨slotOne, ?_⟩
    rw [eq_slotOne x, Equiv.trans_apply, h, Equiv.symm_apply_apply]
  obtain ⟨⟨σ₁, τ⟩, hστ⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hl
  obtain rfl : σ₁ = Equiv.refl _ := Subsingleton.elim _ _
  refine ⟨τ, fun y => ?_⟩
  have hE : E = (Equiv.sumCongr (Equiv.refl (Without (Fin 2) 0)) τ).trans E' := by
    have h2 : Equiv.sumCongr (Equiv.refl (Without (Fin 2) 0)) τ = E.trans E'.symm := hστ
    rw [h2]
    exact Equiv.ext fun w => by simp
  rw [mE_apply, mE_apply, SymOperad.comp_map_right_sum (R := R), ← SymOperad.map_trans, ← hE]

/-- **The product of an operation of arity four with an input is in the span of the
thirty-four.** -/
lemma mE_mem34 (E : Without (Fin 2) 0 ⊕ Fin 4 ≃ Fin 5) (y : HyperComOp R (Fin 4)) :
    mE E y ∈ sp34 R := by
  have hy : y ∈ Submodule.span R (Set.range (seven R)) := by
    rw [span_seven]
    exact Submodule.mem_top
  refine (Submodule.span_le.2 ?_ : Submodule.span R (Set.range (seven R)) ≤
    (sp34 R).comap (mE E)) hy
  rintro _ ⟨r, rfl⟩
  show mE E (seven R r) ∈ sp34 R
  fin_cases r
  · show mE E (opGen 4 (by norm_num)) ∈ sp34 R
    rw [mE_apply, SymOperad.map_comp_eq_twoOp (fun σ => map_opGen _ σ)
      (fun τ => map_opGen _ τ)]
    have hk : (Finset.univ.image fun b => E (Sum.inr b)) = {E (Sum.inl slotOne)}ᶜ := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_compl,
        Finset.mem_singleton]
      constructor
      · rintro ⟨b, rfl⟩ hb
        exact Sum.inr_ne_inl (E.injective hb)
      · intro hx
        obtain ⟨w, rfl⟩ := E.surjective x
        rcases w with a | b
        · exact absurd (by rw [eq_slotOne a]) hx
        · exact ⟨b, rfl⟩
    rw [hk]
    exact tOp5_mem34 _
  · show mE E (bin4 R) ∈ sp34 R
    rw [mE_apply, ((isBin_m2.comp isBin_bin4 0).map E).eq isBin_bin5]
    exact bin5_mem34
  · show mE E (pOp R 0 1) ∈ sp34 R
    obtain ⟨τ, hτ⟩ := mE_eq (R := R) E (eE (E (Sum.inl slotOne))) (eE_outer _).symm
    rw [hτ, pOp, ← SymOperad.map_trans, map_c32_eq_pOp]
    have hne : ((eP 0 1).trans τ) (Sum.inr 0) ≠ ((eP 0 1).trans τ) (Sum.inr 1) := fun h => by
      simpa using ((eP 0 1).trans τ).injective h
    rw [← sub_add_cancel (pOp R (((eP 0 1).trans τ) (Sum.inr 0))
      (((eP 0 1).trans τ) (Sum.inr 1))) (pOp R 0 1), map_add]
    refine add_mem ?_ (eOp5_mem34 _)
    refine (Submodule.span_le.2 ?_ : tSpan R ≤ (sp34 R).comap (mE _)) (pOp_sub_mem_tSpan hne)
    rintro _ ⟨a, rfl⟩
    exact mE_tOp _ a
  · exact mE_tOp E 0
  · exact mE_tOp E 1
  · exact mE_tOp E 2
  · exact mE_tOp E 3

lemma sp0_le_sp34 : sp0 R ≤ sp34 R := by
  refine Submodule.span_le.2 ?_
  rintro z (((rfl | rfl) | ⟨j, y, E, rfl⟩) | (⟨S, rfl⟩ | ⟨S, rfl⟩))
  · exact bin5_mem34
  · exact m5_mem34
  · obtain ⟨F, hF, -⟩ := SymOperad.comp_eq_map_comp (R := R)
      (fun σ => map_opGen (R := R) le_rfl σ) (0 : Fin 2) j y
    rw [hF, ← SymOperad.map_trans]
    exact mE_mem34 _ y
  · exact tt5_mem34 S
  · exact qOp5_mem34 S

/-- **The thirty-four operations span the operations of arity five.** -/
theorem span_basis34 : Submodule.span R (Set.range (basis34 R)) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have hb : sp0 R ⊔ Submodule.span R {bq5 R {0, 1, 2}} ≤ sp34 R :=
    sup_le sp0_le_sp34 ((Submodule.span_singleton_le_iff_mem _ _).2 bq5_mem34)
  have hp : sp0 R ⊔ Submodule.span R {pOp5 R {0, 1}} ≤ sp34 R :=
    sup_le sp0_le_sp34 ((Submodule.span_singleton_le_iff_mem _ _).2 pOp5_mem34)
  have hB : spB R ≤ sp34 R := sup_le sp0_le_sp34 (Submodule.span_le.2 (by
    rintro _ ⟨S, rfl⟩
    exact hb (bq5_mem S)))
  have hP : spP R ≤ sp34 R := sup_le hB (Submodule.span_le.2 (by
    rintro _ ⟨S, rfl⟩
    exact hp (pOp5_mem S)))
  exact hP (mem_spP x)

end HyperCom

end Operad
