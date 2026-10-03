/-
# The graded decomposition cooperad of a twisted linearization

A set operad `S` with finite factorizations (`SetOperad.FiniteFact`) and sign data `δ` has a
twisted linearization `SgnLin R δ`, a graded operad (`SgnLin.instGrOperad`). It is also a
**graded cooperad** (`SgnLin.instGrCooperad`): an operation decomposes as the signed sum of its
factorizations,

  `Δᵢ x = ∑_{p ∘ᵢ q = x} σ(sgn i p q) p ⊗ q`,

the sign being that of the composite (`SgnData.sgn`). On coefficients, the coefficient of `p ⊗ q`
in `Δᵢ x` is the sign of `p ∘ᵢ q` times the coefficient of `p ∘ᵢ q` in `x` (`SgnLin.decompT_apply`),
so that every axiom of a graded cooperad is the corresponding axiom of `S`, read on coefficients,
together with the corresponding property of the sign: the cocycle conditions `SgnData.sgn_seq` and
`SgnData.sgn_par` for coassociativity, the latter matching the Koszul sign of the super swap.

When the units of `S` only factor into units (`SetOperad.UnitFact`), the unit is a coaugmentation
(`SgnLin.instCoaug`). This is the case of the free set operad on generators of any arity, the
regular operad of planar trees (`FreeGr.instUnitFact`), so that **the free graded operad
`FreeGr R gp` is a coaugmented graded cooperad**, decomposing a tree as the signed sum of its cuts.
-/
import Operad.FreeGraded
import Operad.GrCooperad

universe u v w

namespace Operad

open Sym GerBV
open scoped TensorProduct

/-! ## Signed pullbacks of finitely supported functions -/

section SFinComap

variable {R : Type u} [CommRing R]

/-- **The signed pullback** of a finitely supported function along a map with finite fibers:
`x ↦ (a ↦ s a * x (c a))`. -/
noncomputable def sfinComap {X Y : Type*} (s : X → R) (c : X → Y)
    (hc : ∀ y, (c ⁻¹' {y}).Finite) : (Y →₀ R) →ₗ[R] (X →₀ R) where
  toFun x := Finsupp.ofSupportFinite (fun a => s a * x (c a)) (by
    refine (x.support.finite_toSet.biUnion fun y _ => hc y).subset fun a ha => ?_
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_coe]
    refine ⟨c a, Finsupp.mem_support_iff.2 fun h => ha ?_, rfl⟩
    simp [h])
  map_add' x y := by
    ext a
    simp [Finsupp.ofSupportFinite_coe, mul_add]
  map_smul' r x := by
    ext a
    simp only [Finsupp.ofSupportFinite_coe, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

@[simp] lemma sfinComap_apply {X Y : Type*} (s : X → R) (c : X → Y)
    (hc : ∀ y, (c ⁻¹' {y}).Finite) (x : Y →₀ R) (a : X) :
    sfinComap s c hc x a = s a * x (c a) :=
  rfl

/-- Two diagonal maps of tensor products, on coefficients. -/
lemma tens_map_diag {X Y : Type*} (f : (X →₀ R) →ₗ[R] (X →₀ R)) (g : (Y →₀ R) →ₗ[R] (Y →₀ R))
    (u : X → R) (w : Y → R) (hf : ∀ x a, f x a = u a * x a) (hg : ∀ y b, g y b = w b * y b)
    (t : (X →₀ R) ⊗[R] (Y →₀ R)) (a : X) (b : Y) :
    tens R X Y (TensorProduct.map f g t) (a, b) = u a * w b * tens R X Y t (a, b) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [TensorProduct.map_tmul, tens_tmul_apply, hf, hg]
    ring
  | add t t' ht ht' => simp only [map_add, Finsupp.add_apply, ht, ht', mul_add]

/-- **The super swap of the last two factors, on coefficients**, for diagonal parity
projections. -/
lemma tens3'_sswapLast {X Y Z : Type w} (pY : Bool → (Y →₀ R) →ₗ[R] (Y →₀ R))
    (pZ : Bool → (Z →₀ R) →ₗ[R] (Z →₀ R)) (cY : Y → Bool) (cZ : Z → Bool)
    (hY : ∀ q y b, pY q y b = if cY b = q then y b else 0)
    (hZ : ∀ r z d, pZ r z d = if cZ d = r then z d else 0)
    (t : ((X →₀ R) ⊗[R] (Y →₀ R)) ⊗[R] (Z →₀ R)) (a : X) (b : Y) (d : Z) :
    tens3' R X Z Y (sswapLast R pY pZ t) ((a, d), b)
      = σ R (cY b && cZ d) * tens3' R X Y Z t ((a, b), d) := by
  have : (Finsupp.lapply ((a, d), b)) ∘ₗ (tens3' R X Z Y).toLinearMap ∘ₗ sswapLast R pY pZ
      = σ R (cY b && cZ d) • ((Finsupp.lapply ((a, b), d)) ∘ₗ (tens3' R X Y Z).toLinearMap) :=
    TensorProduct.ext_threefold fun x y z => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, sswapLast_tmul, Fintype.sum_bool,
        map_add, map_smul, Finsupp.lapply_apply, tens3'_tmul_apply, smul_eq_mul,
        LinearMap.smul_apply]
      simp only [hY, hZ]
      cases cY b <;> cases cZ d <;> simp <;> ring
  exact LinearMap.congr_fun this t

/-- Decomposing the second factor with signs, on coefficients. -/
lemma tens3_lTensor_s {X Y Y₁ Y₂ : Type*} (g : (Y →₀ R) →ₗ[R] (Y₁ →₀ R) ⊗[R] (Y₂ →₀ R))
    (s : Y₁ × Y₂ → R) (c : Y₁ × Y₂ → Y) (hg : ∀ y p, tens R Y₁ Y₂ (g y) p = s p * y (c p))
    (t : (X →₀ R) ⊗[R] (Y →₀ R)) (a : X) (p : Y₁ × Y₂) :
    tens3 R X Y₁ Y₂ (LinearMap.lTensor (X →₀ R) g t) (a, p) = s p * tens R X Y t (a, c p) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    obtain ⟨b, d⟩ := p
    have h := hg y (b, d)
    simp only [LinearMap.lTensor_tmul, tens_tmul_apply, tens3, LinearEquiv.trans_apply,
      TensorProduct.congr_tmul, LinearEquiv.refl_apply, h]
    ring
  | add t t' ht ht' => simp only [map_add, Finsupp.add_apply, ht, ht', mul_add]

/-- Decomposing the first factor with signs, on coefficients. -/
lemma tens3'_rTensor_s {X X₁ X₂ Z : Type*} (g : (X →₀ R) →ₗ[R] (X₁ →₀ R) ⊗[R] (X₂ →₀ R))
    (s : X₁ × X₂ → R) (c : X₁ × X₂ → X) (hg : ∀ x p, tens R X₁ X₂ (g x) p = s p * x (c p))
    (t : (X →₀ R) ⊗[R] (Z →₀ R)) (p : X₁ × X₂) (d : Z) :
    tens3' R X₁ X₂ Z (LinearMap.rTensor (Z →₀ R) g t) (p, d) = s p * tens R X Z t (c p, d) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x z =>
    obtain ⟨a, b⟩ := p
    have h := hg x (a, b)
    simp only [LinearMap.rTensor_tmul, tens_tmul_apply, tens3', LinearEquiv.trans_apply,
      TensorProduct.congr_tmul, LinearEquiv.refl_apply, h]
    ring
  | add t t' ht ht' => simp only [map_add, Finsupp.add_apply, ht, ht', mul_add]

end SFinComap

/-! ## Units factoring into units -/

/-- **The units only factor into units**: a factorization of a relabelled unit consists of
relabelled units. -/
class SetOperad.UnitFact (S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    [SetOperad S] : Prop where
  /-- The factors of a relabelled unit are relabelled units. -/
  fact {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (e : Unit ≃ Without A i ⊕ B) (p : S A) (q : S B) :
    SetOperad.comp i p q = SetOperad.map e SetOperad.one →
      (∃ e₁ : Unit ≃ A, p = SetOperad.map e₁ SetOperad.one) ∧
        ∃ e₂ : Unit ≃ B, q = SetOperad.map e₂ SetOperad.one

/-! ## The graded decomposition cooperad -/

namespace SgnLin

variable {R : Type u} [CommRing R]
  {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  [SetOperad.FiniteFact S] (δ : SetOperadHom S SgnD)
variable {A A' B B' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] [Fintype D] [DecidableEq D]

variable (R) in
/-- **The decomposition**: `Δᵢ x = ∑_{p ∘ᵢ q = x} σ(sgn i p q) p ⊗ q`. -/
noncomputable def decompT (i : A) :
    (S (Without A i ⊕ B) →₀ R) →ₗ[R] (S A →₀ R) ⊗[R] (S B →₀ R) :=
  (tens R (S A) (S B)).symm.toLinearMap ∘ₗ
    sfinComap (fun pq : S A × S B => σ R (SgnData.sgn i (δ.app A pq.1) (δ.app B pq.2)))
      (fun pq : S A × S B => SetOperad.comp i pq.1 pq.2) (SetOperad.FiniteFact.finite i)

/-- **The coefficients of a decomposition**: the coefficient of `p ⊗ q` in `Δᵢ x` is the sign of
`p ∘ᵢ q` times the coefficient of `p ∘ᵢ q` in `x`. -/
lemma decompT_apply (i : A) (x : S (Without A i ⊕ B) →₀ R) (pq : S A × S B) :
    tens R (S A) (S B) (decompT R δ i x) pq
      = σ R (SgnData.sgn i (δ.app A pq.1) (δ.app B pq.2)) * x (SetOperad.comp i pq.1 pq.2) := by
  simp [decompT]

omit [SetOperad.FiniteFact S] in
lemma parT_apply (b : Bool) (x : S A →₀ R) (a : S A) :
    parT R δ b x a = if (δ.app A a).tot = b then x a else 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' =>
    rw [map_add, Finsupp.add_apply, hx, hx', Finsupp.add_apply]
    split_ifs <;> simp
  | single s r =>
    rw [parT_single]
    by_cases h : (δ.app A s).tot = b
    · rw [if_pos h]
      by_cases hs : s = a
      · subst hs
        rw [if_pos h]
      · rw [Finsupp.single_eq_of_ne (Ne.symm hs)]
        split_ifs <;> simp
    · rw [if_neg h, Finsupp.zero_apply]
      by_cases hs : s = a
      · subst hs
        rw [if_neg h]
      · split_ifs <;> simp [Finsupp.single_eq_of_ne (Ne.symm hs)]

/-- **Decomposition preserves parities.** -/
lemma decompT_parT (i : A) (b : Bool) :
    decompT R δ (B := B) i ∘ₗ parT R δ b
      = tpar R (fun c => parT R δ c) (fun c => parT R δ c) b ∘ₗ decompT R δ i := by
  refine LinearMap.ext fun x => (tens R (S A) (S B)).injective (Finsupp.ext fun ⟨p, q⟩ => ?_)
  have hd : ∀ c (y : S A →₀ R) a, parT R δ c y a
      = (if (δ.app A a).tot = c then 1 else 0) * y a := fun c y a => by
    rw [parT_apply]
    split_ifs <;> simp
  have hd' : ∀ c (y : S B →₀ R) a, parT R δ c y a
      = (if (δ.app B a).tot = c then 1 else 0) * y a := fun c y a => by
    rw [parT_apply]
    split_ifs <;> simp
  rw [LinearMap.comp_apply, LinearMap.comp_apply, decompT_apply, parT_apply, tpar,
    LinearMap.add_apply, map_add, Finsupp.add_apply, tens_map_diag _ _ _ _ (hd false) (hd' b),
    tens_map_diag _ _ _ _ (hd true) (hd' (!b)), decompT_apply, δ.app_comp, SgnData.comp_def,
    SgnData.comp_tot]
  cases (δ.app A p).tot <;> cases (δ.app B q).tot <;> cases b <;> simp

/-- **Decomposition is equivariant.** -/
lemma decompT_map (σ' : A ≃ A') (τ : B ≃ B') (i : A) :
    decompT R δ (σ' i) ∘ₗ Lin.mapL R (compEquiv σ' τ i)
      = TensorProduct.map (Lin.mapL R σ') (Lin.mapL R τ) ∘ₗ decompT R δ i :=
  LinearMap.ext fun x => (tens R (S A') (S B')).injective (Finsupp.ext fun ⟨p, q⟩ => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, decompT_apply, Lin.mapL_apply,
      tens_map _ _ _ _ (Lin.mapL_apply σ') (Lin.mapL_apply τ), decompT_apply]
    have hs : SgnData.sgn (σ' i) (δ.app A' p) (δ.app B' q)
        = SgnData.sgn i (δ.app A (SetOperad.map σ'.symm p)) (δ.app B (SetOperad.map τ.symm q)) := by
      rw [δ.app_map, δ.app_map, SgnData.map_def, SgnData.map_def]
      have h := SgnData.sgn_map σ'.symm τ.symm (σ' i) (δ.app A' p) (δ.app B' q)
      rw [Equiv.symm_apply_apply] at h
      exact h.symm
    rw [hs]
    congr 2
    rw [← SetOperad.map_symm_map (compEquiv σ' τ i) (SetOperad.comp i _ _),
      SetOperad.map_comp, SetOperad.map_map_symm, SetOperad.map_map_symm])

/-- The right counit law. -/
lemma decompT_counit_right (i : A) :
    (TensorProduct.rid R (S A →₀ R)).toLinearMap ∘ₗ
        LinearMap.lTensor (S A →₀ R) (Finsupp.lapply SetOperad.one) ∘ₗ
          decompT R δ (B := Unit) i ∘ₗ Lin.mapL R (rightUnitEquiv i).symm
      = LinearMap.id :=
  LinearMap.ext fun x => Finsupp.ext fun a => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, rid_lTensor_lapply, decompT_apply,
      Lin.mapL_apply, Equiv.symm_symm, SetOperad.comp_one, LinearMap.id_apply, δ.app_one,
      SgnData.one_def, SgnData.sgn_one_right, σ_false, one_mul]

/-- The left counit law. -/
lemma decompT_counit_left :
    (TensorProduct.lid R (S B →₀ R)).toLinearMap ∘ₗ
        LinearMap.rTensor (S B →₀ R) (Finsupp.lapply SetOperad.one) ∘ₗ decompT R δ () ∘ₗ
          Lin.mapL R (leftUnitEquiv B).symm
      = LinearMap.id :=
  LinearMap.ext fun x => Finsupp.ext fun b => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, lid_rTensor_lapply, decompT_apply,
      Lin.mapL_apply, Equiv.symm_symm, SetOperad.one_comp, LinearMap.id_apply, δ.app_one,
      SgnData.one_def, SgnData.sgn_one_left, σ_false, one_mul]

/-- **Sequential coassociativity.** -/
lemma decompT_assoc_seq (i : A) (j : B) :
    LinearMap.lTensor (S A →₀ R) (decompT R δ (B := D) j) ∘ₗ decompT R δ i
      = (TensorProduct.assoc R (S A →₀ R) (S B →₀ R) (S D →₀ R)).toLinearMap ∘ₗ
          LinearMap.rTensor (S D →₀ R) (decompT R δ i) ∘ₗ decompT R δ (Sum.inr j) ∘ₗ
            Lin.mapL R (seqEquiv i j D).symm :=
  LinearMap.ext fun x => (tens3 R (S A) (S B) (S D)).injective (Finsupp.ext fun ⟨a, b, d⟩ => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [tens3_lTensor_s _ _ _ (decompT_apply δ j), decompT_apply, tens3_assoc,
      tens3'_rTensor_s _ _ _ (decompT_apply δ i), decompT_apply, Lin.mapL_apply,
      Equiv.symm_symm, SetOperad.comp_assoc_seq]
    have key := congrArg (σ R) (SgnData.sgn_seq i j (δ.app A a) (δ.app B b) (δ.app D d))
    rw [σ_xor, σ_xor, ← SgnData.comp_def, ← SgnData.comp_def, ← δ.app_comp,
      ← δ.app_comp] at key
    linear_combination (-x (SetOperad.comp i a (SetOperad.comp j b d))) * key)

/-- **Parallel coassociativity, up to the Koszul sign** of the super swap. -/
lemma decompT_assoc_par {i k : A} (hik : i ≠ k) :
    LinearMap.rTensor (S B →₀ R) (decompT R δ (B := D) k) ∘ₗ decompT R δ (Sum.inl ⟨i, hik⟩)
      = sswapLast R (fun c => parT R δ c) (fun c => parT R δ c) ∘ₗ
          LinearMap.rTensor (S D →₀ R) (decompT R δ i) ∘ₗ
            decompT R δ (Sum.inl ⟨k, Ne.symm hik⟩) ∘ₗ Lin.mapL R (parEquiv hik B D).symm :=
  LinearMap.ext fun x => (tens3' R (S A) (S D) (S B)).injective
    (Finsupp.ext fun ⟨⟨a, d⟩, b⟩ => by
      simp only [LinearMap.comp_apply]
      rw [tens3'_rTensor_s _ _ _ (decompT_apply δ k), decompT_apply,
        tens3'_sswapLast _ _ (fun b => (δ.app B b).tot) (fun d => (δ.app D d).tot)
          (fun q y b => parT_apply δ q y b) (fun r z d => parT_apply δ r z d),
        tens3'_rTensor_s _ _ _ (decompT_apply δ i), decompT_apply, Lin.mapL_apply,
        Equiv.symm_symm, SetOperad.comp_assoc_par]
      have key := congrArg (σ R) (SgnData.sgn_par hik (δ.app A a) (δ.app B b) (δ.app D d))
      rw [σ_xor, σ_xor, σ_xor, ← SgnData.comp_def, ← SgnData.comp_def, ← δ.app_comp,
        ← δ.app_comp] at key
      have msq := σ_mul_self R ((δ.app B b).tot && (δ.app D d).tot)
      linear_combination (-σ R ((δ.app B b).tot && (δ.app D d).tot)
          * x (SetOperad.comp (Sum.inl ⟨i, hik⟩) (SetOperad.comp k a d) b)) * key
        - (σ R (SgnData.sgn k (δ.app A a) (δ.app D d))
          * σ R (SgnData.sgn (Sum.inl ⟨i, hik⟩) (δ.app _ (SetOperad.comp k a d)) (δ.app B b))
          * x (SetOperad.comp (Sum.inl ⟨i, hik⟩) (SetOperad.comp k a d) b)) * msq)

omit [SetOperad.FiniteFact S] in
/-- The counit is even. -/
lemma counit_parT : Finsupp.lapply (R := R) (SetOperad.one : S Unit) ∘ₗ parT R δ true = 0 :=
  LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, Finsupp.lapply_apply, parT_apply, δ.app_one, SgnData.one_def,
      SgnData.one_tot]
    rfl

variable (R) in
/-- **The graded decomposition cooperad of a twisted linearization.** -/
noncomputable instance instGrCooperad : GrCooperad R (SgnLin R δ) where
  toGrSpecies := GrOperad.toGrSpecies R (SgnLin R δ)
  counit := Finsupp.lapply SetOperad.one
  counit_par := counit_parT δ
  decomp i := decompT R δ i
  decomp_par i b := decompT_parT δ i b
  decomp_map σ' τ i := decompT_map δ σ' τ i
  counit_right i := decompT_counit_right δ i
  counit_left := decompT_counit_left δ
  decomp_assoc_seq i j := decompT_assoc_seq δ i j
  decomp_assoc_par hik := decompT_assoc_par δ hik

/-! ### The coaugmentation -/

/-- The relabellings of the unit, in the twisted linearization. -/
lemma map_single_one (e : Unit ≃ A) :
    SymSpecies.map (R := R) (V := SgnLin R δ) e (Finsupp.single SetOperad.one 1)
      = Finsupp.single (SetOperad.map e SetOperad.one) 1 :=
  Lin.mapL_single e _ 1

/-- The factorizations of an operation, as a finite set. -/
lemma mem_fact_iff (i : A) (t : S (Without A i ⊕ B)) (pq : S A × S B) :
    pq ∈ (SetOperad.FiniteFact.finite i t).toFinset ↔ SetOperad.comp i pq.1 pq.2 = t := by
  rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]

/-- **The decomposition of a basis element**: the signed sum of its factorizations. -/
lemma decompT_single (i : A) (t : S (Without A i ⊕ B)) (r : R) :
    decompT R δ i (Finsupp.single t r)
      = ∑ pq ∈ (SetOperad.FiniteFact.finite i t).toFinset,
          (σ R (SgnData.sgn i (δ.app A pq.1) (δ.app B pq.2)) * r)
            • (Finsupp.single pq.1 1 ⊗ₜ[R] Finsupp.single pq.2 (1 : R)) := by
  classical
  refine (tens R (S A) (S B)).injective (Finsupp.ext fun ⟨p, q⟩ => ?_)
  rw [decompT_apply, map_sum, Finsupp.finsetSum_apply]
  simp only [map_smul, Finsupp.smul_apply, tens_tmul_apply, Finsupp.single_apply, smul_eq_mul]
  by_cases h : SetOperad.comp i p q = t
  · rw [if_pos h.symm, Finset.sum_eq_single (p, q)]
    · simp
    · rintro ⟨p', q'⟩ _ hne
      by_cases h1 : p' = p
      · subst h1
        have h2 : ¬ q' = q := fun h2 => hne (by rw [h2])
        simp [h2]
      · simp [h1]
    · intro hn
      exact absurd ((mem_fact_iff i t (p, q)).2 h) hn
  · rw [if_neg (Ne.symm h), mul_zero]
    refine (Finset.sum_eq_zero fun pq hpq => ?_).symm
    have hpq' : SetOperad.comp i pq.1 pq.2 = t := (mem_fact_iff i t pq).1 hpq
    by_cases h1 : pq.1 = p
    · by_cases h2 : pq.2 = q
      · exact absurd (by rw [← h1, ← h2]; exact hpq') h
      · simp [h2]
    · simp [h1]

variable [SetOperad.UnitFact S]

variable (R) in
/-- **The unit is a coaugmentation**, when the units only factor into units. -/
noncomputable instance instCoaug : GrCooperad.Coaug R (SgnLin R δ) where
  one := Finsupp.single SetOperad.one 1
  par_one := parT_one
  counit_one := by
    show Finsupp.lapply SetOperad.one (Finsupp.single (SetOperad.one : S Unit) (1 : R)) = 1
    simp
  decomp_mem {A B} _ _ _ _ i e := by
    show decompT R δ i (SymSpecies.map (R := R) (V := SgnLin R δ) e
      (Finsupp.single SetOperad.one 1)) ∈ _
    rw [map_single_one, decompT_single]
    refine Submodule.sum_mem _ fun pq hpq => Submodule.smul_mem _ _ ?_
    have hf : SetOperad.comp i pq.1 pq.2 = SetOperad.map e SetOperad.one :=
      (mem_fact_iff i _ pq).1 hpq
    obtain ⟨⟨e₁, h₁⟩, ⟨e₂, h₂⟩⟩ := SetOperad.UnitFact.fact i e pq.1 pq.2 hf
    refine Submodule.apply_mem_map₂ (TensorProduct.mk R _ _) ?_ ?_
    · exact Submodule.subset_span ⟨e₁, (map_single_one δ e₁).trans (by rw [h₁])⟩
    · exact Submodule.subset_span ⟨e₂, (map_single_one δ e₂).trans (by rw [h₂])⟩

end SgnLin

/-! ## The free graded operad as a graded cooperad -/

namespace FreeGr

open TreeOfArity

variable {T : ℕ → Type v}

/-- A graft is the trivial tree only when both trees are. -/
lemma graft_eq_leaf {s u : Tree T} {p : ℕ} (h : s.graft p u = .leaf) :
    s = .leaf ∧ u = .leaf := by
  cases s with
  | leaf => exact ⟨rfl, by simpa using h⟩
  | node e f => simp at h

/-- An operation with the trivial tree is a relabelled unit. -/
lemma eq_map_one_of_leaf {A : Type} [Fintype A] [DecidableEq A] (x : Reg (TreeOfArity T) A)
    (hx : treeOf x = .leaf) :
    ∃ e : Unit ≃ A, x = SetOperad.map e (SetOperad.one : Reg (TreeOfArity T) Unit) := by
  have hcard : Fintype.card A = 1 := by
    rw [← x.2.2, ← treeOf_arity, hx]
    rfl
  have hsub : Subsingleton A := Fintype.card_le_one_iff_subsingleton.1 hcard.le
  refine ⟨Fintype.equivOfCardEq (by rw [hcard]; rfl), Reg.ext (LinOrd.eq_of_subsingleton _ _)
    (arr_ext ?_)⟩
  exact hx

/-- **In the regular operad of planar trees, the units only factor into units.** -/
instance instUnitFact : SetOperad.UnitFact (Reg (TreeOfArity T)) where
  fact {A B} _ _ _ _ i e p q h := by
    have ht := congrArg treeOf h
    rw [treeOf_comp] at ht
    obtain ⟨hp, hq⟩ := graft_eq_leaf ht
    exact ⟨eq_map_one_of_leaf p hp, eq_map_one_of_leaf q hq⟩

end FreeGr

end Operad
