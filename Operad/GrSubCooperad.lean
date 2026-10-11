/-
# Subcooperads of graded cooperads

* **A subcooperad of a graded cooperad** (`GrSubCooperad`): submodules stable under the parity
  projections and the relabellings, whose decompositions lie in the image of `K ⊗ K`.
* **Sums of subcooperads are subcooperads** (`GrSubCooperad.sSup`), so **every family of
  submodules contains a largest subcooperad** (`GrSubCooperad.cogen`, `GrSubCooperad.cogen_le`,
  `GrSubCooperad.le_cogen`).
* Over a field the tensor products of the inclusions are injective, so the decompositions
  restrict: **a subcooperad is a graded cooperad** (`GrSubCooperad.instGrCooperad`), and the
  inclusion is a morphism of graded cooperads (`GrSubCooperad.inclHom`). The span of the
  coaugmentation is a subcooperad (`GrSubCooperad.unitSub`), and a subcooperad containing it is
  coaugmented (`GrSubCooperad.instCoaug`).
* **Precomposing with a morphism of graded cooperads is a morphism of convolution operads**
  (`ConvOp.preHom`).
-/
import Operad.GrCoideal
import Operad.ConvOperad
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

universe u v w x

namespace Operad

open Sym GerBV
open scoped TensorProduct

/-! ## Subcooperads and their sums -/

section Lattice

variable {R : Type u} [CommRing R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]

variable (R C) in
/-- **A subcooperad of a graded cooperad**: submodules stable under the parity projections and the
relabellings, whose decompositions lie in the image of `K ⊗ K`. -/
structure GrSubCooperad where
  /-- The component at a finite input set. -/
  sub (A : Type) [Fintype A] [DecidableEq A] : Submodule R (C A)
  par_mem {A : Type} [Fintype A] [DecidableEq A] (b : Bool) {x : C A} :
    x ∈ sub A → GrSpecies.par (R := R) b x ∈ sub A
  map_mem {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    {x : C A} : x ∈ sub A → SymSpecies.map (R := R) e x ∈ sub B
  decomp_mem {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    {x : C (Without A i ⊕ B)} : x ∈ sub (Without A i ⊕ B) →
      GrCooperad.decomp (R := R) i x
        ∈ LinearMap.range (TensorProduct.map (sub A).subtype (sub B).subtype)

namespace GrSubCooperad

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

lemma ext {K L : GrSubCooperad R C}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A], K.sub A = L.sub A) : K = L := by
  obtain ⟨K, _, _, _⟩ := K
  obtain ⟨L, _, _, _⟩ := L
  have : @K = @L := by
    funext A _ _
    exact h A
  subst this
  rfl

/-- **Subcooperads are ordered by inclusion**, input set by input set. -/
instance : PartialOrder (GrSubCooperad R C) where
  le K L := ∀ (A : Type) [Fintype A] [DecidableEq A], K.sub A ≤ L.sub A
  le_refl _ _ _ _ := le_rfl
  le_trans _ _ _ hKL hLM A _ _ := (hKL A).trans (hLM A)
  le_antisymm _ _ hKL hLK := ext fun A _ _ => le_antisymm (hKL A) (hLK A)

omit [GrCooperad R C] in
/-- The image of `p ⊗ q` grows with `p` and `q`. -/
lemma range_map_subtype_mono {p p' : Submodule R (C A)} {q q' : Submodule R (C B)}
    (hp : p ≤ p') (hq : q ≤ q') :
    LinearMap.range (TensorProduct.map p.subtype q.subtype)
      ≤ LinearMap.range (TensorProduct.map p'.subtype q'.subtype) := by
  have h : TensorProduct.map p.subtype q.subtype = TensorProduct.map p'.subtype q'.subtype ∘ₗ
      TensorProduct.map (Submodule.inclusion hp) (Submodule.inclusion hq) := by
    rw [← TensorProduct.map_comp, Submodule.subtype_comp_inclusion,
      Submodule.subtype_comp_inclusion]
  rw [h]
  exact LinearMap.range_comp_le_range _ _

/-- **The sum of a set of subcooperads is a subcooperad.** -/
def sSup (S : Set (GrSubCooperad R C)) : GrSubCooperad R C where
  sub A _ _ := ⨆ K : S, K.1.sub A
  par_mem := by
    intro A _ _ b x hx
    refine Submodule.iSup_induction (fun K : S => K.1.sub A)
      (motive := fun x => GrSpecies.par (R := R) b x ∈ ⨆ K : S, K.1.sub A) hx ?_ ?_ ?_
    · exact fun K x hx => Submodule.mem_iSup_of_mem K (K.1.par_mem b hx)
    · beta_reduce
      rw [map_zero]
      exact zero_mem _
    · intro x y hx hy
      beta_reduce at hx hy ⊢
      rw [map_add]
      exact add_mem hx hy
  map_mem := by
    intro A B _ _ _ _ e x hx
    refine Submodule.iSup_induction (fun K : S => K.1.sub A)
      (motive := fun x => SymSpecies.map (R := R) e x ∈ ⨆ K : S, K.1.sub B) hx ?_ ?_ ?_
    · exact fun K x hx => Submodule.mem_iSup_of_mem K (K.1.map_mem e hx)
    · beta_reduce
      rw [map_zero]
      exact zero_mem _
    · intro x y hx hy
      beta_reduce at hx hy ⊢
      rw [map_add]
      exact add_mem hx hy
  decomp_mem := by
    intro A B _ _ _ _ i x hx
    refine Submodule.iSup_induction (fun K : S => K.1.sub (Without A i ⊕ B))
      (motive := fun x => GrCooperad.decomp (R := R) i x ∈ LinearMap.range
        (TensorProduct.map (⨆ K : S, K.1.sub A).subtype (⨆ K : S, K.1.sub B).subtype))
      hx ?_ ?_ ?_
    · exact fun K x hx => range_map_subtype_mono (le_iSup (fun K : S => K.1.sub A) K)
        (le_iSup (fun K : S => K.1.sub B) K) (K.1.decomp_mem i hx)
    · beta_reduce
      rw [map_zero]
      exact zero_mem _
    · intro x y hx hy
      beta_reduce at hx hy ⊢
      rw [map_add]
      exact add_mem hx hy

lemma le_sSup {S : Set (GrSubCooperad R C)} {K : GrSubCooperad R C} (hK : K ∈ S) :
    K ≤ sSup S :=
  fun A _ _ => le_iSup (fun K : S => K.1.sub A) ⟨K, hK⟩

/-- **The largest subcooperad contained in a family of submodules.** -/
def cogen (N : ∀ (A : Type) [Fintype A] [DecidableEq A], Submodule R (C A)) :
    GrSubCooperad R C :=
  sSup {K | ∀ (A : Type) [Fintype A] [DecidableEq A], K.sub A ≤ N A}

lemma cogen_le (N : ∀ (A : Type) [Fintype A] [DecidableEq A], Submodule R (C A))
    (A : Type) [Fintype A] [DecidableEq A] : (cogen N).sub A ≤ N A :=
  iSup_le fun K => K.2 A

lemma le_cogen (N : ∀ (A : Type) [Fintype A] [DecidableEq A], Submodule R (C A))
    {K : GrSubCooperad R C} (hK : ∀ (A : Type) [Fintype A] [DecidableEq A], K.sub A ≤ N A) :
    K ≤ cogen N :=
  le_sSup hK

/-! ### The span of the coaugmentation -/

variable [GrCooperad.Coaug R C]

omit [GrCooperad R C] [GrCooperad.Coaug R C] in
/-- The span of the pure tensors of two submodules is the image of their tensor product. -/
lemma map₂_eq_range (p : Submodule R (C A)) (q : Submodule R (C B)) :
    Submodule.map₂ (TensorProduct.mk R (C A) (C B)) p q
      = LinearMap.range (TensorProduct.map p.subtype q.subtype) := by
  apply le_antisymm
  · rw [Submodule.map₂_le]
    intro a ha b hb
    exact ⟨⟨a, ha⟩ ⊗ₜ ⟨b, hb⟩, rfl⟩
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul a b => exact Submodule.apply_mem_map₂ _ a.2 b.2
    | add z z' hz hz' => rw [map_add]; exact add_mem hz hz'

variable (R C) in
/-- **The span of the coaugmentation is a subcooperad.** -/
def unitSub : GrSubCooperad R C where
  sub A _ _ := GrCooperad.unitSpan R C A
  par_mem b _ hx := GrCooperad.unitSpan_le_comap_par b hx
  map_mem e _ hx := GrCooperad.unitSpan_le_comap_map e hx
  decomp_mem := by
    intro A B _ _ _ _ i x hx
    rw [← map₂_eq_range]
    refine Submodule.span_induction (p := fun x _ => GrCooperad.decomp (R := R) i x ∈ _)
      ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨e, rfl⟩
      exact GrCooperad.Coaug.decomp_mem i e
    · beta_reduce
      rw [map_zero]
      exact zero_mem _
    · intro x y _ _ hx hy
      beta_reduce at hx hy ⊢
      rw [map_add]
      exact add_mem hx hy
    · intro a x _ hx
      beta_reduce at hx ⊢
      rw [map_smul]
      exact Submodule.smul_mem _ a hx

end GrSubCooperad

end Lattice

/-! ## Subcooperads are cooperads, over a field -/

section Field

variable {R : Type u} [Field R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]

namespace GrSubCooperad

variable (K : GrSubCooperad R C)
variable {A A' B B' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] [Fintype D] [DecidableEq D]

omit [GrCooperad R C] in
/-- **Over a field, the tensor products of inclusions are injective.** -/
lemma map_subtype_injective (p : Submodule R (C A)) (q : Submodule R (C B)) :
    Function.Injective (TensorProduct.map p.subtype q.subtype) :=
  TensorProduct.map_injective_of_flat_flat _ _ p.subtype_injective q.subtype_injective

/-- The subcooperad, input set by input set. -/
abbrev Sub (A : Type) [Fintype A] [DecidableEq A] : Type v := K.sub A

/-- The inclusion. -/
abbrev incl (A : Type) [Fintype A] [DecidableEq A] : K.Sub A →ₗ[R] C A := (K.sub A).subtype

lemma incl_injective (A : Type) [Fintype A] [DecidableEq A] : Function.Injective (K.incl A) :=
  (K.sub A).subtype_injective

lemma map_incl_injective : Function.Injective (TensorProduct.map (K.incl A) (K.incl B)) :=
  map_subtype_injective _ _

/-- **A subcooperad is a graded linear species.** -/
instance instGrSpecies : GrSpecies R K.Sub where
  map e := (SymSpecies.map (R := R) e).restrict fun _ hx => K.map_mem e hx
  map_refl x := Subtype.ext (SymSpecies.map_refl (R := R) x.1)
  map_trans e f x := Subtype.ext (SymSpecies.map_trans (R := R) e f x.1)
  par b := (GrSpecies.par (R := R) b).restrict fun _ hx => K.par_mem b hx
  par_add x := Subtype.ext (GrSpecies.par_add (R := R) x.1)
  par_par b b' x := Subtype.ext (by
    show GrSpecies.par (R := R) b (GrSpecies.par (R := R) b' x.1) = _
    rw [GrSpecies.par_par]
    split_ifs <;> rfl)
  map_par e b x := Subtype.ext (GrSpecies.map_par (R := R) e b x.1)

lemma incl_map (e : A ≃ B) (x : K.Sub A) :
    K.incl B (SymSpecies.map (R := R) e x) = SymSpecies.map (R := R) e (K.incl A x) := rfl

lemma incl_par (b : Bool) (x : K.Sub A) :
    K.incl A (GrSpecies.par (R := R) b x) = GrSpecies.par (R := R) b (K.incl A x) := rfl

lemma incl_comp_par (b : Bool) :
    K.incl A ∘ₗ GrSpecies.par (R := R) (V := K.Sub) b
      = GrSpecies.par (R := R) (V := C) b ∘ₗ K.incl A := rfl

/-- The decompositions, restricted to the subcooperad. -/
noncomputable def decompS (i : A) : K.Sub (Without A i ⊕ B) →ₗ[R] K.Sub A ⊗[R] K.Sub B :=
  (LinearEquiv.ofInjective _ K.map_incl_injective).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict _ (GrCooperad.decomp (R := R) i ∘ₗ K.incl _)
      (fun x => K.decomp_mem i x.2)

@[simp] lemma map_incl_decompS (i : A) (x : K.Sub (Without A i ⊕ B)) :
    TensorProduct.map (K.incl A) (K.incl B) (K.decompS i x)
      = GrCooperad.decomp (R := R) i (K.incl _ x) := by
  simp only [decompS, LinearEquiv.coe_coe, LinearEquiv.ofInjective_symm_apply,
    LinearMap.codRestrict_apply, LinearMap.comp_apply]

/-- The counit, restricted to the subcooperad. -/
def counitS : K.Sub Unit →ₗ[R] R := GrCooperad.counit (R := R) (C := C) ∘ₗ K.incl Unit

lemma map3_injective_right :
    Function.Injective (TensorProduct.map (K.incl A)
      (TensorProduct.map (K.incl B) (K.incl D))) :=
  TensorProduct.map_injective_of_flat_flat _ _ (K.incl_injective A) K.map_incl_injective

lemma map3_injective_left :
    Function.Injective (TensorProduct.map (TensorProduct.map (K.incl A) (K.incl B))
      (K.incl D)) :=
  TensorProduct.map_injective_of_flat_flat _ _ K.map_incl_injective (K.incl_injective D)

lemma lTensor_decompS (j : B) (t : K.Sub A ⊗[R] K.Sub (Without B j ⊕ D)) :
    TensorProduct.map (K.incl A) (TensorProduct.map (K.incl B) (K.incl D))
        (LinearMap.lTensor (K.Sub A) (K.decompS j) t)
      = LinearMap.lTensor (C A) (GrCooperad.decomp (R := R) j)
          (TensorProduct.map (K.incl A) (K.incl _) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a w => simp
  | add t t' ht ht' => simp only [map_add, ht, ht']

lemma rTensor_decompS (i : A) (t : K.Sub (Without A i ⊕ B) ⊗[R] K.Sub D) :
    TensorProduct.map (TensorProduct.map (K.incl A) (K.incl B)) (K.incl D)
        (LinearMap.rTensor (K.Sub D) (K.decompS i) t)
      = LinearMap.rTensor (C D) (GrCooperad.decomp (R := R) i)
          (TensorProduct.map (K.incl _) (K.incl D) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul w a => simp
  | add t t' ht ht' => simp only [map_add, ht, ht']

/-- **Decompositions preserve parities**, on the subcooperad. -/
lemma decompS_par (i : A) (b : Bool) :
    K.decompS (B := B) i ∘ₗ GrSpecies.par (R := R) (V := K.Sub) b
      = tpar R (fun c => GrSpecies.par (R := R) (V := K.Sub) c)
          (fun c => GrSpecies.par (R := R) (V := K.Sub) c) b ∘ₗ K.decompS i := by
  refine LinearMap.ext fun x => K.map_incl_injective ?_
  have h := LinearMap.congr_fun (GrCooperad.decomp_par (R := R) (C := C) (B := B) i b) (K.incl _ x)
  have hn := LinearMap.congr_fun (map_tpar (pX := fun c => GrSpecies.par (R := R) (V := K.Sub) c)
    (pX' := fun c => GrSpecies.par (R := R) (V := C) c)
    (pY := fun c => GrSpecies.par (R := R) (V := K.Sub) c)
    (pY' := fun c => GrSpecies.par (R := R) (V := C) c) (K.incl A) (K.incl B)
    (fun c => K.incl_comp_par c) (fun c => K.incl_comp_par c) b) (K.decompS i x)
  simp only [LinearMap.comp_apply] at h hn ⊢
  rw [map_incl_decompS, incl_par, h, hn, map_incl_decompS]

/-- **Decompositions are equivariant**, on the subcooperad. -/
lemma decompS_map (σ' : A ≃ A') (τ : B ≃ B') (i : A) :
    K.decompS (σ' i) ∘ₗ SymSpecies.map (R := R) (V := K.Sub) (compEquiv σ' τ i)
      = TensorProduct.map (SymSpecies.map (R := R) (V := K.Sub) σ')
          (SymSpecies.map (R := R) (V := K.Sub) τ) ∘ₗ K.decompS i := by
  refine LinearMap.ext fun x => K.map_incl_injective ?_
  have h := LinearMap.congr_fun (GrCooperad.decomp_map (R := R) (C := C) σ' τ i) (K.incl _ x)
  simp only [LinearMap.comp_apply] at h ⊢
  rw [map_incl_decompS, incl_map, h, ← map_incl_decompS]
  induction K.decompS (B := B) i x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [TensorProduct.map_tmul]
    rfl
  | add t t' ht ht' => simp only [map_add, ht, ht']

/-- The right counit law, on the subcooperad. -/
lemma decompS_counit_right (i : A) :
    (TensorProduct.rid R (K.Sub A)).toLinearMap ∘ₗ LinearMap.lTensor (K.Sub A) K.counitS ∘ₗ
        K.decompS i ∘ₗ SymSpecies.map (R := R) (V := K.Sub) (rightUnitEquiv i).symm
      = LinearMap.id := by
  refine LinearMap.ext fun x => K.incl_injective A ?_
  have h := LinearMap.congr_fun (GrCooperad.counit_right (R := R) (C := C) i) (K.incl A x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at h ⊢
  conv_rhs => rw [← h]
  rw [← incl_map, ← map_incl_decompS]
  induction K.decompS (B := Unit) i (SymSpecies.map (R := R) (rightUnitEquiv i).symm x)
    using TensorProduct.induction_on with
  | zero => simp
  | tmul a u => simp [counitS]
  | add t t' ht ht' => simp only [map_add, ht, ht']

/-- The left counit law, on the subcooperad. -/
lemma decompS_counit_left :
    (TensorProduct.lid R (K.Sub B)).toLinearMap ∘ₗ LinearMap.rTensor (K.Sub B) K.counitS ∘ₗ
        K.decompS () ∘ₗ SymSpecies.map (R := R) (V := K.Sub) (leftUnitEquiv B).symm
      = LinearMap.id := by
  refine LinearMap.ext fun x => K.incl_injective B ?_
  have h := LinearMap.congr_fun (GrCooperad.counit_left (R := R) (C := C) (B := B)) (K.incl B x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at h ⊢
  conv_rhs => rw [← h]
  rw [← incl_map, ← map_incl_decompS]
  induction K.decompS (B := B) () (SymSpecies.map (R := R) (leftUnitEquiv B).symm x)
    using TensorProduct.induction_on with
  | zero => simp
  | tmul u b => simp [counitS]
  | add t t' ht ht' => simp only [map_add, ht, ht']

/-- **Sequential coassociativity**, on the subcooperad. -/
lemma decompS_assoc_seq (i : A) (j : B) :
    LinearMap.lTensor (K.Sub A) (K.decompS (B := D) j) ∘ₗ K.decompS i
      = (TensorProduct.assoc R (K.Sub A) (K.Sub B) (K.Sub D)).toLinearMap ∘ₗ
          LinearMap.rTensor (K.Sub D) (K.decompS i) ∘ₗ K.decompS (Sum.inr j) ∘ₗ
            SymSpecies.map (R := R) (V := K.Sub) (seqEquiv i j D).symm := by
  refine LinearMap.ext fun x => K.map3_injective_right ?_
  have h := LinearMap.congr_fun (GrCooperad.decomp_assoc_seq (R := R) (C := C) (D := D) i j)
    (K.incl _ x)
  have ha := LinearMap.congr_fun (TensorProduct.map_map_comp_assoc_eq (R := R) (K.incl A)
    (K.incl B) (K.incl D))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h ha ⊢
  rw [lTensor_decompS, map_incl_decompS, h, ha, rTensor_decompS, map_incl_decompS, incl_map]

/-- **Parallel coassociativity**, on the subcooperad. -/
lemma decompS_assoc_par {i k : A} (hik : i ≠ k) :
    LinearMap.rTensor (K.Sub B) (K.decompS (B := D) k) ∘ₗ K.decompS (Sum.inl ⟨i, hik⟩)
      = sswapLast R (fun c => GrSpecies.par (R := R) (V := K.Sub) c)
          (fun c => GrSpecies.par (R := R) (V := K.Sub) c) ∘ₗ
          LinearMap.rTensor (K.Sub D) (K.decompS i) ∘ₗ
            K.decompS (Sum.inl ⟨k, Ne.symm hik⟩) ∘ₗ
              SymSpecies.map (R := R) (V := K.Sub) (parEquiv hik B D).symm := by
  refine LinearMap.ext fun x => K.map3_injective_left ?_
  have h := LinearMap.congr_fun (GrCooperad.decomp_assoc_par (R := R) (C := C) (B := B)
    (D := D) hik) (K.incl _ x)
  have hs := LinearMap.congr_fun (map_sswapLast
    (pY := fun c => GrSpecies.par (R := R) (V := K.Sub) c)
    (pY' := fun c => GrSpecies.par (R := R) (V := C) c)
    (pZ := fun c => GrSpecies.par (R := R) (V := K.Sub) c)
    (pZ' := fun c => GrSpecies.par (R := R) (V := C) c) (K.incl A) (K.incl B) (K.incl D)
    (fun c => K.incl_comp_par c) (fun c => K.incl_comp_par c))
  simp only [LinearMap.comp_apply] at h hs ⊢
  rw [rTensor_decompS, map_incl_decompS, h, hs, rTensor_decompS, map_incl_decompS, incl_map]

/-- The counit is even, on the subcooperad. -/
lemma counitS_par : K.counitS ∘ₗ GrSpecies.par (R := R) (V := K.Sub) true = 0 :=
  LinearMap.ext fun x => LinearMap.congr_fun (GrCooperad.counit_par (R := R) (C := C)) (K.incl _ x)

/-- **A subcooperad is a graded cooperad.** -/
noncomputable instance instGrCooperad : GrCooperad R K.Sub where
  toGrSpecies := K.instGrSpecies
  counit := K.counitS
  counit_par := K.counitS_par
  decomp i := K.decompS i
  decomp_par i b := K.decompS_par i b
  decomp_map σ' τ i := K.decompS_map σ' τ i
  counit_right i := K.decompS_counit_right i
  counit_left := K.decompS_counit_left
  decomp_assoc_seq i j := K.decompS_assoc_seq i j
  decomp_assoc_par hik := K.decompS_assoc_par hik

/-- **The inclusion of a subcooperad is a morphism of graded cooperads.** -/
noncomputable def inclHom : GrCooperadHom R K.Sub C where
  app A _ _ := K.incl A
  app_map _ _ := rfl
  app_par _ _ := rfl
  counit_app := rfl
  decomp_app i := LinearMap.ext fun x => (K.map_incl_decompS i x).symm

/-! ### Coaugmentations -/

variable [GrCooperad.Coaug R C]

lemma one_mem (h : unitSub R C ≤ K) : GrCooperad.Coaug.one (R := R) (C := C) ∈ K.sub Unit := by
  have := h Unit (GrCooperad.map_one_mem (R := R) (C := C) (Equiv.refl Unit))
  rwa [SymSpecies.map_refl] at this

/-- **A subcooperad containing the coaugmentation is coaugmented.** -/
@[reducible] noncomputable def coaug (h : unitSub R C ≤ K) : GrCooperad.Coaug R K.Sub where
  one := ⟨GrCooperad.Coaug.one (R := R) (C := C), K.one_mem h⟩
  par_one := Subtype.ext (GrCooperad.Coaug.par_one (R := R) (C := C))
  counit_one := GrCooperad.Coaug.counit_one (R := R) (C := C)
  decomp_mem {A B} _ _ _ _ i e := by
    have hU : ∀ (A : Type) [Fintype A] [DecidableEq A],
        (GrCooperad.unitSpanOf R K.Sub ⟨GrCooperad.Coaug.one (R := R) (C := C), K.one_mem h⟩
          A).map (K.incl A)
          = GrCooperad.unitSpanOf R C (GrCooperad.Coaug.one (R := R) (C := C)) A := by
      intro A _ _
      rw [GrCooperad.unitSpanOf, GrCooperad.unitSpanOf, Submodule.map_span]
      congr 1
      ext y
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨_, ⟨e, rfl⟩, rfl⟩
        exact ⟨e, rfl⟩
      · rintro ⟨e, rfl⟩
        exact ⟨_, ⟨e, rfl⟩, rfl⟩
    have hmem := GrCooperad.Coaug.decomp_mem (R := R) (C := C) (A := A) (B := B) i e
    rw [map₂_eq_range, ← hU A, ← hU B] at hmem
    rw [map₂_eq_range]
    obtain ⟨z, hz⟩ := hmem
    obtain ⟨z', rfl⟩ := TensorProduct.map_surjective
      (LinearMap.submoduleMap_surjective (K.incl A) _)
      (LinearMap.submoduleMap_surjective (K.incl B) _) z
    refine ⟨z', K.map_incl_injective ?_⟩
    show _ = TensorProduct.map (K.incl A) (K.incl B) (K.decompS i _)
    rw [map_incl_decompS]
    refine Eq.trans ?_ hz
    rw [← LinearMap.comp_apply (TensorProduct.map (K.incl A) (K.incl B)),
      ← TensorProduct.map_comp, ← LinearMap.comp_apply (TensorProduct.map _ _),
      ← TensorProduct.map_comp]
    rfl

end GrSubCooperad

end Field

/-! ## Precomposing with morphisms of cooperads -/

namespace ConvOp

variable {R : Type u} [CommRing R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {C' : (A : Type) → [Fintype A] → [DecidableEq A] → Type x}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C' A)] [GrCooperad R C']
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {A : Type} [Fintype A] [DecidableEq A]

/-- Precomposing with a linear map `C' A → C A`. -/
def preL (ψ : C' A →ₗ[R] C A) : ConvOp R C P A →ₗ[R] ConvOp R C' P A where
  toFun f := of (toLin f ∘ₗ ψ)
  map_add' f g := by
    simp only [toLin_add, LinearMap.add_comp]
    rfl
  map_smul' a f := by
    simp only [toLin_smul, LinearMap.smul_comp]
    rfl

omit [GrCooperad R C] [GrCooperad R C'] [GrOperad R P] in
@[simp] lemma toLin_preL (ψ : C' A →ₗ[R] C A) (f : ConvOp R C P A) :
    toLin (preL ψ f) = toLin f ∘ₗ ψ := rfl

/-- **Precomposing with a morphism of graded cooperads is a morphism of convolution operads.** -/
noncomputable def preHom (ψ : GrCooperadHom R C' C) :
    GrOperadHom R (ConvOp R C P) (ConvOp R C' P) where
  app A _ _ := preL (ψ.app A)
  app_par b f := by
    ext x
    simp only [par_def, toLin_preL, LinearMap.comp_apply, parC_apply, ψ.app_par]
  app_map σ' f := by
    ext x
    simp only [map_def, toLin_preL, LinearMap.comp_apply, mapC_apply, ψ.app_map]
  app_one := by
    ext x
    simp only [one_def, toLin_preL, LinearMap.comp_apply, oneC_apply]
    rw [← LinearMap.comp_apply (GrCooperad.counit (R := R) (C := C)), ψ.counit_app]
  app_comp i f g := by
    ext x
    simp only [comp_def, toLin_preL, LinearMap.comp_apply, toLin_compC]
    rw [← LinearMap.comp_apply (GrCooperad.decomp (R := R) (C := C) i), ψ.decomp_app,
      LinearMap.comp_apply]
    induction GrCooperad.decomp (R := R) (C := C') i x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [kap, LinearMap.coe_sum, Finset.sum_apply, TensorProduct.map_tmul,
        LinearMap.comp_apply, map_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      congr 2
      · simp only [GrSpecies.tw_apply, map_add, map_smul, toLin_preL, LinearMap.comp_apply,
          ψ.app_par]
      · simp only [parC_apply, toLin_preL, LinearMap.comp_apply, ψ.app_par]
    | add a b ha hb => simp only [map_add, ha, hb]

@[simp] lemma preHom_app (ψ : GrCooperadHom R C' C) (f : ConvOp R C P A) :
    toLin ((preHom (P := P) ψ).app A f) = toLin f ∘ₗ ψ.app A := rfl

end ConvOp

end Operad
