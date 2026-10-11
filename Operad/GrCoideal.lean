/-
# Coideals and quotients of graded cooperads

* **Morphisms of graded cooperads** (`GrCooperadHom`): morphisms of graded linear species
  commuting with the counits and the decompositions.
* **A coideal of a graded cooperad** (`GrCoideal`): submodules stable under the parity projections
  and the relabellings, killed by the counit, whose decompositions lie in `J ⊗ C + C ⊗ J`. By the
  right exactness of the tensor product, `J ⊗ C + C ⊗ J` is the kernel of the tensor square of
  the projection, so the decompositions descend: **the quotient by a coideal is a graded
  cooperad** (`GrCoideal.instGrCooperad`), and the projection is a morphism of graded cooperads
  (`GrCoideal.projHom`). A coaugmentation descends to the quotient (`GrCoideal.instCoaug`).
-/
import Operad.GrCooperad

universe u v w x

namespace Operad

open Sym GerBV
open scoped TensorProduct

/-! ## Naturality of the parity projections of tensor products and of the super swap -/

section Natural

variable {R : Type u} [CommRing R] {X X' Y Y' Z Z' : Type v} [AddCommGroup X] [Module R X]
  [AddCommGroup X'] [Module R X'] [AddCommGroup Y] [Module R Y] [AddCommGroup Y'] [Module R Y']
  [AddCommGroup Z] [Module R Z] [AddCommGroup Z'] [Module R Z']

/-- **The parity projections of tensor products are natural.** -/
lemma map_tpar {pX : Bool → X →ₗ[R] X} {pX' : Bool → X' →ₗ[R] X'} {pY : Bool → Y →ₗ[R] Y}
    {pY' : Bool → Y' →ₗ[R] Y'} (f : X →ₗ[R] X') (g : Y →ₗ[R] Y')
    (hf : ∀ c, f ∘ₗ pX c = pX' c ∘ₗ f) (hg : ∀ c, g ∘ₗ pY c = pY' c ∘ₗ g) (b : Bool) :
    TensorProduct.map f g ∘ₗ tpar R pX pY b = tpar R pX' pY' b ∘ₗ TensorProduct.map f g :=
  TensorProduct.ext' fun x y => by
    simp only [LinearMap.comp_apply, tpar_tmul, map_add, TensorProduct.map_tmul,
      ← LinearMap.comp_apply f, ← LinearMap.comp_apply g, hf, hg]

/-- **The super swap is natural.** -/
lemma map_sswapLast {pY : Bool → Y →ₗ[R] Y} {pY' : Bool → Y' →ₗ[R] Y'}
    {pZ : Bool → Z →ₗ[R] Z} {pZ' : Bool → Z' →ₗ[R] Z'} (f : X →ₗ[R] X') (g : Y →ₗ[R] Y')
    (h : Z →ₗ[R] Z') (hg : ∀ c, g ∘ₗ pY c = pY' c ∘ₗ g) (hh : ∀ c, h ∘ₗ pZ c = pZ' c ∘ₗ h) :
    TensorProduct.map (TensorProduct.map f h) g ∘ₗ sswapLast R (X := X) pY pZ
      = sswapLast R (X := X') pY' pZ' ∘ₗ TensorProduct.map (TensorProduct.map f g) h :=
  TensorProduct.ext_threefold fun x y z => by
    simp only [LinearMap.comp_apply, sswapLast_tmul, map_sum, map_smul, TensorProduct.map_tmul,
      ← LinearMap.comp_apply g, ← LinearMap.comp_apply h, hg, hh]

end Natural

/-! ## Morphisms of graded cooperads -/

/-- **A morphism of graded cooperads**: a morphism of graded linear species commuting with the
counits and the decompositions. -/
structure GrCooperadHom (R : Type u) [CommRing R]
    (C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    (D : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (D A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (D A)]
    [GrCooperad R C] [GrCooperad R D] extends GrSpeciesHom R C D where
  counit_app : GrCooperad.counit (R := R) (C := D) ∘ₗ app Unit
    = GrCooperad.counit (R := R) (C := C)
  decomp_app {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A) :
    GrCooperad.decomp (R := R) (C := D) (B := B) i ∘ₗ app (Without A i ⊕ B)
      = TensorProduct.map (app A) (app B) ∘ₗ GrCooperad.decomp (R := R) (C := C) i

/-! ## Coideals -/

variable {R : Type u} [CommRing R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]

variable (R C) in
/-- **A coideal of a graded cooperad**: submodules stable under the parity projections and the
relabellings, killed by the counit, whose decompositions lie in `J ⊗ C + C ⊗ J`. -/
structure GrCoideal where
  /-- The component at a finite input set. -/
  sub (A : Type) [Fintype A] [DecidableEq A] : Submodule R (C A)
  par_mem {A : Type} [Fintype A] [DecidableEq A] (b : Bool) {x : C A} :
    x ∈ sub A → GrSpecies.par (R := R) b x ∈ sub A
  map_mem {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    {x : C A} : x ∈ sub A → SymSpecies.map (R := R) e x ∈ sub B
  counit_mem {x : C Unit} : x ∈ sub Unit → GrCooperad.counit (R := R) x = 0
  decomp_mem {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    {x : C (Without A i ⊕ B)} : x ∈ sub (Without A i ⊕ B) →
      GrCooperad.decomp (R := R) i x ∈ LinearMap.range (LinearMap.lTensor (C A) (sub B).subtype)
        ⊔ LinearMap.range (LinearMap.rTensor (C B) (sub A).subtype)

namespace GrCoideal

variable (J : GrCoideal R C)
variable {A A' B B' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] [Fintype D] [DecidableEq D]

/-- **The quotient by a coideal**, input set by input set. -/
def Quot (A : Type) [Fintype A] [DecidableEq A] : Type v := C A ⧸ J.sub A

instance (A : Type) [Fintype A] [DecidableEq A] : AddCommGroup (J.Quot A) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

instance (A : Type) [Fintype A] [DecidableEq A] : Module R (J.Quot A) :=
  inferInstanceAs (Module R (_ ⧸ _))

/-- The projection. -/
def proj (A : Type) [Fintype A] [DecidableEq A] : C A →ₗ[R] J.Quot A := (J.sub A).mkQ

lemma proj_surjective (A : Type) [Fintype A] [DecidableEq A] : Function.Surjective (J.proj A) :=
  Submodule.mkQ_surjective _

lemma proj_eq_zero_iff (x : C A) : J.proj A x = 0 ↔ x ∈ J.sub A :=
  Submodule.Quotient.mk_eq_zero _

/-- Maps out of the quotient agree when they agree on the projections. -/
lemma hom_ext {M : Type w} [AddCommGroup M] [Module R M] {f g : J.Quot A →ₗ[R] M}
    (h : f ∘ₗ J.proj A = g ∘ₗ J.proj A) : f = g :=
  Submodule.linearMap_qext _ h

/-- **The quotient is a graded linear species.** -/
instance instGrSpecies : GrSpecies R J.Quot where
  map e := Submodule.mapQ _ _ (SymSpecies.map (R := R) e) fun _ hx => J.map_mem e hx
  map_refl X := by
    obtain ⟨x, rfl⟩ := J.proj_surjective _ X
    exact congrArg (J.proj _) (SymSpecies.map_refl (R := R) x)
  map_trans e f X := by
    obtain ⟨x, rfl⟩ := J.proj_surjective _ X
    exact congrArg (J.proj _) (SymSpecies.map_trans (R := R) e f x)
  par b := Submodule.mapQ _ _ (GrSpecies.par (R := R) b) fun _ hx => J.par_mem b hx
  par_add X := by
    obtain ⟨x, rfl⟩ := J.proj_surjective _ X
    exact (map_add (J.proj _) _ _).symm.trans
      (congrArg (J.proj _) (GrSpecies.par_add (R := R) x))
  par_par b b' X := by
    obtain ⟨x, rfl⟩ := J.proj_surjective _ X
    show J.proj _ (GrSpecies.par (R := R) b (GrSpecies.par (R := R) b' x)) = _
    rw [GrSpecies.par_par]
    split_ifs
    · rfl
    · exact map_zero _
  map_par e b X := by
    obtain ⟨x, rfl⟩ := J.proj_surjective _ X
    exact congrArg (J.proj _) (GrSpecies.map_par (R := R) e b x)

@[simp] lemma map_proj (e : A ≃ B) (x : C A) :
    SymSpecies.map (R := R) e (J.proj A x) = J.proj B (SymSpecies.map (R := R) e x) := rfl

@[simp] lemma par_proj (b : Bool) (x : C A) :
    GrSpecies.par (R := R) b (J.proj A x) = J.proj A (GrSpecies.par (R := R) b x) := rfl

lemma map_comp_proj (e : A ≃ B) :
    SymSpecies.map (R := R) (V := J.Quot) e ∘ₗ J.proj A
      = J.proj B ∘ₗ SymSpecies.map (R := R) e := rfl

lemma par_comp_proj (b : Bool) :
    GrSpecies.par (R := R) (V := J.Quot) b ∘ₗ J.proj A = J.proj A ∘ₗ GrSpecies.par (R := R) b :=
  rfl

/-- The tensor square of the projection kills `J ⊗ C + C ⊗ J`. -/
lemma map_proj_eq_zero (i : A) {x : C (Without A i ⊕ B)} (hx : x ∈ J.sub (Without A i ⊕ B)) :
    TensorProduct.map (J.proj A) (J.proj B) (GrCooperad.decomp (R := R) i x) = 0 := by
  have h1 : LinearMap.range (LinearMap.lTensor (C A) (J.sub B).subtype)
      ≤ LinearMap.ker (TensorProduct.map (J.proj A) (J.proj B)) := by
    rw [LinearMap.range_le_ker_iff]
    refine TensorProduct.ext' fun a b => ?_
    simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, TensorProduct.map_tmul,
      Submodule.subtype_apply, LinearMap.zero_apply]
    rw [(J.proj_eq_zero_iff _).2 b.2, TensorProduct.tmul_zero]
  have h2 : LinearMap.range (LinearMap.rTensor (C B) (J.sub A).subtype)
      ≤ LinearMap.ker (TensorProduct.map (J.proj A) (J.proj B)) := by
    rw [LinearMap.range_le_ker_iff]
    refine TensorProduct.ext' fun a b => ?_
    simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, TensorProduct.map_tmul,
      Submodule.subtype_apply, LinearMap.zero_apply]
    rw [(J.proj_eq_zero_iff _).2 a.2, TensorProduct.zero_tmul]
  exact LinearMap.mem_ker.1 (sup_le h1 h2 (J.decomp_mem i hx))

/-- The decomposition, descended to the quotient. -/
noncomputable def decompQ (i : A) : J.Quot (Without A i ⊕ B) →ₗ[R] J.Quot A ⊗[R] J.Quot B :=
  (J.sub _).liftQ (TensorProduct.map (J.proj A) (J.proj B) ∘ₗ GrCooperad.decomp (R := R) i)
    fun _ hx => LinearMap.mem_ker.2 (J.map_proj_eq_zero i hx)

lemma decompQ_comp_proj (i : A) :
    J.decompQ (B := B) i ∘ₗ J.proj _
      = TensorProduct.map (J.proj A) (J.proj B) ∘ₗ GrCooperad.decomp (R := R) i := rfl

/-- The counit, descended to the quotient. -/
noncomputable def counitQ : J.Quot Unit →ₗ[R] R :=
  (J.sub Unit).liftQ (GrCooperad.counit (R := R)) fun _ hx => LinearMap.mem_ker.2 (J.counit_mem hx)

lemma counitQ_comp_proj : J.counitQ ∘ₗ J.proj Unit = GrCooperad.counit (R := R) (C := C) := rfl

@[simp] lemma decompQ_proj (i : A) (x : C (Without A i ⊕ B)) :
    J.decompQ i (J.proj _ x)
      = TensorProduct.map (J.proj A) (J.proj B) (GrCooperad.decomp (R := R) i x) := rfl

@[simp] lemma counitQ_proj (x : C Unit) :
    J.counitQ (J.proj Unit x) = GrCooperad.counit (R := R) x := rfl

/-! ### Naturality of the descended decompositions -/

lemma lTensor_decompQ_map {M : Type v} [AddCommGroup M] [Module R M] (f : M →ₗ[R] J.Quot A)
    (j : B) (t : M ⊗[R] C (Without B j ⊕ D)) :
    LinearMap.lTensor (J.Quot A) (J.decompQ j) (TensorProduct.map f (J.proj _) t)
      = TensorProduct.map f (TensorProduct.map (J.proj B) (J.proj D))
          (LinearMap.lTensor M (GrCooperad.decomp (R := R) j) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a w => simp
  | add t t' ht ht' => simp only [map_add, ht, ht']

lemma rTensor_decompQ_map {M : Type v} [AddCommGroup M] [Module R M] (f : M →ₗ[R] J.Quot D)
    (i : A) (t : C (Without A i ⊕ B) ⊗[R] M) :
    LinearMap.rTensor (J.Quot D) (J.decompQ i) (TensorProduct.map (J.proj _) f t)
      = TensorProduct.map (TensorProduct.map (J.proj A) (J.proj B)) f
          (LinearMap.rTensor M (GrCooperad.decomp (R := R) i) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul w a => simp
  | add t t' ht ht' => simp only [map_add, ht, ht']

/-- **Decompositions preserve parities**, on the quotient. -/
lemma decompQ_par (i : A) (b : Bool) :
    J.decompQ (B := B) i ∘ₗ GrSpecies.par (R := R) (V := J.Quot) b
      = tpar R (fun c => GrSpecies.par (R := R) (V := J.Quot) c)
          (fun c => GrSpecies.par (R := R) (V := J.Quot) c) b ∘ₗ J.decompQ i := by
  refine J.hom_ext (LinearMap.ext fun x => ?_)
  have h := LinearMap.congr_fun (GrCooperad.decomp_par (R := R) (C := C) (B := B) i b) x
  have hn := LinearMap.congr_fun (map_tpar (pX := fun c => GrSpecies.par (R := R) (V := C) c)
    (pX' := fun c => GrSpecies.par (R := R) (V := J.Quot) c)
    (pY := fun c => GrSpecies.par (R := R) (V := C) c)
    (pY' := fun c => GrSpecies.par (R := R) (V := J.Quot) c) (J.proj A) (J.proj B)
    (fun c => (J.par_comp_proj c).symm) (fun c => (J.par_comp_proj c).symm) b)
    (GrCooperad.decomp (R := R) i x)
  simp only [LinearMap.comp_apply] at h hn ⊢
  rw [par_proj, decompQ_proj, decompQ_proj, h, hn]

/-- **Decompositions are equivariant**, on the quotient. -/
lemma decompQ_map (σ' : A ≃ A') (τ : B ≃ B') (i : A) :
    J.decompQ (σ' i) ∘ₗ SymSpecies.map (R := R) (V := J.Quot) (compEquiv σ' τ i)
      = TensorProduct.map (SymSpecies.map (R := R) (V := J.Quot) σ')
          (SymSpecies.map (R := R) (V := J.Quot) τ) ∘ₗ J.decompQ i := by
  refine J.hom_ext (LinearMap.ext fun x => ?_)
  have h := LinearMap.congr_fun (GrCooperad.decomp_map (R := R) (C := C) σ' τ i) x
  simp only [LinearMap.comp_apply] at h ⊢
  rw [map_proj, decompQ_proj, decompQ_proj, h]
  induction GrCooperad.decomp (R := R) (C := C) (B := B) i x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add t t' ht ht' => simp only [map_add, ht, ht']

/-- The right counit law, on the quotient. -/
lemma decompQ_counit_right (i : A) :
    (TensorProduct.rid R (J.Quot A)).toLinearMap ∘ₗ LinearMap.lTensor (J.Quot A) J.counitQ ∘ₗ
        J.decompQ i ∘ₗ SymSpecies.map (R := R) (V := J.Quot) (rightUnitEquiv i).symm
      = LinearMap.id := by
  refine J.hom_ext (LinearMap.ext fun x => ?_)
  have h := LinearMap.congr_fun (GrCooperad.counit_right (R := R) (C := C) i) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at h ⊢
  rw [map_proj, decompQ_proj]
  conv_rhs => rw [← h]
  induction GrCooperad.decomp (R := R) (C := C) (B := Unit) i
    (SymSpecies.map (R := R) (rightUnitEquiv i).symm x) using TensorProduct.induction_on with
  | zero => simp
  | tmul a u => simp
  | add t t' ht ht' => simp only [map_add, ht, ht']

/-- The left counit law, on the quotient. -/
lemma decompQ_counit_left :
    (TensorProduct.lid R (J.Quot B)).toLinearMap ∘ₗ LinearMap.rTensor (J.Quot B) J.counitQ ∘ₗ
        J.decompQ () ∘ₗ SymSpecies.map (R := R) (V := J.Quot) (leftUnitEquiv B).symm
      = LinearMap.id := by
  refine J.hom_ext (LinearMap.ext fun x => ?_)
  have h := LinearMap.congr_fun (GrCooperad.counit_left (R := R) (C := C) (B := B)) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at h ⊢
  rw [map_proj, decompQ_proj]
  conv_rhs => rw [← h]
  induction GrCooperad.decomp (R := R) (C := C) (B := B) ()
    (SymSpecies.map (R := R) (leftUnitEquiv B).symm x) using TensorProduct.induction_on with
  | zero => simp
  | tmul u b => simp
  | add t t' ht ht' => simp only [map_add, ht, ht']

/-- **Sequential coassociativity**, on the quotient. -/
lemma decompQ_assoc_seq (i : A) (j : B) :
    LinearMap.lTensor (J.Quot A) (J.decompQ (B := D) j) ∘ₗ J.decompQ i
      = (TensorProduct.assoc R (J.Quot A) (J.Quot B) (J.Quot D)).toLinearMap ∘ₗ
          LinearMap.rTensor (J.Quot D) (J.decompQ i) ∘ₗ J.decompQ (Sum.inr j) ∘ₗ
            SymSpecies.map (R := R) (V := J.Quot) (seqEquiv i j D).symm := by
  refine J.hom_ext (LinearMap.ext fun x => ?_)
  have h := LinearMap.congr_fun (GrCooperad.decomp_assoc_seq (R := R) (C := C) (D := D) i j) x
  have ha := LinearMap.congr_fun (TensorProduct.map_map_comp_assoc_eq (R := R) (J.proj A)
    (J.proj B) (J.proj D))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h ha ⊢
  rw [decompQ_proj, lTensor_decompQ_map, h, map_proj, decompQ_proj, rTensor_decompQ_map, ha]

/-- **Parallel coassociativity**, on the quotient. -/
lemma decompQ_assoc_par {i k : A} (hik : i ≠ k) :
    LinearMap.rTensor (J.Quot B) (J.decompQ (B := D) k) ∘ₗ J.decompQ (Sum.inl ⟨i, hik⟩)
      = sswapLast R (fun c => GrSpecies.par (R := R) (V := J.Quot) c)
          (fun c => GrSpecies.par (R := R) (V := J.Quot) c) ∘ₗ
          LinearMap.rTensor (J.Quot D) (J.decompQ i) ∘ₗ
            J.decompQ (Sum.inl ⟨k, Ne.symm hik⟩) ∘ₗ
              SymSpecies.map (R := R) (V := J.Quot) (parEquiv hik B D).symm := by
  refine J.hom_ext (LinearMap.ext fun x => ?_)
  have h := LinearMap.congr_fun (GrCooperad.decomp_assoc_par (R := R) (C := C) (B := B)
    (D := D) hik) x
  have hs := LinearMap.congr_fun (map_sswapLast (pY := fun c => GrSpecies.par (R := R) (V := C) c)
    (pY' := fun c => GrSpecies.par (R := R) (V := J.Quot) c)
    (pZ := fun c => GrSpecies.par (R := R) (V := C) c)
    (pZ' := fun c => GrSpecies.par (R := R) (V := J.Quot) c) (J.proj A) (J.proj B) (J.proj D)
    (fun c => (J.par_comp_proj c).symm) (fun c => (J.par_comp_proj c).symm))
  simp only [LinearMap.comp_apply] at h hs ⊢
  rw [decompQ_proj, rTensor_decompQ_map, h, hs, map_proj, decompQ_proj, rTensor_decompQ_map]

/-- The counit is even, on the quotient. -/
lemma counitQ_par : J.counitQ ∘ₗ GrSpecies.par (R := R) (V := J.Quot) true = 0 := by
  refine J.hom_ext (LinearMap.ext fun x => ?_)
  have h := LinearMap.congr_fun (GrCooperad.counit_par (R := R) (C := C)) x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h ⊢
  rw [par_proj, counitQ_proj, h]

/-- **The quotient of a graded cooperad by a coideal is a graded cooperad.** -/
noncomputable instance instGrCooperad : GrCooperad R J.Quot where
  toGrSpecies := J.instGrSpecies
  counit := J.counitQ
  counit_par := J.counitQ_par
  decomp i := J.decompQ i
  decomp_par i b := J.decompQ_par i b
  decomp_map σ' τ i := J.decompQ_map σ' τ i
  counit_right i := J.decompQ_counit_right i
  counit_left := J.decompQ_counit_left
  decomp_assoc_seq i j := J.decompQ_assoc_seq i j
  decomp_assoc_par hik := J.decompQ_assoc_par hik

/-- **The projection onto the quotient is a morphism of graded cooperads.** -/
noncomputable def projHom : GrCooperadHom R C J.Quot where
  app A _ _ := J.proj A
  app_map _ _ := rfl
  app_par _ _ := rfl
  counit_app := rfl
  decomp_app _ := rfl

/-! ### The coaugmentation -/

variable [GrCooperad.Coaug R C]

lemma proj_unitSpan_le :
    (GrCooperad.unitSpan R C A).map (J.proj A)
      ≤ GrCooperad.unitSpanOf R J.Quot (J.proj Unit (GrCooperad.Coaug.one (R := R))) A := by
  rw [GrCooperad.unitSpan, GrCooperad.unitSpanOf, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨e, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨e, rfl⟩

/-- **A coaugmentation descends to the quotient.** -/
noncomputable instance instCoaug : GrCooperad.Coaug R J.Quot where
  one := J.proj Unit (GrCooperad.Coaug.one (R := R))
  par_one := by
    rw [par_proj, GrCooperad.Coaug.par_one]
  counit_one := by
    show J.counitQ (J.proj Unit _) = 1
    rw [counitQ_proj, GrCooperad.Coaug.counit_one]
  decomp_mem {A B} _ _ _ _ i e := by
    show J.decompQ i (SymSpecies.map (R := R) e (J.proj Unit _)) ∈ _
    rw [map_proj, decompQ_proj]
    have hmem := GrCooperad.Coaug.decomp_mem (R := R) (C := C) (A := A) (B := B) i e
    have hle : Submodule.map₂ (TensorProduct.mk R (C A) (C B)) (GrCooperad.unitSpan R C A)
        (GrCooperad.unitSpan R C B)
        ≤ (Submodule.map₂ (TensorProduct.mk R (J.Quot A) (J.Quot B))
            (GrCooperad.unitSpanOf R J.Quot (J.proj Unit (GrCooperad.Coaug.one (R := R))) A)
            (GrCooperad.unitSpanOf R J.Quot (J.proj Unit (GrCooperad.Coaug.one (R := R))) B)).comap
          (TensorProduct.map (J.proj A) (J.proj B)) := by
      refine Submodule.map₂_le.2 fun a ha b hb => ?_
      rw [Submodule.mem_comap, TensorProduct.mk_apply, TensorProduct.map_tmul]
      exact Submodule.apply_mem_map₂ _ (J.proj_unitSpan_le ⟨a, ha, rfl⟩)
        (J.proj_unitSpan_le ⟨b, hb, rfl⟩)
    exact hle hmem

end GrCoideal

end Operad
