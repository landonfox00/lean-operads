/-
# Non-symmetric operads in modules and non-symmetric set operads

* `NSOperadIso`, with `NSOperadIso.ofBijective`: a morphism with bijective components is an
  isomorphism.
* `UndNS R Q`, the underlying non-symmetric set operad of a non-symmetric operad in `R`-modules, and
  **the linearization adjunction** `linHomEquivNS : NSSetOperadHom S (UndNS R Q) ≃
  NSOperadHom R (LinNS R S) Q`.
* `NSSetOperadHom.lin`, `NSSetOperadIso.lin`: linearization of morphisms and isomorphisms.
* `SetOperad.toNSLinIso`: the underlying non-symmetric operad of the linearization of a symmetric
  set operad is the linearization of its underlying non-symmetric set operad.
-/
import Operad.NSSet

universe u v w w'

namespace Operad

/-! ## Isomorphisms -/

/-- **An isomorphism of non-symmetric operads.** -/
structure NSOperadIso (R : Type u) [CommRing R]
    (P : ℕ → Type v) [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]
    (Q : ℕ → Type w) [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)] [NSOperad R Q] where
  /-- The forward morphism. -/
  hom : NSOperadHom R P Q
  /-- The inverse morphism. -/
  inv : NSOperadHom R Q P
  hom_inv_id : inv.comp hom = NSOperadHom.id
  inv_hom_id : hom.comp inv = NSOperadHom.id

variable {R : Type u} [CommRing R]
  {P : ℕ → Type v} [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]
  {Q : ℕ → Type w} [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)] [NSOperad R Q]

namespace NSOperadIso

@[simp] lemma inv_hom_apply (e : NSOperadIso R P Q) (n : ℕ) (x : P n) :
    e.inv.app n (e.hom.app n x) = x :=
  LinearMap.congr_fun (congrArg (fun φ => NSOperadHom.app φ n) e.hom_inv_id) x

@[simp] lemma hom_inv_apply (e : NSOperadIso R P Q) (n : ℕ) (y : Q n) :
    e.hom.app n (e.inv.app n y) = y :=
  LinearMap.congr_fun (congrArg (fun φ => NSOperadHom.app φ n) e.inv_hom_id) y

/-- The inverse isomorphism. -/
def symm (e : NSOperadIso R P Q) : NSOperadIso R Q P :=
  ⟨e.inv, e.hom, e.inv_hom_id, e.hom_inv_id⟩

variable {S : ℕ → Type w'} [∀ n, AddCommGroup (S n)] [∀ n, Module R (S n)] [NSOperad R S]

/-- The composite of two isomorphisms. -/
def trans (e : NSOperadIso R P Q) (f : NSOperadIso R Q S) : NSOperadIso R P S where
  hom := f.hom.comp e.hom
  inv := e.inv.comp f.inv
  hom_inv_id := by
    ext n x
    simp
  inv_hom_id := by
    ext n x
    simp

/-- The components of an isomorphism are bijective. -/
lemma bijective (e : NSOperadIso R P Q) (n : ℕ) : Function.Bijective (e.hom.app n) :=
  ⟨fun x y h => by rw [← e.inv_hom_apply n x, h, e.inv_hom_apply],
    fun y => ⟨e.inv.app n y, e.hom_inv_apply n y⟩⟩

end NSOperadIso

namespace NSOperadHom

/-- **The inverse of a morphism with bijective components** is a morphism. -/
noncomputable def invOfBijective (φ : NSOperadHom R P Q) (h : ∀ n, Function.Bijective (φ.app n)) :
    NSOperadHom R Q P where
  app n := (LinearEquiv.ofBijective (φ.app n) (h n)).symm.toLinearMap
  app_one := by
    apply (h _).1
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_ofBijective_symm_apply, φ.app_one]
  app_comp a b n x y := by
    apply (h _).1
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_ofBijective_symm_apply, φ.app_comp]

lemma app_invOfBijective (φ : NSOperadHom R P Q) (h : ∀ n, Function.Bijective (φ.app n))
    (n : ℕ) (y : Q n) : φ.app n ((φ.invOfBijective h).app n y) = y :=
  LinearEquiv.apply_ofBijective_symm_apply (φ.app n) (h := h n) y

lemma invOfBijective_app (φ : NSOperadHom R P Q) (h : ∀ n, Function.Bijective (φ.app n))
    (n : ℕ) (x : P n) : (φ.invOfBijective h).app n (φ.app n x) = x :=
  (h n).1 (app_invOfBijective φ h n (φ.app n x))

end NSOperadHom

/-- **A morphism with bijective components is an isomorphism.** -/
noncomputable def NSOperadIso.ofBijective (φ : NSOperadHom R P Q)
    (h : ∀ n, Function.Bijective (φ.app n)) : NSOperadIso R P Q where
  hom := φ
  inv := φ.invOfBijective h
  hom_inv_id := by
    ext n x
    exact NSOperadHom.invOfBijective_app φ h n x
  inv_hom_id := by
    ext n y
    exact NSOperadHom.app_invOfBijective φ h n y

/-! ## The underlying non-symmetric set operad, and the adjunction -/

/-- **The underlying non-symmetric set operad** of a non-symmetric operad in `R`-modules: the same
components and operations, forgetting linearity. A type synonym, so that the ring is recorded. -/
@[nolint unusedArguments]
def UndNS (R : Type u) [CommRing R] (Q : ℕ → Type w) : ℕ → Type w := Q

section UndNS

variable (R Q)

/-- An element of `Q n`, seen in the underlying set operad. -/
def UndNS.of {n : ℕ} : Q n ≃ UndNS R Q n := Equiv.refl _

omit [NSOperad R Q] in
variable {R Q} in
@[simp] lemma UndNS.symm_reindexS {m n : ℕ} (h : m = n) (x : UndNS R Q m) :
    (UndNS.of R Q).symm (reindexS (UndNS R Q) h x) = reindex R Q h ((UndNS.of R Q).symm x) := by
  subst h
  rfl

instance instNSSetOperadUndNS : NSSetOperad (UndNS R Q) where
  one := UndNS.of R Q (NSOperad.one (R := R) (P := Q))
  comp a b _ x y := UndNS.of R Q
    (NSOperad.comp (R := R) a b ((UndNS.of R Q).symm x) ((UndNS.of R Q).symm y))
  comp_one_right a b x := NSOperad.comp_one_right (R := R) (P := Q) a b x
  comp_one_left x := (UndNS.of R Q).symm.injective (by
    simp only [UndNS.symm_reindexS, Equiv.symm_apply_apply]
    exact NSOperad.comp_one_left (R := R) (P := Q) x)
  comp_assoc_seq a b c d _ x y z := (UndNS.of R Q).symm.injective (by
    simp only [UndNS.symm_reindexS, Equiv.symm_apply_apply]
    exact NSOperad.comp_assoc_seq (R := R) (P := Q) a b c d x y z)
  comp_assoc_par a b c _ _ x y z := (UndNS.of R Q).symm.injective (by
    simp only [UndNS.symm_reindexS, Equiv.symm_apply_apply]
    exact NSOperad.comp_assoc_par (R := R) (P := Q) a b c x y z)

variable {R Q}

lemma UndNS.one_eq : (NSSetOperad.one : UndNS R Q 1) = UndNS.of R Q (NSOperad.one (R := R)) :=
  rfl

lemma UndNS.comp_eq (a b : ℕ) {n : ℕ} (x : Q (a + 1 + b)) (y : Q n) :
    NSSetOperad.comp a b (UndNS.of R Q x) (UndNS.of R Q y)
      = UndNS.of R Q (NSOperad.comp (R := R) a b x y) := rfl

end UndNS

/-- **The underlying morphism of set operads** of a morphism of operads in modules. -/
def NSOperadHom.und (φ : NSOperadHom R P Q) : NSSetOperadHom (UndNS R P) (UndNS R Q) where
  app n x := UndNS.of R Q (φ.app n ((UndNS.of R P).symm x))
  app_one := congrArg (UndNS.of R Q) φ.app_one
  app_comp a b _ _ _ := congrArg (UndNS.of R Q) (φ.app_comp a b _ _)

section Adjunction

variable (R) {S : ℕ → Type v} [NSSetOperad S]

/-- Extend a morphism of set operads into the underlying set operad of `Q` linearly. -/
noncomputable def NSSetOperadHom.linExtend (φ : NSSetOperadHom S (UndNS R Q)) :
    NSOperadHom R (LinNS R S) Q where
  app n := Finsupp.lift (Q n) R (S n) (fun s => (UndNS.of R Q).symm (φ.app n s))
  app_one := by
    show Finsupp.lift (Q 1) R (S 1) _ (Finsupp.single NSSetOperad.one 1) = _
    simp only [Finsupp.lift_apply, Finsupp.sum_single_index, zero_smul, one_smul]
    rw [φ.app_one]
    rfl
  app_comp a b n x y := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | single s r =>
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, hy, hy']
      | single t r' =>
        show Finsupp.lift (Q _) R (S _) _
            (LinNS.compL R a b (Finsupp.single s r) (Finsupp.single t r')) = _
        rw [LinNS.compL_single]
        simp only [Finsupp.lift_apply, Finsupp.sum_single_index, zero_smul, map_smul,
          LinearMap.smul_apply, mul_smul]
        rw [φ.app_comp a b s t, smul_comm]
        rfl

/-- Restrict a morphism out of the linearization to the basis. -/
noncomputable def NSOperadHom.restrictBasis (Φ : NSOperadHom R (LinNS R S) Q) :
    NSSetOperadHom S (UndNS R Q) where
  app n s := UndNS.of R Q (Φ.app n (Finsupp.single s 1))
  app_one := congrArg (UndNS.of R Q) Φ.app_one
  app_comp a b n s t := by
    show UndNS.of R Q (Φ.app _ (Finsupp.single (NSSetOperad.comp a b s t) 1))
      = UndNS.of R Q (NSOperad.comp (R := R) a b (Φ.app _ (Finsupp.single s 1))
          (Φ.app _ (Finsupp.single t 1)))
    rw [← Φ.app_comp]
    refine congrArg _ (congrArg _ ?_)
    rw [show (Finsupp.single (NSSetOperad.comp a b s t) (1 : R))
        = Finsupp.single (NSSetOperad.comp a b s t) (1 * 1) by rw [mul_one]]
    exact (LinNS.compL_single (R := R) a b s t 1 1).symm

/-- **The linearization adjunction**: a morphism of linear operads out of `LinNS R S` is the same
as a morphism of set operads out of `S` into the underlying set operad. -/
noncomputable def linHomEquivNS : NSSetOperadHom S (UndNS R Q) ≃ NSOperadHom R (LinNS R S) Q where
  toFun φ := NSSetOperadHom.linExtend R φ
  invFun Φ := NSOperadHom.restrictBasis R Φ
  left_inv φ := by
    ext n s
    show UndNS.of R Q (Finsupp.lift (Q n) R (S n) _ (Finsupp.single s 1)) = φ.app n s
    simp
  right_inv Φ := by
    refine NSOperadHom.ext fun n => Finsupp.lhom_ext fun s r => ?_
    show Finsupp.lift (Q n) R (S n) _ (Finsupp.single s r) = Φ.app n (Finsupp.single s r)
    rw [Finsupp.lift_apply, Finsupp.sum_single_index (by simp)]
    show r • Φ.app n (Finsupp.single s 1) = _
    rw [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]

variable {R}

@[simp] lemma linExtend_single (φ : NSSetOperadHom S (UndNS R Q)) {n : ℕ} (s : S n) :
    (NSSetOperadHom.linExtend R φ).app n (Finsupp.single s 1) =
      (UndNS.of R Q).symm (φ.app n s) := by
  show Finsupp.lift (Q n) R (S n) _ (Finsupp.single s 1) = _
  simp

/-- Morphisms out of a linearization agree when they agree on the basis. -/
lemma NSOperadHom.ext_single {Φ Ψ : NSOperadHom R (LinNS R S) Q}
    (h : ∀ n (s : S n), Φ.app n (Finsupp.single s 1) = Ψ.app n (Finsupp.single s 1)) : Φ = Ψ :=
  NSOperadHom.ext fun n => Finsupp.lhom_ext' fun s => LinearMap.ext_ring (h n s)

end Adjunction

/-! ## Linearization of morphisms -/

section Lin

variable (R) {S : ℕ → Type v} [NSSetOperad S] {T : ℕ → Type w} [NSSetOperad T]

/-- **Linearization of a morphism of non-symmetric set operads.** -/
noncomputable def NSSetOperadHom.lin (φ : NSSetOperadHom S T) :
    NSOperadHom R (LinNS R S) (LinNS R T) where
  app n := Finsupp.lmapDomain R R (φ.app n)
  app_one := by
    show Finsupp.mapDomain _ (Finsupp.single _ 1) = _
    rw [Finsupp.mapDomain_single, φ.app_one]
    rfl
  app_comp a b n x y := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | single s r =>
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, hy, hy']
      | single t r' =>
        show Finsupp.mapDomain _ (LinNS.compL R a b (Finsupp.single s r) (Finsupp.single t r'))
          = LinNS.compL R a b (Finsupp.mapDomain _ (Finsupp.single s r))
            (Finsupp.mapDomain _ (Finsupp.single t r'))
        rw [LinNS.compL_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single,
          Finsupp.mapDomain_single, LinNS.compL_single, φ.app_comp]

variable {R}

@[simp] lemma NSSetOperadHom.lin_single (φ : NSSetOperadHom S T) {n : ℕ} (s : S n) (r : R) :
    (φ.lin R).app n (Finsupp.single s r) = Finsupp.single (φ.app n s) r :=
  Finsupp.mapDomain_single

variable (R) in
/-- **Linearization of an isomorphism of non-symmetric set operads.** -/
noncomputable def NSSetOperadIso.lin (e : NSSetOperadIso S T) :
    NSOperadIso R (LinNS R S) (LinNS R T) where
  hom := e.hom.lin R
  inv := e.inv.lin R
  hom_inv_id := NSOperadHom.ext_single fun n s => by
    show (e.inv.lin R).app n ((e.hom.lin R).app n (Finsupp.single s 1)) = Finsupp.single s 1
    rw [NSSetOperadHom.lin_single, NSSetOperadHom.lin_single]
    exact congrArg (Finsupp.single · 1)
      (congrArg (fun φ => NSSetOperadHom.app φ n s) e.hom_inv_id)
  inv_hom_id := NSOperadHom.ext_single fun n s => by
    show (e.hom.lin R).app n ((e.inv.lin R).app n (Finsupp.single s 1)) = Finsupp.single s 1
    rw [NSSetOperadHom.lin_single, NSSetOperadHom.lin_single]
    exact congrArg (Finsupp.single · 1)
      (congrArg (fun φ => NSSetOperadHom.app φ n s) e.inv_hom_id)

end Lin

/-! ## The underlying non-symmetric operad of a linearization -/

namespace SetOperad

open Sym

variable (R) {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]

lemma single_nsComp (a b : ℕ) {n : ℕ} (x : toNSSet S (a + 1 + b)) (y : toNSSet S n) (r r' : R) :
    NSOperad.comp (R := R) (P := SymOperad.toNS (Lin R S)) a b
        (Finsupp.single (α := S (Fin _)) x r) (Finsupp.single (α := S (Fin n)) y r')
      = Finsupp.single (α := S (Fin (a + n + b))) (nsCompSet a b x y) (r * r') := by
  rw [SymOperad.toNS_comp]
  show Lin.mapL R _ (Lin.compL R _ _ _) = _
  rw [Lin.compL_single, Lin.mapL_single]
  rfl

/-- **The underlying non-symmetric operad of `Lin R S` is `LinNS R (toNSSet S)`**, by the identity
in every arity. -/
noncomputable def toNSLinHom : NSOperadHom R (SymOperad.toNS (Lin R S)) (LinNS R (toNSSet S)) where
  app _ := LinearMap.id
  app_one := by
    show Lin.mapL R _ (Finsupp.single _ 1) = _
    rw [Lin.mapL_single]
    rfl
  app_comp a b n x y := by
    have key : LinNS.compL (S := toNSSet S) R a b (n := n)
        = NSOperad.comp (R := R) (P := SymOperad.toNS (Lin R S)) a b :=
      Finsupp.lhom_ext' fun s => LinearMap.ext_ring (Finsupp.lhom_ext' fun t =>
        LinearMap.ext_ring (by
          show LinNS.compL R a b (Finsupp.single s 1) (Finsupp.single t 1)
            = NSOperad.comp (R := R) (P := SymOperad.toNS (Lin R S)) a b
              (Finsupp.single (α := toNSSet S _) s 1) (Finsupp.single (α := toNSSet S n) t 1)
          rw [LinNS.compL_single]
          exact (single_nsComp R a b s t 1 1).symm))
    exact (LinearMap.congr_fun (LinearMap.congr_fun key x) y).symm

/-- The comparison is an isomorphism. -/
noncomputable def toNSLinIso : NSOperadIso R (SymOperad.toNS (Lin R S)) (LinNS R (toNSSet S)) :=
  NSOperadIso.ofBijective (toNSLinHom R) fun _ => Function.bijective_id

end SetOperad

end Operad
