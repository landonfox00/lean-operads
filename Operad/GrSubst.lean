/-
# Signed-basis morphisms of twisted linearizations

A morphism of graded operads between twisted linearizations may send every basis element to a
basis element up to sign, `Φ (bas x) = σ(c x) bas (ψ x)`. This is the case of the morphisms out
of a free graded operad sending each generator to a signed basis element
(`FreeGr.signedBasis`): such values form a set operad, **the signed basis elements**
(`SgnBas`), triples `(b, y, d)` standing for `σ(b) y` with sign data `d` of the parity of `y`,
composed with the signs of both `d` and the sign data of `y` — their discrepancies in parallel
compositions cancel, the parities being equal. The underlying map `ψ` is then a morphism of set
operads, and the signs satisfy the cocycle relation of a composite (`SgnBasMor`).

* A morphism of set operads is **bijective on factorizations** (`SetOperadHom.FactBij`) when every
  factorization of the image of an operation is the image of exactly one factorization of the
  operation. Isomorphisms are (`SetOperadIso.factBij`), relabelling the vertices of trees is
  (`FreeReg.relabel_factBij`), and composites of such are (`SetOperadHom.FactBij.comp`).
* **A signed-basis morphism along a morphism bijective on factorizations is a morphism of the
  graded decomposition cooperads** (`SgnBasMor.decomp_app`): the signs of the factorizations are
  matched by the cocycle relation.
-/
import Operad.TreeRelabel
import Operad.GrDecCooperad

universe u v w

namespace Operad

open Sym GerBV
open scoped TensorProduct

/-! ## Morphisms bijective on factorizations -/

section FactBij

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {S' : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S']
  {S'' : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S'']

/-- **A morphism of set operads bijective on factorizations**: every factorization of the image
of an operation is the image of exactly one factorization of the operation. -/
def SetOperadHom.FactBij (φ : SetOperadHom S S') : Prop :=
  ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (x : S (Without A i ⊕ B)) (p' : S' A) (q' : S' B), SetOperad.comp i p' q' = φ.app _ x →
      ∃! pq : S A × S B, SetOperad.comp i pq.1 pq.2 = x ∧ φ.app A pq.1 = p' ∧ φ.app B pq.2 = q'

/-- **Composites of morphisms bijective on factorizations are bijective on factorizations.** -/
theorem SetOperadHom.FactBij.comp {φ : SetOperadHom S S'} {ψ : SetOperadHom S' S''}
    (hφ : φ.FactBij) (hψ : ψ.FactBij) : (ψ.comp φ).FactBij := by
  intro A B _ _ _ _ i x p'' q'' h
  obtain ⟨⟨p', q'⟩, ⟨h1, h2, h3⟩, hu'⟩ := hψ i (φ.app _ x) p'' q'' h
  obtain ⟨⟨p, q⟩, ⟨g1, g2, g3⟩, hu⟩ := hφ i x p' q' h1
  refine ⟨(p, q), ⟨g1, ?_, ?_⟩, ?_⟩
  · show ψ.app A (φ.app A p) = p''
    rw [g2, h2]
  · show ψ.app B (φ.app B q) = q''
    rw [g3, h3]
  · rintro ⟨r, s⟩ ⟨k1, k2, k3⟩
    have e' := hu' (φ.app A r, φ.app B s) ⟨by rw [← φ.app_comp, k1], k2, k3⟩
    simp only [Prod.mk.injEq] at e'
    exact hu (r, s) ⟨k1, e'.1, e'.2⟩

/-- **Isomorphisms are bijective on factorizations.** -/
theorem SetOperadIso.factBij (φ : SetOperadIso S S') : φ.hom.FactBij := by
  intro A B _ _ _ _ i x p' q' h
  have hinv : ∀ (A : Type) [Fintype A] [DecidableEq A] (z : S' A),
      φ.hom.app A (φ.inv.app A z) = z := fun A _ _ z =>
    congrArg (fun ψ : SetOperadHom S' S' => ψ.app A z) φ.inv_hom_id
  have hinv' : ∀ (A : Type) [Fintype A] [DecidableEq A] (z : S A),
      φ.inv.app A (φ.hom.app A z) = z := fun A _ _ z =>
    congrArg (fun ψ : SetOperadHom S S => ψ.app A z) φ.hom_inv_id
  refine ⟨(φ.inv.app A p', φ.inv.app B q'), ⟨?_, hinv A p', hinv B q'⟩, ?_⟩
  · rw [← φ.inv.app_comp, h, hinv']
  · rintro ⟨r, s⟩ ⟨_, k2, k3⟩
    simp only [Prod.mk.injEq]
    exact ⟨by rw [← k2, hinv'], by rw [← k3, hinv']⟩

end FactBij

/-- **Relabelling the vertices of trees is bijective on factorizations.** -/
theorem FreeReg.relabel_factBij {T T' : ℕ → Type v} (f : ∀ k, T k → T' k) :
    (FreeReg.relabel f).FactBij := by
  intro A B _ _ _ _ i x p' q' h
  obtain ⟨p, q, h1, h2, h3⟩ := FreeReg.relabel_fact f i x p' q' h
  refine ⟨(p, q), ⟨h1, h2, h3⟩, ?_⟩
  rintro ⟨r, s⟩ ⟨k1, k2, k3⟩
  obtain ⟨e1, e2⟩ := FreeReg.relabel_fact_unique f i (k1.trans h1.symm)
    (k2.trans h2.symm) (k3.trans h3.symm)
  exact Prod.ext e1 e2

/-! ## Signed-basis morphisms -/

section SgnBasMor

variable {R : Type u} [CommRing R]
  {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  [SetOperad.FiniteFact S] {δ : SetOperadHom S SgnD}
  {S' : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S']
  [SetOperad.FiniteFact S'] {δ' : SetOperadHom S' SgnD}

/-- **A signed-basis morphism**: a morphism of graded operads between twisted linearizations
sending each basis element to a basis element up to sign, `Φ (bas x) = σ(c x) bas (ψ x)`, along a
morphism of set operads `ψ`, the signs satisfying the cocycle relation of composites. -/
structure SgnBasMor (Φ : GrOperadHom R (SgnLin R δ) (SgnLin R δ')) where
  /-- The underlying morphism of set operads. -/
  ψ : SetOperadHom S S'
  /-- The signs. -/
  c : ∀ (A : Type) [Fintype A] [DecidableEq A], S A → Bool
  app_bas (A : Type) [Fintype A] [DecidableEq A] (x : S A) :
    Φ.app A (SgnLin.bas δ R x) = σ R (c A x) • SgnLin.bas δ' R (ψ.app A x)
  c_comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A) (x : S A)
    (y : S B) : c _ (SetOperad.comp i x y) = xor (xor (c A x) (c B y))
      (xor (SgnData.sgn i (δ.app A x) (δ.app B y))
        (SgnData.sgn i (δ'.app A (ψ.app A x)) (δ'.app B (ψ.app B y))))

variable {Φ : GrOperadHom R (SgnLin R δ) (SgnLin R δ')}

/-- **A signed-basis morphism along a morphism bijective on factorizations is a morphism of the
graded decomposition cooperads.** -/
theorem SgnBasMor.decomp_app (M : SgnBasMor Φ) (hψ : M.ψ.FactBij) {A B : Type} [Fintype A]
    [DecidableEq A] [Fintype B] [DecidableEq B] (i : A) :
    SgnLin.decompT R δ' (B := B) i ∘ₗ Φ.app (Without A i ⊕ B)
      = TensorProduct.map (Φ.app A) (Φ.app B) ∘ₗ SgnLin.decompT R δ i := by
  let φX : (S (Without A i ⊕ B) →₀ R) →ₗ[R] (S' (Without A i ⊕ B) →₀ R) := Φ.app _
  let φA : (S A →₀ R) →ₗ[R] (S' A →₀ R) := Φ.app A
  let φB : (S B →₀ R) →ₗ[R] (S' B →₀ R) := Φ.app B
  have hX : ∀ x, φX (Finsupp.single x 1) = σ R (M.c _ x) • Finsupp.single (M.ψ.app _ x) 1 :=
    fun x => M.app_bas _ x
  have hA : ∀ x, φA (Finsupp.single x 1) = σ R (M.c A x) • Finsupp.single (M.ψ.app A x) 1 :=
    fun x => M.app_bas A x
  have hB : ∀ x, φB (Finsupp.single x 1) = σ R (M.c B x) • Finsupp.single (M.ψ.app B x) 1 :=
    fun x => M.app_bas B x
  show SgnLin.decompT R δ' i ∘ₗ φX = TensorProduct.map φA φB ∘ₗ SgnLin.decompT R δ i
  refine Finsupp.lhom_ext' fun t => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [hX, map_smul, SgnLin.decompT_single, SgnLin.decompT_single, map_sum, Finset.smul_sum]
  symm
  refine Finset.sum_bij (fun pq _ => (M.ψ.app A pq.1, M.ψ.app B pq.2)) ?_ ?_ ?_ ?_
  · intro pq hpq
    rw [SgnLin.mem_fact_iff] at hpq ⊢
    rw [← M.ψ.app_comp, hpq]
  · intro pq₁ h₁ pq₂ h₂ he
    rw [SgnLin.mem_fact_iff] at h₁ h₂
    simp only [Prod.mk.injEq] at he
    obtain ⟨_, _, hu⟩ := hψ i t (M.ψ.app A pq₁.1) (M.ψ.app B pq₁.2)
      (by rw [← M.ψ.app_comp, h₁])
    have e1 := hu pq₁ ⟨h₁, rfl, rfl⟩
    have e2 := hu pq₂ ⟨h₂, he.1.symm, he.2.symm⟩
    rw [e1, e2]
  · intro pq' hpq'
    rw [SgnLin.mem_fact_iff] at hpq'
    obtain ⟨pq, ⟨h1, h2, h3⟩, _⟩ := hψ i t pq'.1 pq'.2 hpq'
    exact ⟨pq, (SgnLin.mem_fact_iff i t pq).2 h1, Prod.ext h2 h3⟩
  · intro pq hpq
    rw [SgnLin.mem_fact_iff] at hpq
    have hc : M.c _ t = xor (xor (M.c A pq.1) (M.c B pq.2))
        (xor (SgnData.sgn i (δ.app A pq.1) (δ.app B pq.2))
          (SgnData.sgn i (δ'.app A (M.ψ.app A pq.1)) (δ'.app B (M.ψ.app B pq.2)))) := by
      rw [← hpq]
      exact M.c_comp i pq.1 pq.2
    dsimp only
    rw [map_smul, TensorProduct.map_tmul, hA, hB, TensorProduct.smul_tmul_smul, smul_smul,
      smul_smul, hc]
    congr 1
    simp only [σ_xor, mul_one]
    have h := σ_mul_self R (SgnData.sgn i (δ'.app A (M.ψ.app A pq.1))
      (δ'.app B (M.ψ.app B pq.2)))
    linear_combination (-(σ R (M.c A pq.1) * σ R (M.c B pq.2)
      * σ R (SgnData.sgn i (δ.app A pq.1) (δ.app B pq.2)))) * h

end SgnBasMor

/-! ## Signed basis elements -/

section SgnBas

variable {S' : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S']
  (δ' : SetOperadHom S' SgnD)

/-- **Signed basis elements**: triples `(b, y, d)` of a sign, an operation and sign data of its
parity, standing for `σ(b) y` with sign data `d`. -/
@[nolint unusedArguments]
def SgnBas (A : Type) [Fintype A] [DecidableEq A] : Type v :=
  {z : Bool × S' A × SgnData A // (δ'.app A z.2.1).tot = z.2.2.tot}

namespace SgnBas

variable {δ'}
variable {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype D]
  [DecidableEq D]

/-- The sign. -/
def sg (z : SgnBas δ' A) : Bool := z.1.1

/-- The operation. -/
def op (z : SgnBas δ' A) : S' A := z.1.2.1

/-- The sign data. -/
def dat (z : SgnBas δ' A) : SgnData A := z.1.2.2

lemma tot_eq (z : SgnBas δ' A) : (δ'.app A z.op).tot = z.dat.tot := z.2

@[ext] lemma ext {z z' : SgnBas δ' A} (h1 : z.sg = z'.sg) (h2 : z.op = z'.op)
    (h3 : z.dat = z'.dat) : z = z' :=
  Subtype.ext (Prod.ext h1 (Prod.ext h2 h3))

/-- A signed basis element. -/
def mk (b : Bool) (y : S' A) (d : SgnData A) (h : (δ'.app A y).tot = d.tot) : SgnBas δ' A :=
  ⟨(b, y, d), h⟩

@[simp] lemma mk_sg (b : Bool) (y : S' A) (d : SgnData A) (h : (δ'.app A y).tot = d.tot) :
    (mk b y d h).sg = b := rfl

@[simp] lemma mk_op (b : Bool) (y : S' A) (d : SgnData A) (h : (δ'.app A y).tot = d.tot) :
    (mk b y d h).op = y := rfl

@[simp] lemma mk_dat (b : Bool) (y : S' A) (d : SgnData A) (h : (δ'.app A y).tot = d.tot) :
    (mk b y d h).dat = d := rfl

/-- Relabelling. -/
def mapB (e : A ≃ B) (z : SgnBas δ' A) : SgnBas δ' B :=
  mk z.sg (SetOperad.map e z.op) (SgnData.map e z.dat) (by
    rw [δ'.app_map, SgnData.map_def, SgnData.map_tot, SgnData.map_tot, z.tot_eq])

/-- The unit. -/
def oneB : SgnBas δ' Unit :=
  mk false SetOperad.one SgnData.one (by rw [δ'.app_one]; rfl)

/-- **Composition**, with the signs of both the sign data and the sign data of the operations. -/
noncomputable def compB (i : A) (z : SgnBas δ' A) (z' : SgnBas δ' B) :
    SgnBas δ' (Without A i ⊕ B) :=
  mk (xor (xor z.sg z'.sg) (xor (SgnData.sgn i z.dat z'.dat)
      (SgnData.sgn i (δ'.app A z.op) (δ'.app B z'.op))))
    (SetOperad.comp i z.op z'.op) (SgnData.comp i z.dat z'.dat) (by
      rw [δ'.app_comp, SgnData.comp_def, SgnData.comp_tot, SgnData.comp_tot, z.tot_eq,
        z'.tot_eq])

lemma sgn_op_map {A' B' : Type} [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']
    (σ' : A ≃ A') (τ : B ≃ B') (i : A) (z : SgnBas δ' A) (z' : SgnBas δ' B) :
    SgnData.sgn (σ' i) (δ'.app A' (SetOperad.map σ' z.op)) (δ'.app B' (SetOperad.map τ z'.op))
      = SgnData.sgn i (δ'.app A z.op) (δ'.app B z'.op) := by
  rw [δ'.app_map, δ'.app_map, SgnData.map_def, SgnData.map_def, SgnData.sgn_map]

/-- **Signed basis elements form a set operad**: the discrepancies of the two signs in parallel
compositions cancel, the parities being equal. -/
noncomputable instance instSetOperad : SetOperad (SgnBas δ') where
  map e z := mapB e z
  map_refl z := SgnBas.ext rfl (SetOperad.map_refl z.op)
    (SetOperad.map_refl (S := SgnD) z.dat)
  map_trans e f z := SgnBas.ext rfl (SetOperad.map_trans e f z.op)
    (SetOperad.map_trans (S := SgnD) e f z.dat)
  one := oneB
  comp i z z' := compB i z z'
  map_comp σ' τ i z z' := by
    refine SgnBas.ext ?_ (SetOperad.map_comp σ' τ i z.op z'.op)
      (SetOperad.map_comp (S := SgnD) σ' τ i z.dat z'.dat)
    show xor (xor z.sg z'.sg) (xor (SgnData.sgn i z.dat z'.dat)
        (SgnData.sgn i (δ'.app _ z.op) (δ'.app _ z'.op)))
      = xor (xor z.sg z'.sg) (xor (SgnData.sgn (σ' i) (SgnData.map σ' z.dat)
        (SgnData.map τ z'.dat))
        (SgnData.sgn (σ' i) (δ'.app _ (SetOperad.map σ' z.op))
          (δ'.app _ (SetOperad.map τ z'.op))))
    rw [SgnData.sgn_map, sgn_op_map]
  comp_one i z := by
    refine SgnBas.ext ?_ (SetOperad.comp_one i z.op) (SetOperad.comp_one (S := SgnD) i z.dat)
    show xor (xor z.sg false) (xor (SgnData.sgn i z.dat SgnData.one)
        (SgnData.sgn i (δ'.app _ z.op) (δ'.app Unit SetOperad.one))) = z.sg
    rw [δ'.app_one, SgnData.one_def, SgnData.sgn_one_right, SgnData.sgn_one_right]
    simp
  one_comp z := by
    refine SgnBas.ext ?_ (SetOperad.one_comp z.op) (SetOperad.one_comp (S := SgnD) z.dat)
    show xor (xor false z.sg) (xor (SgnData.sgn () SgnData.one z.dat)
        (SgnData.sgn () (δ'.app Unit SetOperad.one) (δ'.app _ z.op))) = z.sg
    rw [δ'.app_one, SgnData.one_def, SgnData.sgn_one_left, SgnData.sgn_one_left]
    simp
  comp_assoc_seq {A B D} _ _ _ _ _ _ i j z z' z'' := by
    refine SgnBas.ext ?_ (SetOperad.comp_assoc_seq i j z.op z'.op z''.op)
      (SetOperad.comp_assoc_seq (S := SgnD) i j z.dat z'.dat z''.dat)
    show xor (xor (xor (xor z.sg z'.sg) (xor (SgnData.sgn i z.dat z'.dat)
          (SgnData.sgn i (δ'.app A z.op) (δ'.app B z'.op)))) z''.sg)
        (xor (SgnData.sgn (Sum.inr j) (SgnData.comp i z.dat z'.dat) z''.dat)
          (SgnData.sgn (Sum.inr j) (δ'.app _ (SetOperad.comp i z.op z'.op)) (δ'.app D z''.op)))
      = xor (xor z.sg (xor (xor z'.sg z''.sg) (xor (SgnData.sgn j z'.dat z''.dat)
          (SgnData.sgn j (δ'.app B z'.op) (δ'.app D z''.op)))))
        (xor (SgnData.sgn i z.dat (SgnData.comp j z'.dat z''.dat))
          (SgnData.sgn i (δ'.app A z.op) (δ'.app _ (SetOperad.comp j z'.op z''.op))))
    have h1 := SgnData.sgn_seq i j z.dat z'.dat z''.dat
    have h2 := SgnData.sgn_seq i j (δ'.app A z.op) (δ'.app B z'.op) (δ'.app D z''.op)
    rw [δ'.app_comp, δ'.app_comp, SgnData.comp_def, SgnData.comp_def]
    revert h1 h2
    cases z.sg <;> cases z'.sg <;> cases z''.sg <;>
      cases SgnData.sgn i z.dat z'.dat <;>
      cases SgnData.sgn i (δ'.app A z.op) (δ'.app B z'.op) <;>
      cases SgnData.sgn j z'.dat z''.dat <;>
      cases SgnData.sgn j (δ'.app B z'.op) (δ'.app D z''.op) <;> simp_all
  comp_assoc_par {A B D} _ _ _ _ _ _ i k hik z z' z'' := by
    refine SgnBas.ext ?_ (SetOperad.comp_assoc_par hik z.op z'.op z''.op)
      (SetOperad.comp_assoc_par (S := SgnD) hik z.dat z'.dat z''.dat)
    show xor (xor (xor (xor z.sg z'.sg) (xor (SgnData.sgn i z.dat z'.dat)
          (SgnData.sgn i (δ'.app A z.op) (δ'.app B z'.op)))) z''.sg)
        (xor (SgnData.sgn (Sum.inl ⟨k, Ne.symm hik⟩) (SgnData.comp i z.dat z'.dat) z''.dat)
          (SgnData.sgn (Sum.inl ⟨k, Ne.symm hik⟩) (δ'.app _ (SetOperad.comp i z.op z'.op))
            (δ'.app D z''.op)))
      = xor (xor (xor (xor z.sg z''.sg) (xor (SgnData.sgn k z.dat z''.dat)
          (SgnData.sgn k (δ'.app A z.op) (δ'.app D z''.op)))) z'.sg)
        (xor (SgnData.sgn (Sum.inl ⟨i, hik⟩) (SgnData.comp k z.dat z''.dat) z'.dat)
          (SgnData.sgn (Sum.inl ⟨i, hik⟩) (δ'.app _ (SetOperad.comp k z.op z''.op))
            (δ'.app B z'.op)))
    have h1 := SgnData.sgn_par hik z.dat z'.dat z''.dat
    have h2 := SgnData.sgn_par hik (δ'.app A z.op) (δ'.app B z'.op) (δ'.app D z''.op)
    rw [z'.tot_eq, z''.tot_eq] at h2
    rw [δ'.app_comp, δ'.app_comp, SgnData.comp_def, SgnData.comp_def]
    revert h1 h2
    cases z.sg <;> cases z'.sg <;> cases z''.sg <;> cases z'.dat.tot && z''.dat.tot <;>
      cases SgnData.sgn i z.dat z'.dat <;>
      cases SgnData.sgn i (δ'.app A z.op) (δ'.app B z'.op) <;>
      cases SgnData.sgn k z.dat z''.dat <;>
      cases SgnData.sgn k (δ'.app A z.op) (δ'.app D z''.op) <;> simp_all

@[simp] lemma map_sg (e : A ≃ B) (z : SgnBas δ' A) : (SetOperad.map e z).sg = z.sg := rfl

@[simp] lemma map_op (e : A ≃ B) (z : SgnBas δ' A) :
    (SetOperad.map e z).op = SetOperad.map e z.op := rfl

@[simp] lemma map_dat (e : A ≃ B) (z : SgnBas δ' A) :
    (SetOperad.map e z).dat = SgnData.map e z.dat := rfl

@[simp] lemma one_sg : (SetOperad.one : SgnBas δ' Unit).sg = false := rfl

@[simp] lemma one_op : (SetOperad.one : SgnBas δ' Unit).op = SetOperad.one := rfl

@[simp] lemma one_dat : (SetOperad.one : SgnBas δ' Unit).dat = SgnData.one := rfl

@[simp] lemma comp_sg (i : A) (z : SgnBas δ' A) (z' : SgnBas δ' B) :
    (SetOperad.comp i z z').sg = xor (xor z.sg z'.sg) (xor (SgnData.sgn i z.dat z'.dat)
      (SgnData.sgn i (δ'.app A z.op) (δ'.app B z'.op))) := rfl

@[simp] lemma comp_op (i : A) (z : SgnBas δ' A) (z' : SgnBas δ' B) :
    (SetOperad.comp i z z').op = SetOperad.comp i z.op z'.op := rfl

@[simp] lemma comp_dat (i : A) (z : SgnBas δ' A) (z' : SgnBas δ' B) :
    (SetOperad.comp i z z').dat = SgnData.comp i z.dat z'.dat := rfl

variable (δ') in
/-- The operations of signed basis elements. -/
def projOp : SetOperadHom (SgnBas δ') S' where
  app _ _ _ z := z.op
  app_map _ _ := rfl
  app_one := rfl
  app_comp _ _ _ := rfl

variable (δ') in
/-- The sign data of signed basis elements. -/
def projDat : SetOperadHom (SgnBas δ') SgnD where
  app _ _ _ z := z.dat
  app_map _ _ := rfl
  app_one := rfl
  app_comp _ _ _ := rfl

variable (R : Type u) [CommRing R] (δ') in
/-- **Signed basis elements as homogeneous operations with sign data**: `(b, y, d) ↦ σ(b) y`. -/
noncomputable def toSO : SetOperadHom (SgnBas δ') (SgnOp R (SgnLin R δ')) where
  app A _ _ z := SgnOp.mk (σ R z.sg • SgnLin.bas δ' R z.op) z.dat (by
    rw [map_smul, ← z.tot_eq, SgnLin.par_bas])
  app_map e z := SgnOp.ext (by
    show σ R z.sg • SgnLin.bas δ' R (SetOperad.map e z.op)
      = GrOperad.map (R := R) e (σ R z.sg • SgnLin.bas δ' R z.op)
    rw [map_smul, SgnLin.map_bas]) rfl
  app_one := SgnOp.ext (by
    show σ R false • SgnLin.bas δ' R SetOperad.one = GrOperad.one (R := R)
    rw [σ_false, one_smul]
    rfl) rfl
  app_comp i z z' := SgnOp.ext (by
    show σ R (SetOperad.comp i z z').sg • SgnLin.bas δ' R (SetOperad.comp i z.op z'.op)
      = σ R (SgnData.sgn i z.dat z'.dat) • GrOperad.comp (R := R) i
          (σ R z.sg • SgnLin.bas δ' R z.op) (σ R z'.sg • SgnLin.bas δ' R z'.op)
    rw [map_smul, map_smul, LinearMap.smul_apply, SgnLin.comp_bas, comp_sg, smul_smul,
      smul_smul, smul_smul]
    congr 1
    simp only [σ_xor]
    ring) rfl

end SgnBas

end SgnBas

/-! ## Signed-basis morphisms out of free graded operads -/

namespace FreeGr

open TreeOfArity

variable {R : Type u} [CommRing R] {T T' : ℕ → Type v} {gp : ∀ k, T k → Bool}
  {gp' : ∀ k, T' k → Bool}

variable (gp gp') in
/-- **Signed basis values on the generators**: for each generator, a sign and a tree of its
parity. -/
structure SBVal where
  /-- The signs. -/
  sg : ∀ k, T k → Bool
  /-- The trees. -/
  tree : ∀ k, T k → Reg (TreeOfArity T') (Fin k)
  tot_eq : ∀ k (e : T k), ((treeSgn gp').app _ (tree k e)).tot = gp k e

namespace SBVal

variable (v : SBVal gp gp')

/-- The morphism of set operads into signed basis elements defined by the values. -/
noncomputable def liftB : SetOperadHom (Reg (TreeOfArity T)) (SgnBas (treeSgn gp')) :=
  Reg.lift (TreeOfArity.lift (S := SetOperad.toNSSet (SgnBas (treeSgn gp'))) fun k e =>
    SgnBas.mk (v.sg k e) (v.tree k e) ((treeSgn gp).app _ (Reg.std (corolla e)))
      (by rw [v.tot_eq, treeSgn_tot]))

lemma liftB_std {k : ℕ} (e : T k) :
    v.liftB.app (Fin k) (Reg.std (corolla e))
      = SgnBas.mk (v.sg k e) (v.tree k e) ((treeSgn gp).app _ (Reg.std (corolla e)))
          (by rw [v.tot_eq, treeSgn_tot]) := by
  rw [liftB, Reg.lift_std]
  exact TreeOfArity.lift_corolla (S := SetOperad.toNSSet (SgnBas (treeSgn gp'))) _ e

lemma projDat_liftB : (SgnBas.projDat (treeSgn gp')).comp v.liftB = treeSgn gp :=
  FreeReg.regHom_ext fun k e => by
    show (v.liftB.app _ (Reg.std (corolla e))).dat = _
    rw [liftB_std]
    rfl

lemma dat_liftB {A : Type} [Fintype A] [DecidableEq A] (x : Reg (TreeOfArity T) A) :
    (v.liftB.app A x).dat = (treeSgn gp).app A x :=
  congrArg (fun φ : SetOperadHom _ SgnD => φ.app A x) v.projDat_liftB

lemma proj_toSO_liftB :
    (SgnOp.proj R (SgnLin R (treeSgn gp'))).comp ((SgnBas.toSO (treeSgn gp') R).comp v.liftB)
      = treeSgn gp :=
  SetOperadHom.ext fun _ _ _ x => v.dat_liftB x

variable (R) in
/-- **The morphism of free graded operads defined by signed basis values on the generators.** -/
noncomputable def hom : GrOperadHom R (FreeGr R gp) (FreeGr R gp') :=
  SgnLin.ofSO ((SgnBas.toSO (treeSgn gp') R).comp v.liftB) v.proj_toSO_liftB

lemma hom_bas {A : Type} [Fintype A] [DecidableEq A] (x : Reg (TreeOfArity T) A) :
    (v.hom R).app A (SgnLin.bas _ R x)
      = σ R (v.liftB.app A x).sg • SgnLin.bas (treeSgn gp') R (v.liftB.app A x).op :=
  (SgnLin.ofSOApp_single _ x 1).trans (one_smul R _)

lemma hom_gen {k : ℕ} (e : T k) :
    (v.hom R).app (Fin k) (gen e) = σ R (v.sg k e) • SgnLin.bas (treeSgn gp') R (v.tree k e) := by
  show (v.hom R).app (Fin k) (SgnLin.bas _ R (Reg.std (corolla e))) = _
  rw [hom_bas, liftB_std]
  rfl

/-- **A morphism of free graded operads with signed basis values on the generators is the
morphism they define.** -/
lemma eq_hom {Φ : GrOperadHom R (FreeGr R gp) (FreeGr R gp')}
    (h : ∀ k (e : T k), Φ.app (Fin k) (gen e)
      = σ R (v.sg k e) • SgnLin.bas (treeSgn gp') R (v.tree k e)) : Φ = v.hom R :=
  FreeGr.hom_ext fun k e => by rw [h, hom_gen]

variable (R) in
/-- **The morphism defined by signed basis values is a signed-basis morphism.** -/
noncomputable def sbm : SgnBasMor (v.hom R) where
  ψ := (SgnBas.projOp (treeSgn gp')).comp v.liftB
  c A _ _ x := (v.liftB.app A x).sg
  app_bas A _ _ x := v.hom_bas x
  c_comp i x y := by
    show (v.liftB.app _ (SetOperad.comp i x y)).sg = _
    rw [v.liftB.app_comp, SgnBas.comp_sg, v.dat_liftB, v.dat_liftB]
    rfl

lemma sbm_ψ_std {k : ℕ} (e : T k) :
    (v.sbm R).ψ.app (Fin k) (Reg.std (corolla e)) = v.tree k e := by
  show (v.liftB.app (Fin k) (Reg.std (corolla e))).op = v.tree k e
  rw [liftB_std]
  rfl

end SBVal

end FreeGr

end Operad
