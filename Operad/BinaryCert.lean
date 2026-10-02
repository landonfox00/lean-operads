/-
# Certificates for binary quadratic operads in arity three

Statements about the relations of arity three of a binary quadratic operad over a field — that an
element lies in the span of relabelled relators, that it is orthogonal to them for the Koszul
pairing, that a family is independent — are finite linear algebra in the `12 |G|²` monomials of
arity three (`Operad.FreeBin.basis3`). This file reduces them to computations with integer
combinations of monomials, which the kernel checks by `decide`:

* `Cert3 G`, a list of monomials of arity three with integer coefficients, and its value in
  `FreeBin K G (Fin 3)` (`Cert3.val`); relabelling (`Cert3.act`, `map_val`), its coordinates
  (`Cert3.coeff`, `repr_val`), and the Koszul pairing (`Cert3.pair`, `pair3_val`);
* `Cert2 G` in arity two (`Cert2.val`), and the composites of two of them at either input,
  relabelled as in `comp_e0_bin2` and `comp_e1_bin2` (`Cert2.comp0`, `Cert2.comp1`; `comp0_val`,
  `comp1_val`);
* **membership** (`val_mem_of_cert`): an integer combination of relabelled generators, checked
  coordinate by coordinate, lies in every submodule containing the relabelled generators; the
  composites of the relators of arity two with the monomials and the relators of arity three
  generate the relations of arity three (`gens23`, `gens23_mem`);
* **orthogonality** (`val_mem_dualRel23`): a certificate orthogonal to the relabellings of those
  generators lies in the Koszul dual relations;
* **dimension** (`le_finrank_of_cert`): certificates in a submodule, each with a coordinate where
  the others vanish, bound its dimension from below.
-/
import Operad.BinaryKoszulSym
import Mathlib.Data.List.GetD

universe u v

namespace Operad

open Sym SetOperad

namespace FreeBin

variable {G : Type v}

/-- **A certificate in arity three**: an integer combination of monomials of arity three. -/
abbrev Cert3 (G : Type v) := List (Mono3 G × ℤ)

/-- **A certificate in arity two**: an integer combination of monomials of arity two. -/
abbrev Cert2 (G : Type v) := List ((G × Equiv.Perm (Fin 2)) × ℤ)

namespace Cert3

/-- The relabelling of a certificate. -/
def act (τ : Equiv.Perm (Fin 3)) (l : Cert3 G) : Cert3 G := l.map fun p => (act3 τ p.1, p.2)

/-- An integer multiple of a certificate. -/
def smul (c : ℤ) (l : Cert3 G) : Cert3 G := l.map fun p => (p.1, c * p.2)

/-- The sign of a monomial in the Koszul pairing, as an integer. -/
def signZ (m : Mono3 G) : ℤ := (if m.1 then -1 else 1) * ((Equiv.Perm.sign m.2.2.2 : ℤˣ) : ℤ)

variable [DecidableEq G]

/-- The coefficient of a monomial in a certificate. -/
def coeff (l : Cert3 G) (m : Mono3 G) : ℤ := (l.map fun p => if p.1 = m then p.2 else 0).sum

/-- **The Koszul pairing of two certificates.** -/
def pair (l l' : Cert3 G) : ℤ :=
  (l.map fun p => p.2 * (l'.map fun q => if p.1 = q.1 then signZ p.1 * q.2 else 0).sum).sum

@[simp] lemma coeff_nil (m : Mono3 G) : coeff [] m = 0 := rfl

lemma coeff_cons (p : Mono3 G × ℤ) (l : Cert3 G) (m : Mono3 G) :
    coeff (p :: l) m = (if p.1 = m then p.2 else 0) + coeff l m := by
  simp [coeff]

lemma coeff_append (l l' : Cert3 G) (m : Mono3 G) : coeff (l ++ l') m = coeff l m + coeff l' m := by
  simp [coeff]

lemma coeff_smul (c : ℤ) (l : Cert3 G) (m : Mono3 G) : coeff (smul c l) m = c * coeff l m := by
  induction l with
  | nil => simp [smul]
  | cons p l ih =>
    simp only [smul, List.map_cons] at ih ⊢
    rw [coeff_cons, coeff_cons, ih, mul_add]
    split_ifs <;> simp

variable (K : Type u) [CommRing K]

/-- **The value of a certificate** in the free operad. -/
noncomputable def val (l : Cert3 G) : FreeBin K G (Fin 3) :=
  (l.map fun p => (p.2 : K) • mono3 K p.1).sum

omit [DecidableEq G] in
@[simp] lemma val_nil : val K ([] : Cert3 G) = 0 := by simp [val]

omit [DecidableEq G] in
@[simp] lemma val_cons (p : Mono3 G × ℤ) (l : Cert3 G) :
    val K (p :: l) = (p.2 : K) • mono3 K p.1 + val K l := by
  simp [val]

omit [DecidableEq G] in
lemma val_append (l l' : Cert3 G) : val K (l ++ l') = val K l + val K l' := by
  simp [val]

omit [DecidableEq G] in
lemma val_smul (c : ℤ) (l : Cert3 G) : val K (smul c l) = (c : K) • val K l := by
  induction l with
  | nil => simp [smul]
  | cons p l ih =>
    simp only [smul, List.map_cons] at ih ⊢
    rw [val_cons, val_cons, ih, smul_add, smul_smul]
    push_cast
    rfl

omit [DecidableEq G] in
/-- **Relabelling a certificate** relabels its value. -/
lemma map_val (τ : Equiv.Perm (Fin 3)) (l : Cert3 G) :
    SymOperad.map (R := K) τ (val K l) = val K (act τ l) := by
  induction l with
  | nil => simp [act]
  | cons p l ih =>
    simp only [act, List.map_cons] at ih ⊢
    rw [val_cons, val_cons, map_add, map_smul, map_mono3, ih]

variable [Fintype G]

/-- **The coordinates of a certificate** are its coefficients. -/
lemma repr_val (l : Cert3 G) (m : Mono3 G) : (basis3 K).repr (val K l) m = (coeff l m : K) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [val_cons, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, ← basis3_apply,
      Module.Basis.repr_self, ih, coeff_cons, Finsupp.single_apply]
    split_ifs <;> simp

/-- Certificates with the same coefficients have the same value. -/
lemma val_eq_of_coeff {l l' : Cert3 G} (h : ∀ m, coeff l m = coeff l' m) : val K l = val K l' :=
  (basis3 K).repr.injective (Finsupp.ext fun m => by rw [repr_val, repr_val, h])

omit [Fintype G] [DecidableEq G] in
lemma signZ_cast {K : Type u} [Field K] (m : Mono3 G) : ((signZ m : ℤ) : K) = sign3 K m := by
  simp only [signZ, sign3]
  split_ifs <;> push_cast <;> ring

omit [Fintype G] in
lemma pair_cons (p : Mono3 G × ℤ) (l l' : Cert3 G) :
    pair (p :: l) l'
      = p.2 * (l'.map fun q => if p.1 = q.1 then signZ p.1 * q.2 else 0).sum + pair l l' := by
  simp [pair]

variable {K} in
lemma pair3_mono3_val {K : Type u} [Field K] (m : Mono3 G) (l : Cert3 G) :
    pair3 G K (mono3 K m) (val K l)
      = (((l.map fun q => if m = q.1 then signZ m * q.2 else 0).sum : ℤ) : K) := by
  induction l with
  | nil => simp
  | cons q l ih =>
    rw [val_cons, map_add, map_smul, ih, pair3_mono3, List.map_cons, List.sum_cons]
    push_cast
    split_ifs with h <;> simp [h, signZ_cast, mul_comm]

/-- **The Koszul pairing of the values is the pairing of the certificates.** -/
lemma pair3_val {K : Type u} [Field K] (l l' : Cert3 G) :
    pair3 G K (val K l) (val K l') = (pair l l' : K) := by
  induction l with
  | nil => simp [pair]
  | cons p l ih =>
    rw [val_cons, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, ih,
      pair3_mono3_val, pair_cons]
    push_cast
    rw [smul_eq_mul]

omit [DecidableEq G] [Fintype G] in
lemma image_val_cons (a : Cert3 G) (l : List (Cert3 G)) :
    val K '' {r | r ∈ a :: l} = insert (val K a) (val K '' {r | r ∈ l}) := by
  rw [show {r | r ∈ a :: l} = insert a {r | r ∈ l} from Set.ext fun _ => List.mem_cons,
    Set.image_insert_eq]

omit [DecidableEq G] [Fintype G] in
lemma image_val_nil : val K '' {r | r ∈ ([] : List (Cert3 G))} = ∅ := by simp

end Cert3

namespace Cert2

variable (K : Type u) [CommRing K]

/-- **The value of a certificate of arity two** in the free operad. -/
noncomputable def val (l : Cert2 G) : FreeBin K G (Fin 2) :=
  (l.map fun p => (p.2 : K) • bin2 p.1.1 p.1.2).sum

@[simp] lemma val_nil : val K ([] : Cert2 G) = 0 := by simp [val]

@[simp] lemma val_cons (p : (G × Equiv.Perm (Fin 2)) × ℤ) (l : Cert2 G) :
    val K (p :: l) = (p.2 : K) • bin2 p.1.1 p.1.2 + val K l := by
  simp [val]

lemma image_val_singleton (a : Cert2 G) : val K '' {r | r ∈ [a]} = {val K a} := by
  ext x
  simp [eq_comm]

/-- The monomial composite of two monomials at the first input, relabelled by `e0`. -/
noncomputable def mono0 (a b : G × Equiv.Perm (Fin 2)) : Mono3 G :=
  if a.2 = 1 then (false, a.1, b.1, if b.2 = 1 then 1 else perm3 1 0 2)
  else (true, a.1, b.1, if b.2 = 1 then perm3 2 0 1 else perm3 2 1 0)

/-- The monomial composite of two monomials at the second input, relabelled by `e1`. -/
noncomputable def mono1 (a b : G × Equiv.Perm (Fin 2)) : Mono3 G :=
  if a.2 = 1 then (true, a.1, b.1, if b.2 = 1 then 1 else perm3 0 2 1)
  else (false, a.1, b.1, if b.2 = 1 then perm3 1 2 0 else perm3 2 1 0)

/-- **The composite at the first input**, relabelled by `e0`. -/
noncomputable def comp0 (a b : Cert2 G) : Cert3 G :=
  a.flatMap fun p => b.map fun q => (mono0 p.1 q.1, p.2 * q.2)

/-- **The composite at the second input**, relabelled by `e1`. -/
noncomputable def comp1 (a b : Cert2 G) : Cert3 G :=
  a.flatMap fun p => b.map fun q => (mono1 p.1 q.1, p.2 * q.2)

variable [Fintype G] [DecidableEq G]

lemma mono3_mono0 (a b : G × Equiv.Perm (Fin 2)) :
    SymOperad.map (R := K) e0 (SymOperad.comp (R := K) 0 (bin2 a.1 a.2) (bin2 b.1 b.2))
      = mono3 K (mono0 a b) := by
  rw [comp_e0_bin2, mono0]
  split_ifs <;> rfl

lemma mono3_mono1 (a b : G × Equiv.Perm (Fin 2)) :
    SymOperad.map (R := K) e1 (SymOperad.comp (R := K) 1 (bin2 a.1 a.2) (bin2 b.1 b.2))
      = mono3 K (mono1 a b) := by
  rw [comp_e1_bin2, mono1]
  split_ifs <;> rfl

lemma comp0_single (p : (G × Equiv.Perm (Fin 2)) × ℤ) (b : Cert2 G) :
    SymOperad.map (R := K) e0 (SymOperad.comp (R := K) 0 ((p.2 : K) • bin2 p.1.1 p.1.2) (val K b))
      = Cert3.val K (b.map fun q => (mono0 p.1 q.1, p.2 * q.2)) := by
  induction b with
  | nil => simp
  | cons q b ih =>
    rw [val_cons, map_add, map_add, ih, List.map_cons, Cert3.val_cons]
    congr 1
    simp only [map_smul, LinearMap.smul_apply, mono3_mono0, smul_smul, Int.cast_mul, mul_comm]

lemma comp1_single (p : (G × Equiv.Perm (Fin 2)) × ℤ) (b : Cert2 G) :
    SymOperad.map (R := K) e1 (SymOperad.comp (R := K) 1 ((p.2 : K) • bin2 p.1.1 p.1.2) (val K b))
      = Cert3.val K (b.map fun q => (mono1 p.1 q.1, p.2 * q.2)) := by
  induction b with
  | nil => simp
  | cons q b ih =>
    rw [val_cons, map_add, map_add, ih, List.map_cons, Cert3.val_cons]
    congr 1
    simp only [map_smul, LinearMap.smul_apply, mono3_mono1, smul_smul, Int.cast_mul, mul_comm]

/-- **The composite of two certificates at the first input**, relabelled by `e0`. -/
lemma comp0_val (a b : Cert2 G) :
    SymOperad.map (R := K) e0 (SymOperad.comp (R := K) 0 (val K a) (val K b))
      = Cert3.val K (comp0 a b) := by
  induction a with
  | nil => simp [comp0]
  | cons p a ih =>
    have h : comp0 (p :: a) b = (b.map fun q => (mono0 p.1 q.1, p.2 * q.2)) ++ comp0 a b := by
      simp [comp0]
    rw [h, Cert3.val_append, ← ih, ← comp0_single, ← map_add, ← LinearMap.add_apply, ← map_add,
      val_cons]

/-- **The composite of two certificates at the second input**, relabelled by `e1`. -/
lemma comp1_val (a b : Cert2 G) :
    SymOperad.map (R := K) e1 (SymOperad.comp (R := K) 1 (val K a) (val K b))
      = Cert3.val K (comp1 a b) := by
  induction a with
  | nil => simp [comp1]
  | cons p a ih =>
    have h : comp1 (p :: a) b = (b.map fun q => (mono1 p.1 q.1, p.2 * q.2)) ++ comp1 a b := by
      simp [comp1]
    rw [h, Cert3.val_append, ← ih, ← comp1_single, ← map_add, ← LinearMap.add_apply, ← map_add,
      val_cons]

end Cert2

open Cert3 Cert2

/-! ## Membership -/

section Membership

variable [DecidableEq G] (K : Type u) [Field K]

/-- **A membership certificate**: integer multiples of relabelled generators, the generators
given by their index in a list. -/
abbrev MemCert := List (ℤ × Equiv.Perm (Fin 3) × ℕ)

/-- The combination of the relabelled generators of a membership certificate. -/
def MemCert.sum (gens : List (Cert3 G)) (c : MemCert) : Cert3 G :=
  c.flatMap fun x => smul x.1 (act x.2.1 (gens.getD x.2.2 []))

omit [DecidableEq G] in
lemma val_memCertSum {W : Submodule K (FreeBin K G (Fin 3))} (gens : List (Cert3 G))
    (hgens : ∀ g ∈ gens, ∀ τ, val K (act τ g) ∈ W) (c : MemCert) :
    val K (MemCert.sum gens c) ∈ W := by
  induction c with
  | nil => simp [MemCert.sum]
  | cons x c ih =>
    rw [MemCert.sum, List.flatMap_cons, val_append, ← MemCert.sum, val_smul]
    refine add_mem (Submodule.smul_mem _ _ ?_) ih
    rcases lt_or_ge x.2.2 gens.length with h | h
    · rw [List.getD_eq_getElem _ _ h]
      exact hgens _ (List.getElem_mem h) _
    · rw [List.getD_eq_default _ _ h]
      simp [act]

variable [Fintype G]

/-- **Membership by certificate**: if `d v` is an integer combination of relabelled generators,
coordinate by coordinate, and `d ≠ 0` in `K`, then `v` lies in every submodule containing the
relabelled generators. -/
theorem val_mem_of_cert {W : Submodule K (FreeBin K G (Fin 3))} (gens : List (Cert3 G))
    (hgens : ∀ g ∈ gens, ∀ τ, val K (act τ g) ∈ W) (v : Cert3 G) (d : ℤ) (hd : (d : K) ≠ 0)
    (c : MemCert) (hv : ∀ m, d * coeff v m = coeff (MemCert.sum gens c) m) : val K v ∈ W := by
  have h : (d : K) • val K v = val K (MemCert.sum gens c) := by
    rw [← val_smul]
    exact val_eq_of_coeff K fun m => by rw [coeff_smul, hv]
  have hmem := val_memCertSum K gens hgens c
  rw [← h] at hmem
  simpa [smul_smul, inv_mul_cancel₀ hd] using Submodule.smul_mem W (d : K)⁻¹ hmem

end Membership

/-! ## The generators of the relations of arity three -/

section Generators

variable [Fintype G] [DecidableEq G] (K : Type u) [Field K]

/-- **The generators of the relations of arity three** of relators `r₂` of arity two and `r₃` of
arity three, for the monomials of arity two on the generators `gs`: the composites of the
relators of arity two with the monomials, at either input and on either side, and the relators of
arity three. -/
noncomputable def gens23 (gs : List G) (r₂ : List (Cert2 G)) (r₃ : List (Cert3 G)) :
    List (Cert3 G) :=
  (r₂.flatMap fun a => gs.flatMap fun g => [1, Equiv.swap 0 1].flatMap fun σ =>
    [comp0 a [((g, σ), 1)], comp1 a [((g, σ), 1)], comp0 [((g, σ), 1)] a,
      comp1 [((g, σ), 1)] a]) ++ r₃

omit [Fintype G] [DecidableEq G] in
lemma bin2_eq_val (g : G) (σ : Equiv.Perm (Fin 2)) : bin2 g σ = Cert2.val K [((g, σ), 1)] := by
  simp

/-- **The generators lie in the relations of arity three**, with all their relabellings. -/
theorem gens23_mem (gs : List G) (r₂ : List (Cert2 G)) (r₃ : List (Cert3 G)) :
    ∀ g ∈ gens23 gs r₂ r₃, ∀ τ : Equiv.Perm (Fin 3), val K (act τ g) ∈
      ideal3Of K (Cert2.val K '' {a | a ∈ r₂}) ⊔
        Submodule.span K (orbit3 K (Cert3.val K '' {r | r ∈ r₃})) := by
  intro g hg τ
  rw [← map_val]
  rw [gens23, List.mem_append, List.mem_flatMap] at hg
  rcases hg with ⟨a, ha, hg⟩ | hg
  · refine Submodule.mem_sup_left (ideal3Of_map_mem τ ?_)
    simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hg
    obtain ⟨g', -, σ, -, hg⟩ := hg
    have ha' : Cert2.val K a ∈ Cert2.val K '' {a | a ∈ r₂} := ⟨a, ha, rfl⟩
    rcases hg with rfl | rfl | rfl | rfl
    · rw [← comp0_val]
      exact Submodule.subset_span ⟨0, e0, _, _, Or.inl ha', rfl⟩
    · rw [← comp1_val]
      exact Submodule.subset_span ⟨1, e1, _, _, Or.inl ha', rfl⟩
    · rw [← comp0_val]
      exact Submodule.subset_span ⟨0, e0, _, _, Or.inr ha', rfl⟩
    · rw [← comp1_val]
      exact Submodule.subset_span ⟨1, e1, _, _, Or.inr ha', rfl⟩
  · exact Submodule.mem_sup_right
      (mem_orbit3 K (r := Cert3.val K '' {r | r ∈ r₃}) ⟨g, hg, rfl⟩ τ)

end Generators

/-! ## Orthogonality -/

section Orthogonality

variable [Fintype G] [DecidableEq G] (K : Type u) [Field K]

/-- **Orthogonality by certificate**: a certificate whose relabellings are orthogonal to the
composites of the relators of arity two with the monomials and to the relators of arity three
lies in the Koszul dual relations. -/
theorem val_mem_dualRel23 (r₂ : List (Cert2 G)) (r₃ : List (Cert3 G)) (u : Cert3 G)
    (h₂ : ∀ τ : Equiv.Perm (Fin 3), ∀ a ∈ r₂, ∀ g : G, ∀ σ : Equiv.Perm (Fin 2),
      pair (act τ u) (comp0 a [((g, σ), 1)]) = 0 ∧ pair (act τ u) (comp1 a [((g, σ), 1)]) = 0 ∧
      pair (act τ u) (comp0 [((g, σ), 1)] a) = 0 ∧ pair (act τ u) (comp1 [((g, σ), 1)] a) = 0)
    (h₃ : ∀ τ : Equiv.Perm (Fin 3), ∀ r ∈ r₃, pair (act τ u) r = 0) :
    val K u ∈ dualRel23 K (Cert2.val K '' {a | a ∈ r₂}) (Cert3.val K '' {r | r ∈ r₃}) := by
  let S : Submodule K (FreeBin K G (Fin 3)) :=
    ⨅ τ : Equiv.Perm (Fin 3), LinearMap.ker (pair3 G K (val K (act τ u)))
  have hS : ∀ w, w ∈ S ↔ ∀ τ : Equiv.Perm (Fin 3), pair3 G K (val K (act τ u)) w = 0 := by
    intro w
    simp [S]
  have hSmap : ∀ (σ : Equiv.Perm (Fin 3)) w, w ∈ S → SymOperad.map (R := K) σ w ∈ S := by
    intro σ w hw
    rw [hS] at hw ⊢
    intro τ
    have h := pair3_map K σ (SymOperad.map (R := K) σ⁻¹ (val K (act τ u))) w
    rw [SymOperad.map_map, show σ⁻¹.trans σ = Equiv.refl _ by ext; simp, SymOperad.map_refl,
      map_val, show act σ⁻¹ (act τ u) = act (τ.trans σ⁻¹) u by
        simp only [act, List.map_map]; rfl, hw, mul_zero] at h
    exact h
  have hW : ideal3Of K (Cert2.val K '' {a | a ∈ r₂}) ⊔
      Submodule.span K (orbit3 K (Cert3.val K '' {r | r ∈ r₃})) ≤ S := by
    refine sup_le (ideal3Of_le K hSmap fun a ha g σ => ?_) ?_
    · obtain ⟨a, ha, rfl⟩ := ha
      have h := h₂
      simp only [hS, bin2_eq_val K, comp0_val, comp1_val, pair3_val] at h ⊢
      exact ⟨fun τ => by simp [(h τ a ha g σ).1], fun τ => by simp [(h τ a ha g σ).2.1],
        fun τ => by simp [(h τ a ha g σ).2.2.1], fun τ => by simp [(h τ a ha g σ).2.2.2]⟩
    · rw [Submodule.span_le]
      rintro _ ⟨σ, _, ⟨r, hr, rfl⟩, rfl⟩
      refine hSmap σ _ ((hS _).2 fun τ => ?_)
      rw [pair3_val, h₃ τ r hr, Int.cast_zero]
  have hW' : Submodule.span K (orbit3 K ((ideal3Of K (Cert2.val K '' {a | a ∈ r₂}) ⊔
      Submodule.span K (orbit3 K (Cert3.val K '' {r | r ∈ r₃})) : Submodule K _) :
        Set (FreeBin K G (Fin 3)))) ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨σ, w, hw, rfl⟩
    exact hSmap σ w (hW hw)
  intro n hn
  have h := (hS n).1 (hW' hn) 1
  rw [show act 1 u = u by simp [act, act3]] at h
  show pair3 G K n (val K u) = 0
  rw [pair3_comm]
  exact h

end Orthogonality

/-! ## Dimension -/

section Dimension

variable [Fintype G] [DecidableEq G] (K : Type u) [Field K] [CharZero K]

/-- **A lower bound on a dimension by certificate**: certificates in `W`, each with a monomial
where it alone among them has a nonzero coefficient. -/
theorem le_finrank_of_cert {W : Submodule K (FreeBin K G (Fin 3))} (l : List (Cert3 G × Mono3 G))
    (hl : ∀ x ∈ l, val K x.1 ∈ W)
    (h : ∀ i j : Fin l.length, coeff (l.get j).1 (l.get i).2 ≠ 0 ↔ j = i) :
    l.length ≤ Module.finrank K W := by
  have := le_finrank_of_private K (fun i : Fin l.length => val K (l.get i).1)
    (fun i => hl _ (List.get_mem l i)) (fun i => (l.get i).2)
    (fun i j => by rw [repr_val, Int.cast_ne_zero]; exact h i j)
  simpa using this

end Dimension

/-! ## Koszul dual relations by certificate -/

section Dual

variable [Fintype G] [DecidableEq G] (K : Type u) [Field K] [CharZero K]

omit [Fintype G] [DecidableEq G] [CharZero K] in
lemma sup_map_mem' {W W' : Submodule K (FreeBin K G (Fin 3))}
    (hW : ∀ τ : Equiv.Perm (Fin 3), ∀ x ∈ W, SymOperad.map (R := K) τ x ∈ W)
    (hW' : ∀ τ : Equiv.Perm (Fin 3), ∀ x ∈ W', SymOperad.map (R := K) τ x ∈ W')
    (τ : Equiv.Perm (Fin 3)) {x : FreeBin K G (Fin 3)} (hx : x ∈ W ⊔ W') :
    SymOperad.map (R := K) τ x ∈ W ⊔ W' := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add]
  exact add_mem (Submodule.mem_sup_left (hW τ a ha)) (Submodule.mem_sup_right (hW' τ b hb))

omit [Fintype G] [DecidableEq G] [CharZero K] in
lemma rel3_map_mem (r₂ : Set (FreeBin K G (Fin 2))) (r₃ : Set (FreeBin K G (Fin 3)))
    (τ : Equiv.Perm (Fin 3)) {x : FreeBin K G (Fin 3)}
    (hx : x ∈ ideal3Of K r₂ ⊔ Submodule.span K (orbit3 K r₃)) :
    SymOperad.map (R := K) τ x ∈ ideal3Of K r₂ ⊔ Submodule.span K (orbit3 K r₃) :=
  sup_map_mem' K (fun τ _ hx => ideal3Of_map_mem τ hx) (fun τ _ hx => map_mem_span_orbit3 K τ hx)
    τ hx

/-- **The Koszul dual relations by certificate**: if the relations of `r₂` and `r₃` contain
`dim.length` certificates with private coordinates, and `U` consists of certificates orthogonal to
the relabelled generators with private coordinates, of the complementary number, then the dual
relations are the span of `U`. -/
theorem dualRel23_eq_span_of_cert (gs : List G) (r₂ : List (Cert2 G)) (r₃ : List (Cert3 G))
    (dim : List (MemCert × Mono3 G)) (U : List (Cert3 G × Mono3 G))
    (hcard : 12 * Fintype.card G ^ 2 ≤ dim.length + U.length)
    (hdim : ∀ i j : Fin dim.length,
      coeff (MemCert.sum (gens23 gs r₂ r₃) (dim.get j).1) (dim.get i).2 ≠ 0 ↔ j = i)
    (hU : ∀ i j : Fin U.length, coeff (U.get j).1 (U.get i).2 ≠ 0 ↔ j = i)
    (h₂ : ∀ u ∈ U, ∀ τ : Equiv.Perm (Fin 3), ∀ a ∈ r₂, ∀ g : G, ∀ σ : Equiv.Perm (Fin 2),
      pair (act τ u.1) (comp0 a [((g, σ), 1)]) = 0 ∧ pair (act τ u.1) (comp1 a [((g, σ), 1)]) = 0 ∧
      pair (act τ u.1) (comp0 [((g, σ), 1)] a) = 0 ∧ pair (act τ u.1) (comp1 [((g, σ), 1)] a) = 0)
    (h₃ : ∀ u ∈ U, ∀ τ : Equiv.Perm (Fin 3), ∀ r ∈ r₃, pair (act τ u.1) r = 0) :
    dualRel23 K (Cert2.val K '' {a | a ∈ r₂}) (Cert3.val K '' {r | r ∈ r₃})
      = Submodule.span K (Cert3.val K '' {u | u ∈ U.map Prod.fst}) := by
  set W := ideal3Of K (Cert2.val K '' {a | a ∈ r₂}) ⊔
    Submodule.span K (orbit3 K (Cert3.val K '' {r | r ∈ r₃}))
  have hle : Submodule.span K (Cert3.val K '' {u | u ∈ U.map Prod.fst})
      ≤ dualRel23 K (Cert2.val K '' {a | a ∈ r₂}) (Cert3.val K '' {r | r ∈ r₃}) := by
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hu
    exact val_mem_dualRel23 K r₂ r₃ x.1 (h₂ x hx) (h₃ x hx)
  have hdimW : dim.length ≤ Module.finrank K W := by
    have := le_finrank_of_cert K (W := W)
      (dim.map fun x => (MemCert.sum (gens23 gs r₂ r₃) x.1, x.2))
      (fun x hx => by
        obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
        exact val_memCertSum K _ (gens23_mem K gs r₂ r₃) y.1)
      (fun i j => by simpa using hdim (i.cast (by simp)) (j.cast (by simp)))
    simpa using this
  have hdimU : U.length ≤ Module.finrank K
      (Submodule.span K (Cert3.val K '' {u | u ∈ U.map Prod.fst})) :=
    le_finrank_of_cert K U (fun x hx => Submodule.subset_span ⟨x.1, List.mem_map_of_mem hx, rfl⟩)
      hU
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  have hspan : Submodule.span K (orbit3 K (W : Set (FreeBin K G (Fin 3)))) = W :=
    span_orbit3_eq K fun τ _ hx => rel3_map_mem K _ _ τ hx
  have hfin := finrank_dualRel K (W : Set (FreeBin K G (Fin 3)))
  rw [hspan] at hfin
  rw [dualRel23, hfin]
  omega

/-- **Koszul dual presentations by certificate**: with the dual relations spanned by `U` as in
`dualRel23_eq_span_of_cert`, if the relators of arity two `s₂` are the twisted `r₂`, every element
of `U` is an integer combination of the relabelled generators of `s₂` and `s₃`, and a nonzero
multiple of every element of `s₃` one of the relabelled generators of `s₂` and `U`, then the
Koszul dual of the operad presented by `r₂` and `r₃` is presented by `s₂` and `s₃`. -/
theorem dual23_span_eq_of_cert (gs : List G) (r₂ : List (Cert2 G)) (r₃ : List (Cert3 G))
    (s₂ : List (Cert2 G)) (s₃ : List (Cert3 G)) (U : List (Cert3 G × Mono3 G))
    (hU : dualRel23 K (Cert2.val K '' {a | a ∈ r₂}) (Cert3.val K '' {r | r ∈ r₃})
      = Submodule.span K (Cert3.val K '' {u | u ∈ U.map Prod.fst}))
    (htwist : twist2 K '' (Cert2.val K '' {a | a ∈ r₂}) = Cert2.val K '' {a | a ∈ s₂})
    (memU : List MemCert) (hmemU : ∀ x ∈ U.zip memU, ∀ m,
      coeff x.1.1 m = coeff (MemCert.sum (gens23 gs s₂ s₃) x.2) m)
    (hlenU : U.length ≤ memU.length)
    (memS : List (ℤ × MemCert)) (hmemS : ∀ x ∈ s₃.zip memS, x.2.1 ≠ 0 ∧ ∀ m,
      x.2.1 * coeff x.1 m = coeff (MemCert.sum (gens23 gs s₂ (U.map Prod.fst)) x.2.2) m)
    (hlenS : s₃.length ≤ memS.length) :
    SymOperadIdeal.span K (rel23 (twist2 K '' (Cert2.val K '' {a | a ∈ r₂}))
        (dualRel23 K (Cert2.val K '' {a | a ∈ r₂}) (Cert3.val K '' {r | r ∈ r₃}) :
          Set (FreeBin K G (Fin 3))))
      = SymOperadIdeal.span K (rel23 (Cert2.val K '' {a | a ∈ s₂})
          (Cert3.val K '' {r | r ∈ s₃})) := by
  rw [htwist]
  set Ws := ideal3Of K (Cert2.val K '' {a | a ∈ s₂}) ⊔
    Submodule.span K (orbit3 K (Cert3.val K '' {r | r ∈ s₃}))
  set Wd := ideal3Of K (Cert2.val K '' {a | a ∈ s₂}) ⊔ Submodule.span K (orbit3 K
    (dualRel23 K (Cert2.val K '' {a | a ∈ r₂}) (Cert3.val K '' {r | r ∈ r₃}) :
      Set (FreeBin K G (Fin 3))))
  have hself : ∀ x ∈ Cert2.val K '' {a | a ∈ s₂},
      x ∈ Submodule.span K (orbit2 K (Cert2.val K '' {a | a ∈ s₂})) := fun x hx =>
    Submodule.subset_span ⟨1, x, hx, by
      rw [show (1 : Equiv.Perm (Fin 2)) = Equiv.refl _ from rfl, SymOperad.map_refl]⟩
  -- the elements of `U` lie in `Ws`
  have hUWs : ∀ u ∈ U.map Prod.fst, Cert3.val K u ∈ Ws := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hu
    have hi' : i < U.length := by simpa using hi
    have hx : (U[i], memU[i]'(by omega)) ∈ U.zip memU := by
      rw [List.mem_iff_getElem]
      exact ⟨i, by simp; omega, by simp⟩
    rw [List.getElem_map]
    exact val_mem_of_cert K (gens23 gs s₂ s₃) (gens23_mem K gs s₂ s₃) _ 1 (by simp) _
      fun m => by rw [one_mul]; exact hmemU _ hx m
  have hdWs : (dualRel23 K (Cert2.val K '' {a | a ∈ r₂}) (Cert3.val K '' {r | r ∈ r₃}) :
      Set (FreeBin K G (Fin 3))) ⊆ Ws := by
    rw [hU]
    intro x hx
    refine (Submodule.span_le.2 ?_) hx
    rintro _ ⟨u, hu, rfl⟩
    exact hUWs u hu
  -- the elements of `s₃` lie in `Wd`
  have hUd : ∀ u ∈ U.map Prod.fst, Cert3.val K u ∈
      dualRel23 K (Cert2.val K '' {a | a ∈ r₂}) (Cert3.val K '' {r | r ∈ r₃}) := fun u hu => by
    rw [hU]
    exact Submodule.subset_span ⟨u, hu, rfl⟩
  have hs₃ : ∀ r ∈ s₃, Cert3.val K r ∈ Wd := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
    have hx : (s₃[i], memS[i]'(by omega)) ∈ s₃.zip memS := by
      rw [List.mem_iff_getElem]
      exact ⟨i, by simp; omega, by simp⟩
    obtain ⟨hd, hm⟩ := hmemS _ hx
    have hsub : ideal3Of K (Cert2.val K '' {a | a ∈ s₂}) ⊔
        Submodule.span K (orbit3 K (Cert3.val K '' {u | u ∈ U.map Prod.fst})) ≤ Wd := by
      refine sup_le_sup_left (Submodule.span_mono ?_) _
      rintro _ ⟨τ, _, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨τ, _, hUd u hu, rfl⟩
    exact hsub (val_mem_of_cert K (gens23 gs s₂ (U.map Prod.fst))
      (gens23_mem K gs s₂ (U.map Prod.fst)) _ _ (by exact_mod_cast hd) _ hm)
  apply le_antisymm
  · refine span_le_23 hself fun x hx => ?_
    exact hdWs hx
  · refine span_le_23 hself fun x hx => ?_
    obtain ⟨r, hr, rfl⟩ := hx
    exact hs₃ r hr

end Dual


end FreeBin

end Operad
