/-
# Invariant families on a cooperad of alternating lines

A **cooperad of alternating lines** (`AltGen`) is a coaugmented graded cooperad `C` over a field
with an element `ν n` on `n + 1` inputs, for every `n`, such that: the `ν n` alternate; every
element on a set of `n + 1` inputs is a multiple of a relabelling of `ν n`; `C` vanishes on no
inputs; `ν 0` is the coaugmentation; every element has the parity of its number of inputs plus
one; and the decomposition of a relabelling of `ν n` at a factorization of the standard order
is the tensor of the corresponding relabellings of the `ν`, with the sign of the signed linear
orders. The Koszul dual cooperad of `Lie` is one (`LieDual.altGen`, in
`Operad/LieTwisting.lean`).

For an invariant family `α : C → Q` with values in a graded operad `Q`, with operations
`AltGen.lam ν α n = α (ν n)`:

* the operations alternate (`AltGen.map_lam`) and determine the family (`AltGen.inv_ext`);
* **the convolution product at a generator** (`AltGen.star_nu`): `(α ⋆ α') (ν n)` is the sum,
  over the nonempty subsets `S` of the inputs, of the planar term at the initial window of `|S|`
  inputs of the families of operations on the signed linear orders (`NOrd.plTN`), moved to `S`
  by any permutation carrying the initial window onto `S` and multiplied by its sign. The term
  at an initial window is `AltGen.toLin_term_ini`; the others follow by `GrOperad.Inv.map_term`
  and the alternation of the `ν n`;
* the family is odd iff its operation of arity `n + 1` has the parity of `n + 1`
  (`AltGen.isPar_iff`), and it kills the coaugmentation iff its operation of arity one vanishes
  (`AltGen.killsUnit_iff`);
* along a morphism `ψ : C → OrdCo K` carrying the `ν n` to the alternating sums, the operations
  of a pulled back family are the alternating sums of its operations (`AltGen.lam_appHom`), and
  **in characteristic zero every alternating family is the family of operations of an invariant
  family** (`AltGen.exists_lam`).
-/
import Operad.LieAlt

universe u v w

namespace Operad

open Sym GerBV
open scoped TensorProduct

/-- **A cooperad of alternating lines**: a coaugmented graded cooperad `C` with an element `ν n`
on `n + 1` inputs, for every `n`, which alternates, spans `C` on `n + 1` inputs, and whose
decompositions are the tensors of the `ν`, with the signs of the signed linear orders. -/
structure AltGen (K : Type u) [Field K]
    (C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (C A)] [GrCooperad K C]
    [GrCooperad.Coaug K C] (ν : ∀ n : ℕ, C (Fin (n + 1))) : Prop where
  /-- The generators alternate. -/
  map_nu : ∀ (n : ℕ) (τ : Equiv.Perm (Fin (n + 1))),
    SymSpecies.map (R := K) τ (ν n) = ((Equiv.Perm.sign τ : ℤ) : K) • ν n
  /-- An element on a set of inputs has the parity of its number of inputs plus one. -/
  par_self : ∀ (A : Type) [Fintype A] [DecidableEq A] (y : C A),
    GrSpecies.par (R := K) (Fintype.card A + 1).bodd y = y
  /-- The generators span. -/
  span : ∀ (A : Type) [Fintype A] [DecidableEq A] (n : ℕ) (e : Fin (n + 1) ≃ A) (y : C A),
    ∃ c : K, y = c • SymSpecies.map (R := K) e (ν n)
  /-- Nothing on no inputs. -/
  empty : ∀ (A : Type) [Fintype A] [DecidableEq A] [IsEmpty A] (y : C A), y = 0
  /-- The generator on one input is the coaugmentation. -/
  one : ν 0 = SymSpecies.map (R := K) (Equiv.ofUnique Unit (Fin 1))
    (GrCooperad.Coaug.one (R := K) (C := C))
  /-- The decomposition of a generator at a factorization of the standard order. -/
  decomp : ∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (n m l : ℕ) (e : Fin (n + 1) ≃ Without A i ⊕ B) (f : Fin (m + 1) ≃ A) (g : Fin (l + 1) ≃ B),
    SetOperad.comp i (SetOperad.map f (OrdCo.sd m)) (SetOperad.map g (OrdCo.sd l))
        = SetOperad.map e (OrdCo.sd n) →
      GrCooperad.decomp (R := K) (C := C) (B := B) i (SymSpecies.map (R := K) e (ν n))
        = σ K (SgnData.sgn i (NOrd.sgnD.app A (SetOperad.map f (OrdCo.sd m)))
            (NOrd.sgnD.app B (SetOperad.map g (OrdCo.sd l)))) •
          (SymSpecies.map (R := K) f (ν m) ⊗ₜ[K] SymSpecies.map (R := K) g (ν l))

namespace AltGen

open OrdCo

variable {K : Type u} [Field K]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (C A)] [GrCooperad K C]
  [GrCooperad.Coaug K C]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (Q A)] [GrOperad K Q]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-! ## Invariant families -/

omit [GrCooperad.Coaug K C] in
/-- An invariant family commutes with the relabellings. -/
lemma toLin_map (α : GrOperad.Inv K (ConvOp K C Q)) (e : A ≃ B) (y : C A) :
    ConvOp.toLin (α.1 B) (SymSpecies.map (R := K) e y)
      = GrOperad.map (R := K) e (ConvOp.toLin (α.1 A) y) := by
  rw [← GrOperad.Inv.map_apply α e]
  show GrOperad.map (R := K) e (ConvOp.toLin _ (SymSpecies.map (R := K) e.symm
    (SymSpecies.map (R := K) e y))) = _
  rw [← SymSpecies.map_trans, Equiv.self_trans_symm, SymSpecies.map_refl]

omit [GrCooperad.Coaug K C] in
/-- **A convolution composite on an element with a pure decomposition.** -/
lemma compC_of_decomp (i : A) (F : ConvOp K C Q A) {G : ConvOp K C Q B}
    (hG : ConvOp.IsParC true G) {z : C (Without A i ⊕ B)} {c : K} {u : C A} {v : C B}
    (hz : GrCooperad.decomp (R := K) (C := C) (B := B) i z = c • (u ⊗ₜ[K] v)) :
    ConvOp.toLin (ConvOp.compC i F G) z
      = c • GrOperad.comp (R := K) i (ConvOp.toLin F (GrSpecies.tw (R := K) true u))
          (ConvOp.toLin G v) := by
  rw [ConvOp.toLin_compC, LinearMap.comp_apply, LinearMap.comp_apply, hz, LinearMap.map_smul,
    LinearMap.map_smul, ConvOp.kap_tmul F hG, ConvOp.mu_tmul]

variable (ν : ∀ n : ℕ, C (Fin (n + 1)))

omit [GrCooperad.Coaug K C] in
/-- **The family of operations of an invariant family**: its values at the generators. -/
noncomputable def lam (α : GrOperad.Inv K (ConvOp K C Q)) (n : ℕ) : Q (Fin (n + 1)) :=
  ConvOp.toLin (α.1 (Fin (n + 1))) (ν n)

variable {ν} (H : AltGen K C ν)

include H

/-- **The operations of an invariant family alternate.** -/
lemma map_lam (α : GrOperad.Inv K (ConvOp K C Q)) (n : ℕ) (τ : Equiv.Perm (Fin (n + 1))) :
    GrOperad.map (R := K) τ (lam ν α n) = ((Equiv.Perm.sign τ : ℤ) : K) • lam ν α n := by
  rw [lam, ← toLin_map, H.map_nu, LinearMap.map_smul]

/-- **An invariant family is determined by its operations.** -/
theorem inv_ext {α α' : GrOperad.Inv K (ConvOp K C Q)} (h : ∀ n, lam ν α n = lam ν α' n) :
    α = α' := by
  refine Subtype.ext (funext fun A => funext fun _ => funext fun _ => ?_)
  refine ConvOp.ext fun y => ?_
  rcases isEmpty_or_nonempty A with hA | hA
  · rw [H.empty A y, LinearMap.map_zero, LinearMap.map_zero]
  · obtain ⟨n, hn⟩ : ∃ n, Fintype.card A = n + 1 :=
      ⟨Fintype.card A - 1, by have := Fintype.card_pos (α := A); omega⟩
    obtain ⟨c, rfl⟩ := H.span A n (Fintype.equivFinOfCardEq hn).symm y
    rw [LinearMap.map_smul, LinearMap.map_smul, toLin_map, toLin_map]
    exact congrArg (fun x => c • GrOperad.map (R := K) _ x) (h n)

/-! ## The convolution product at a generator -/

omit H in
/-- The initial window of `l` inputs. -/
def ini (N l : ℕ) : Finset (Fin N) := Finset.univ.filter fun x => (x : ℕ) < l

omit H in
lemma mem_ini {N l : ℕ} {x : Fin N} : x ∈ ini N l ↔ (x : ℕ) < l := by
  rw [ini, Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ x)

omit H in
lemma card_ini {N l : ℕ} (h : l ≤ N) : (ini N l).card = l := by
  have he : ini N l = (Finset.univ : Finset (Fin l)).map (Fin.castLEEmb h) := by
    ext x
    rw [mem_ini, Finset.mem_map]
    exact ⟨fun hx => ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩, by
      rintro ⟨a, -, rfl⟩
      exact a.2⟩
  rw [he, Finset.card_map, Finset.card_univ, Fintype.card_fin]

omit H [GrCooperad K C] [GrCooperad.Coaug K C] in
lemma famOf_ofFam (a : ∀ n : ℕ, Q (Fin (n + 1))) (n : ℕ) : famOf (ofFam (K := K) a) n = a n :=
  congrFun ((invEquiv (K := K) (Q := Q)).right_inv a) n

/-- **The term of the convolution product at an initial window, at a generator**: the planar
term of the families of operations, on the signed linear orders. -/
theorem toLin_term_ini (α α' : GrOperad.Inv K (ConvOp K C Q))
    (hα' : GrOperad.Inv.IsPar true α') (n l : ℕ) (hl : 0 < l) (hln : l ≤ n + 1) :
    ConvOp.toLin (GrOperad.Inv.term (R := K) α.1 α'.1 (Fin (n + 1)) (ini (n + 1) l)) (ν n)
      = NOrd.plTN (ofFam (K := K) (lam ν α)) (ofFam (K := K) (lam ν α')) (n + 1)
        (n + 1 - l, 0) := by
  obtain ⟨S₀, hS₀⟩ : ∃ S₀, S₀ = ini (n + 1) l := ⟨_, rfl⟩
  rw [← hS₀]
  have hr : (0 : Fin (n + 1)) ∈ S₀ := hS₀ ▸ mem_ini.2 hl
  have hcard : S₀.card = l := hS₀ ▸ card_ini hln
  obtain ⟨p, q, hpq⟩ := NOrd.exists_fact n.succ_pos hr fun x y hx hy z hxz hzy => by
    rw [hS₀] at hy ⊢
    exact mem_ini.2 (lt_of_le_of_lt hzy (mem_ini.1 hy))
  obtain ⟨m', f, rfl⟩ := exists_std p
  obtain ⟨l', g, rfl⟩ := exists_std q
  have hodd : ConvOp.IsParC true (α'.1 (SIn S₀)) := ConvOp.parC_eq_self_iff.1 (hα' (SIn S₀))
  have hstd : SetOperad.map (splitEquiv S₀)
      (SetOperad.comp none (SetOperad.map f (sd m')) (SetOperad.map g (sd l')))
        = NOrd.std (n + 1) n.succ_pos := by
    rw [hpq, SetOperad.map_map_symm]
  have hL : ConvOp.toLin (GrOperad.Inv.term (R := K) α.1 α'.1 (Fin (n + 1)) S₀) (ν n)
      = GrOperad.map (R := K) (splitEquiv S₀) (ConvOp.toLin
          (ConvOp.compC none (α.1 (SOut S₀)) (α'.1 (SIn S₀)))
          (SymSpecies.map (R := K) (splitEquiv S₀).symm (ν n))) := rfl
  have hX : ConvOp.toLin (α.1 (SOut S₀))
        (GrSpecies.tw (R := K) true (SymSpecies.map (R := K) f (ν m')))
      = ConvOp.toLin ((ofFam (K := K) (lam ν α)).1 (SOut S₀))
        (GrSpecies.tw (R := K) true (SgnLin.bas NOrd.sgnD K (SetOperad.map f (sd m')))) := by
    rw [GrSpecies.tw_hom true (H.par_self (SOut S₀) (SymSpecies.map (R := K) f (ν m'))),
      GrSpecies.tw_hom true (show GrSpecies.par (R := K) (Fintype.card (SOut S₀) + 1).bodd
        (SgnLin.bas NOrd.sgnD K (SetOperad.map f (sd m')) : OrdCo K (SOut S₀)) = _ from by
          rw [OrdCo.par_bs, if_pos rfl]),
      LinearMap.map_smul, LinearMap.map_smul, toLin_map, toLin_bs_map, famOf_ofFam]
    rfl
  have hY : ConvOp.toLin (α'.1 (SIn S₀)) (SymSpecies.map (R := K) g (ν l'))
      = ConvOp.toLin ((ofFam (K := K) (lam ν α')).1 (SIn S₀))
        (SgnLin.bas NOrd.sgnD K (SetOperad.map g (sd l'))) := by
    rw [toLin_map, toLin_bs_map, famOf_ofFam]
    rfl
  have hR : NOrd.plTN (ofFam (K := K) (lam ν α)) (ofFam (K := K) (lam ν α')) (n + 1)
        (n + 1 - l, 0)
      = SgnLin.repW (ofFam (K := K) (lam ν α)) (ofFam (K := K) (lam ν α')) (splitEquiv S₀)
        (SetOperad.map f (sd m')) (SetOperad.map g (sd l')) := by
    rw [NOrd.plTN, dif_pos ⟨Nat.zero_le _, by show n + 1 - l < n + 1; omega⟩]
    symm
    have hcO := NOrd.card_SOut S₀
    rw [Fintype.card_fin, hcard] at hcO
    refine NOrd.repW_eq_of_fact _ _ (hstd.trans ?_) ?_ ?_ ?_
    · exact (Subtype.ext (map_posEquivF _ _)).symm
    · rw [Fintype.card_fin]
      omega
    · rw [NOrd.card_SIn, Fintype.card_fin, hcard]
      omega
    · have hb := (NOrd.mem_block hstd (0 : Fin (n + 1))).1 hr
      have h0 : (NOrd.std (n + 1) n.succ_pos).1.rank (0 : Fin (n + 1)) = 0 :=
        LinOrd.rank_std (n + 1) 0
      rw [h0] at hb
      exact (Nat.le_zero.1 hb.1).trans
        (LinOrd.rank_std (n + 1 - l + 1) ⟨0, by omega⟩).symm
  rw [hL, compC_of_decomp none _ hodd
    (H.decomp (SOut S₀) (SIn S₀) none n m' l' (splitEquiv S₀).symm f g hpq), hX, hY, hR]
  rfl

/-- **The convolution product at a generator**: the sum, over the nonempty subsets of the
inputs, of the planar terms at the initial windows, moved to the subset by a permutation and
multiplied by its sign. -/
theorem star_nu (α α' : GrOperad.Inv K (ConvOp K C Q)) (hα' : GrOperad.Inv.IsPar true α')
    (n : ℕ) (ω : Finset (Fin (n + 1)) → Equiv.Perm (Fin (n + 1)))
    (hω : ∀ S, (ini (n + 1) S.card).map (ω S).toEmbedding = S) :
    ConvOp.toLin ((GrOperad.Inv.star K _ α α').1 (Fin (n + 1))) (ν n)
      = ∑ S ∈ nonempties (Fin (n + 1)), ((Equiv.Perm.sign (ω S) : ℤ) : K) •
          GrOperad.map (R := K) (ω S) (NOrd.plTN (ofFam (K := K) (lam ν α))
            (ofFam (K := K) (lam ν α')) (n + 1) (n + 1 - S.card, 0)) := by
  rw [GrOperad.Inv.star_apply, ConvOp.toLin_sum, LinearMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hne : S.Nonempty := NOrd.mem_nonempties.1 hS
  have hle : S.card ≤ n + 1 := (Finset.card_le_univ S).trans (Fintype.card_fin _).le
  have h1 : GrOperad.Inv.term (R := K) α.1 α'.1 (Fin (n + 1)) S
      = GrOperad.map (R := K) (ω S)
        (GrOperad.Inv.term (R := K) α.1 α'.1 (Fin (n + 1)) (ini (n + 1) S.card)) :=
    (congrArg (fun T => GrOperad.Inv.term (R := K) α.1 α'.1 (Fin (n + 1)) T) (hω S).symm).trans
      (GrOperad.Inv.map_term α α' (ω S) _).symm
  rw [h1]
  show GrOperad.map (R := K) (ω S) (ConvOp.toLin
    (GrOperad.Inv.term (R := K) α.1 α'.1 (Fin (n + 1)) (ini (n + 1) S.card))
    (SymSpecies.map (R := K) (ω S)⁻¹ (ν n))) = _
  rw [H.map_nu, Equiv.Perm.sign_inv, LinearMap.map_smul, LinearMap.map_smul,
    H.toLin_term_ini α α' hα' n S.card hne.card_pos hle]

/-! ## Parity and units -/

/-- **An invariant family is odd** iff its operation of arity `n + 1` has the parity of
`n + 1`. -/
theorem isPar_iff (α : GrOperad.Inv K (ConvOp K C Q)) :
    GrOperad.Inv.IsPar true α
      ↔ ∀ n, GrOperad.par (R := K) (n + 1).bodd (lam ν α n) = lam ν α n := by
  have hb : ∀ n : ℕ, (n + 1 + 1).bodd = !(n + 1).bodd := fun n => Nat.bodd_succ (n + 1)
  constructor
  · intro h n
    have hc := (ConvOp.parC_eq_self_iff.1 (h (Fin (n + 1)))) (n + 1 + 1).bodd (ν n)
    have hp := H.par_self (Fin (n + 1)) (ν n)
    rw [Fintype.card_fin] at hp
    rw [hp] at hc
    have hx : xor (n + 1 + 1).bodd true = (n + 1).bodd := by
      rw [hb]
      cases (n + 1).bodd <;> rfl
    rw [hx] at hc
    exact hc.symm
  · intro h A _ _
    refine ConvOp.parC_eq_self_iff.2 fun c x => ?_
    rcases isEmpty_or_nonempty A with hA | hA
    · rw [H.empty A x, LinearMap.map_zero, LinearMap.map_zero, LinearMap.map_zero]
    · obtain ⟨n, hn⟩ : ∃ n, Fintype.card A = n + 1 :=
        ⟨Fintype.card A - 1, by have := Fintype.card_pos (α := A); omega⟩
      obtain ⟨c', rfl⟩ := H.span A n (Fintype.equivFinOfCardEq hn).symm x
      obtain ⟨y, hy⟩ : ∃ y : C A,
        y = SymSpecies.map (R := K) (Fintype.equivFinOfCardEq hn).symm (ν n) := ⟨_, rfl⟩
      rw [← hy]
      have hy0 := H.par_self A y
      rw [hn] at hy0
      have hyQ : GrOperad.par (R := K) (n + 1).bodd (ConvOp.toLin (α.1 A) y)
          = ConvOp.toLin (α.1 A) y := by
        rw [hy, toLin_map, ← GrOperad.map_par]
        exact congrArg _ (h n)
      rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul]
      congr 1
      by_cases hc : c = (n + 1 + 1).bodd
      · rw [hc, hy0, hb, show xor (!(n + 1).bodd) true = (n + 1).bodd from by
          cases (n + 1).bodd <;> rfl, hyQ]
      · have h0 : GrSpecies.par (R := K) c y = 0 :=
          (congrArg (GrSpecies.par (R := K) c) hy0).symm.trans (GrSpecies.par_par_ne hc y)
        have hne : xor c true ≠ (n + 1).bodd := by
          intro h'
          apply hc
          rw [hb, ← h']
          cases c <;> rfl
        rw [h0, LinearMap.map_zero, ← hyQ, GrOperad.par_par, if_neg hne]

/-- **An invariant family kills the coaugmentation** iff its operation of arity one vanishes. -/
theorem killsUnit_iff (α : GrOperad.Inv K (ConvOp K C Q)) :
    KillsUnit K C Q α ↔ lam ν α 0 = 0 := by
  constructor
  · intro h
    refine h (Fin 1) (ν 0) ?_
    rw [H.one]
    exact Submodule.subset_span ⟨Equiv.ofUnique Unit (Fin 1), rfl⟩
  · intro h A _ _ x hx
    refine (Submodule.span_le.2 ?_ : GrCooperad.unitSpan K C A
      ≤ LinearMap.ker (ConvOp.toLin (α.1 A))) hx
    rintro _ ⟨e, rfl⟩
    have h1 : SymSpecies.map (R := K) e (GrCooperad.Coaug.one (R := K) (C := C))
        = SymSpecies.map (R := K) ((Equiv.ofUnique Unit (Fin 1)).symm.trans e) (ν 0) := by
      rw [H.one, ← SymSpecies.map_trans, ← Equiv.trans_assoc, Equiv.self_trans_symm,
        Equiv.refl_trans]
    show ConvOp.toLin (α.1 A) (SymSpecies.map (R := K) e
      (GrCooperad.Coaug.one (R := K) (C := C))) = 0
    rw [h1, toLin_map]
    show GrOperad.map (R := K) _ (lam ν α 0) = 0
    rw [h, LinearMap.map_zero]

/-! ## Families pulled back from the signed linear orders -/

omit H [GrCooperad.Coaug K C] in
/-- **The operations of a family pulled back from the signed linear orders**, along a morphism
carrying the generators to the alternating sums: the alternating sums of its operations. -/
theorem lam_appHom (ψ : GrCooperadHom K C (OrdCo K))
    (hψ : ∀ n, ψ.app (Fin (n + 1)) (ν n) = LieDual.alt K n)
    (β : GrOperad.Inv K (ConvOp K (OrdCo K) Q)) (n : ℕ) :
    lam ν (GrOperad.Inv.appHom (ConvOp.preHom ψ) β) n
      = ∑ τ : Equiv.Perm (Fin (n + 1)),
          ((Equiv.Perm.sign τ : ℤ) : K) • GrOperad.map (R := K) τ (famOf β n) := by
  show ConvOp.toLin (β.1 (Fin (n + 1))) (ψ.app (Fin (n + 1)) (ν n)) = _
  rw [hψ, LieDual.alt, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [LinearMap.map_smul, toLin_bs_map]

omit H [GrCooperad.Coaug K C] in
/-- **Every alternating family is the family of operations of an invariant family**, in
characteristic zero. -/
theorem exists_lam [CharZero K] (ψ : GrCooperadHom K C (OrdCo K))
    (hψ : ∀ n, ψ.app (Fin (n + 1)) (ν n) = LieDual.alt K n) (a : ∀ n : ℕ, Q (Fin (n + 1)))
    (ha : ∀ n (τ : Equiv.Perm (Fin (n + 1))),
      GrOperad.map (R := K) τ (a n) = ((Equiv.Perm.sign τ : ℤ) : K) • a n) :
    lam ν (GrOperad.Inv.appHom (ConvOp.preHom ψ)
      (ofFam (K := K) fun n => ((n + 1).factorial : K)⁻¹ • a n)) = a := by
  funext n
  rw [lam_appHom ψ hψ, famOf_ofFam]
  have hterm : ∀ τ : Equiv.Perm (Fin (n + 1)),
      ((Equiv.Perm.sign τ : ℤ) : K) • GrOperad.map (R := K) τ (((n + 1).factorial : K)⁻¹ • a n)
        = ((n + 1).factorial : K)⁻¹ • a n := fun τ => by
    rw [LinearMap.map_smul, ha, smul_smul, smul_smul, mul_comm _ ((n + 1).factorial : K)⁻¹,
      mul_assoc]
    have hs : ((Equiv.Perm.sign τ : ℤ) : K) * ((Equiv.Perm.sign τ : ℤ) : K) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
      simp
    rw [hs, mul_one]
  rw [Finset.sum_congr rfl fun τ _ => hterm τ, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul K, smul_smul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)), one_smul]

end AltGen

end Operad
