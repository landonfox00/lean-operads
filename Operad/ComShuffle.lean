/-
# The coideal of the shuffles in the signed linear orders

Over a field `K` of characteristic zero, **the shuffles span a coideal of the cooperad of signed
linear orders, killed in `Com^¡`** (`ComDual.shCoideal`, `ComDual.rho_eq_zero`).

* **Sets of orders given by constraints** (`ComDual.consSet`): `Φ a b v` prescribes that `a` is
  before `b` iff `v`. The constraints are on the two sides of a splitting of the inputs into two
  nonempty sides, every constraint being between two inputs of the same side
  (`ComDual.Valid`). A composite satisfies the constraints iff its two factors satisfy the
  induced ones (`ComDual.comp_mem_consSet`), and the induced constraints on the inner inputs, or
  else on the outer inputs, are again on two sides (`ComDual.valid_consB`,
  `ComDual.valid_consA`). On two inputs the constraints do not distinguish the two orders
  (`ComDual.mem_consSet_two`).
* **The generators of the coideal** (`ComDual.shGen`) are the restrictions (`ComDual.restr`) of
  the elements of the image of `Lie^¡`, the multiples of the alternating sums, to such sets of
  orders. The decomposition of a restriction is the tensor of two restrictions
  (`ComDual.decompT_restr`), the decomposition of an element of `Lie^¡` being a multiple of the
  tensor of the generators (`LieDual.decomp_eq`); no sign of a permutation is computed
  (`ComDual.decomp_shGen_mem`).
* **The shuffles are killed in `Com^¡`** (`ComDual.rho_eq_zero`): the symmetrization of the
  orders on two inputs kills the generators (`ComDual.jCom_gen_eq_zero`), so it descends to the
  quotient cooperad (`ComDual.genQ`), and the morphism to the cut cooperad factors through the
  quotient by the uniqueness in the universal property of the cut cooperad
  (`FreeGrL.app_eq_of_genCoef`).
-/
import Operad.ComDual

universe u

namespace Operad

open Sym GerBV
open scoped TensorProduct

namespace ComDual

open SymPresComLie OrdCo LieDual

variable {K : Type u} [Field K]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-! ## Sets of orders given by constraints -/

/-- **The linear orders satisfying a set of constraints**: `Φ a b v` prescribes that `a` is
before `b` iff `v` is true. -/
def consSet (Φ : A → A → Bool → Prop) : Set (NOrd A) :=
  {L | ∀ a b v, Φ a b v → (L.1.lt a b ↔ v = true)}

/-- **Constraints on the two sides of a splitting of the inputs** into two nonempty sides: every
constraint is between two inputs of the same side. -/
structure Valid (side : A → Bool) (Φ : A → A → Bool → Prop) : Prop where
  pos : ∃ a, side a = true
  neg : ∃ a, side a = false
  same : ∀ a b v, Φ a b v → side a = side b

/-- The constraints on the inner inputs of a composite. -/
def consB (i : A) (Φ : Without A i ⊕ B → Without A i ⊕ B → Bool → Prop) : B → B → Bool → Prop :=
  fun b b' v => Φ (Sum.inr b) (Sum.inr b') v

/-- The constraints on the outer inputs of a composite, the inner inputs being collapsed to the
place `i`. -/
def consA (i : A) (Φ : Without A i ⊕ B → Without A i ⊕ B → Bool → Prop) : A → A → Bool → Prop :=
  fun a a' v =>
    (∃ (ha : a ≠ i) (ha' : a' ≠ i), Φ (Sum.inl ⟨a, ha⟩) (Sum.inl ⟨a', ha'⟩) v)
      ∨ (a' = i ∧ ∃ (ha : a ≠ i) (b : B), Φ (Sum.inl ⟨a, ha⟩) (Sum.inr b) v)
      ∨ (a = i ∧ ∃ (ha' : a' ≠ i) (b : B), Φ (Sum.inr b) (Sum.inl ⟨a', ha'⟩) v)

/-- **A composite satisfies a set of constraints** iff its two factors satisfy the induced
constraints. -/
lemma comp_mem_consSet (i : A)
    (Φ : Without A i ⊕ B → Without A i ⊕ B → Bool → Prop) (p : NOrd A) (q : NOrd B) :
    SetOperad.comp i p q ∈ consSet Φ ↔ p ∈ consSet (consA i Φ) ∧ q ∈ consSet (consB i Φ) := by
  constructor
  · intro h
    refine ⟨fun a a' v hΦ => ?_, fun b b' v hΦ => h _ _ v hΦ⟩
    rcases hΦ with ⟨ha, ha', hΦ⟩ | ⟨rfl, ha, b, hΦ⟩ | ⟨rfl, ha', b, hΦ⟩
    · exact h _ _ v hΦ
    · exact h _ _ v hΦ
    · exact h _ _ v hΦ
  · rintro ⟨hp, hq⟩ x y v hΦ
    rcases x with a | b <;> rcases y with a' | b'
    · exact hp a.1 a'.1 v (Or.inl ⟨a.2, a'.2, hΦ⟩)
    · exact hp a.1 i v (Or.inr (Or.inl ⟨rfl, a.2, b', hΦ⟩))
    · exact hp i a'.1 v (Or.inr (Or.inr ⟨rfl, a'.2, b, hΦ⟩))
    · exact hq b b' v hΦ

omit [Fintype A] [Fintype B] [DecidableEq B] in
lemma valid_consB (i : A) {side : Without A i ⊕ B → Bool}
    {Φ : Without A i ⊕ B → Without A i ⊕ B → Bool → Prop} (hv : Valid side Φ)
    (h1 : ∃ b : B, side (Sum.inr b) = true) (h2 : ∃ b : B, side (Sum.inr b) = false) :
    Valid (fun b => side (Sum.inr b)) (consB i Φ) :=
  ⟨h1, h2, fun _ _ v h => hv.same _ _ v h⟩

omit [Fintype A] [Fintype B] [DecidableEq B] in
lemma valid_consA (i : A) {side : Without A i ⊕ B → Bool}
    {Φ : Without A i ⊕ B → Without A i ⊕ B → Bool → Prop} (hv : Valid side Φ) (s₀ : Bool)
    (hs : ∀ b : B, side (Sum.inr b) = s₀) :
    Valid (fun a => if h : a = i then s₀ else side (Sum.inl ⟨a, h⟩)) (consA i Φ) := by
  have hi : (fun a => if h : a = i then s₀ else side (Sum.inl ⟨a, h⟩)) i = s₀ := dif_pos rfl
  have hother : ∀ s : Bool, s ≠ s₀ → (∃ x, side x = s) →
      ∃ a, (fun a => if h : a = i then s₀ else side (Sum.inl ⟨a, h⟩)) a = s := by
    rintro s hs' ⟨x, hx⟩
    rcases x with a | b
    · exact ⟨a.1, (dif_neg a.2).trans hx⟩
    · exact absurd ((hs b).symm.trans hx).symm hs'
  have hne : ∀ (a : A) (ha : a ≠ i),
      (fun a => if h : a = i then s₀ else side (Sum.inl ⟨a, h⟩)) a = side (Sum.inl ⟨a, ha⟩) :=
    fun a ha => dif_neg ha
  refine ⟨?_, ?_, ?_⟩
  · cases s₀ with
    | true => exact ⟨i, hi⟩
    | false => exact hother true (by decide) hv.pos
  · cases s₀ with
    | false => exact ⟨i, hi⟩
    | true => exact hother false (by decide) hv.neg
  · intro a a' v hΦ
    rcases hΦ with ⟨ha, ha', hΦ⟩ | ⟨rfl, ha, b, hΦ⟩ | ⟨rfl, ha', b, hΦ⟩
    · exact (hne a ha).trans ((hv.same _ _ v hΦ).trans (hne a' ha').symm)
    · exact (hne a ha).trans ((hv.same _ _ v hΦ).trans ((hs b).trans hi.symm))
    · exact hi.trans ((hs b).symm.trans ((hv.same _ _ v hΦ).trans (hne a' ha').symm))

/-- **On two inputs, the constraints do not distinguish the two orders.** -/
lemma mem_consSet_two (τ : Fin 2 ≃ A) {side : A → Bool} {Φ : A → A → Bool → Prop}
    (hv : Valid side Φ) (L L' : NOrd A) :
    L ∈ consSet Φ ↔ L' ∈ consSet Φ := by
  have h2 : ∀ i j k : Fin 2, i ≠ j → k = i ∨ k = j := by decide
  have key : ∀ a b, side a = side b → a = b := by
    intro a b h
    by_contra hne
    obtain ⟨x, hx⟩ := hv.pos
    obtain ⟨y, hy⟩ := hv.neg
    have hc : ∀ c : A, c = a ∨ c = b := fun c => by
      rcases h2 (τ.symm a) (τ.symm b) (τ.symm c) (fun e => hne (τ.symm.injective e)) with e | e
      · exact Or.inl (τ.symm.injective e)
      · exact Or.inr (τ.symm.injective e)
    rcases hc x with rfl | rfl <;> rcases hc y with rfl | rfl <;> simp_all
  have char : ∀ M : NOrd A, M ∈ consSet Φ ↔ ∀ a v, Φ a a v → v = false := fun M => by
    constructor
    · intro hM a v hΦ
      have := hM a a v hΦ
      cases v with
      | false => rfl
      | true => exact absurd (this.2 rfl) (M.1.irrefl a)
    · intro hM a b v hΦ
      obtain rfl := key a b (hv.same a b v hΦ)
      rw [hM a v hΦ]
      exact ⟨fun h => absurd h (M.1.irrefl a), fun h => absurd h (by decide)⟩
  rw [char, char]

/-! ## Restriction to a set of orders -/

open Classical in
/-- **The restriction of a combination of orders to a set of orders.** -/
noncomputable def restr (T : Set (NOrd A)) (w : NOrd A →₀ K) : NOrd A →₀ K :=
  Finsupp.filter (· ∈ T) w

open Classical in
lemma restr_apply (T : Set (NOrd A)) (w : NOrd A →₀ K) (L : NOrd A) :
    restr T w L = if L ∈ T then w L else 0 := Finsupp.filter_apply _ _ _

/-- **The decomposition of a restriction**, for a set of orders whose composites are those of
two sets of orders, and a combination of orders whose decomposition is the image of a multiple of
a pure tensor. -/
lemma decompT_restr {M N : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (F : M →ₗ[K] (NOrd A →₀ K)) (G : N →ₗ[K] (NOrd B →₀ K)) (i : A)
    (w : NOrd (Without A i ⊕ B) →₀ K) (T : Set (NOrd (Without A i ⊕ B))) (P : Set (NOrd A))
    (Q : Set (NOrd B)) (hT : ∀ p q, SetOperad.comp i p q ∈ T ↔ p ∈ P ∧ q ∈ Q) (c : K) (u : M)
    (v : N) {t : M ⊗[K] N} (ht : t = c • (u ⊗ₜ[K] v))
    (hw : SgnLin.decompT K NOrd.sgnD i w = TensorProduct.map F G t) :
    SgnLin.decompT K NOrd.sgnD i (restr T w) = c • (restr P (F u) ⊗ₜ[K] restr Q (G v)) := by
  subst ht
  refine (tens K (NOrd A) (NOrd B)).injective (Finsupp.ext fun pq => ?_)
  obtain ⟨p, q⟩ := pq
  have h0 := SgnLin.decompT_apply (R := K) (δ := NOrd.sgnD) i w (p, q)
  rw [hw, LinearMap.map_smul, TensorProduct.map_tmul, LinearEquiv.map_smul, Finsupp.smul_apply,
    tens_tmul_apply] at h0
  rw [SgnLin.decompT_apply, LinearEquiv.map_smul, Finsupp.smul_apply, tens_tmul_apply,
    restr_apply, restr_apply, restr_apply]
  by_cases hp : p ∈ P <;> by_cases hq : q ∈ Q
  · rw [if_pos ((hT p q).2 ⟨hp, hq⟩), if_pos hp, if_pos hq]
    exact h0.symm
  · rw [if_neg (fun h => hq ((hT p q).1 h).2), if_neg hq]
    simp
  · rw [if_neg (fun h => hp ((hT p q).1 h).1), if_neg hp]
    simp
  · rw [if_neg (fun h => hp ((hT p q).1 h).1), if_neg hp]
    simp

/-- The relabelling of a restriction. -/
lemma mapL_restr (e : A ≃ B) (w : NOrd A →₀ K) (T : Set (NOrd A)) :
    Lin.mapL K e (restr T w) = restr {L | SetOperad.map e.symm L ∈ T} (Lin.mapL K e w) :=
  Finsupp.ext fun L => by
    rw [Lin.mapL_apply, restr_apply, restr_apply, Lin.mapL_apply]
    rfl

/-- The relabelling of a set of orders given by constraints. -/
lemma map_consSet (e : A ≃ B) (Φ : A → A → Bool → Prop) :
    {L : NOrd B | SetOperad.map e.symm L ∈ consSet Φ}
      = consSet fun b b' v => Φ (e.symm b) (e.symm b') v := by
  ext L
  constructor
  · intro h b b' v hΦ
    have := h _ _ v hΦ
    rw [show (SetOperad.map e.symm L).1 = LinOrd.map e.symm L.1 from rfl, LinOrd.map_lt,
      Equiv.symm_symm, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    exact this
  · intro h a a' v hΦ
    have := h (e a) (e a') v (by
      show Φ (e.symm (e a)) (e.symm (e a')) v
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact hΦ)
    rw [show (SetOperad.map e.symm L).1 = LinOrd.map e.symm L.1 from rfl, LinOrd.map_lt,
      Equiv.symm_symm]
    exact this

/-- A multiple of a pure tensor with a factor in a submodule. -/
lemma smul_tmul_mem_sup {M N : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N]
    [Module K N] (SM : Submodule K M) (SN : Submodule K N) {x : M} {y : N} (c : K)
    (h : x ∈ SM ∨ y ∈ SN) :
    c • (x ⊗ₜ[K] y) ∈ LinearMap.range (LinearMap.lTensor M SN.subtype)
      ⊔ LinearMap.range (LinearMap.rTensor N SM.subtype) := by
  rcases h with h | h
  · exact Submodule.mem_sup_right ⟨c • ((⟨x, h⟩ : SM) ⊗ₜ[K] y), by
      rw [LinearMap.map_smul, LinearMap.rTensor_tmul]
      rfl⟩
  · exact Submodule.mem_sup_left ⟨c • (x ⊗ₜ[K] (⟨y, h⟩ : SN)), by
      rw [LinearMap.map_smul, LinearMap.lTensor_tmul]
      rfl⟩

/-- The parity projections of the signed linear orders are the identity or zero. -/
lemma par_eq (b : Bool) (x : OrdCo K A) :
    GrSpecies.par (R := K) b x = if (Fintype.card A + 1).bodd = b then x else 0 := by
  by_cases h : (Fintype.card A + 1).bodd = b
  · rw [if_pos h]
    exact LinearMap.congr_fun (OrdCo.hom_ext (f := GrSpecies.par (R := K) b)
      (g := LinearMap.id) fun L => by
        rw [OrdCo.par_bs, if_pos h]
        rfl) x
  · rw [if_neg h]
    exact LinearMap.congr_fun (OrdCo.hom_ext (f := GrSpecies.par (R := K) b)
      (g := 0) fun L => by
        rw [OrdCo.par_bs, if_neg h]
        rfl) x

/-! ## The coideal of the shuffles -/

variable [CharZero K]

variable (K) in
/-- **The generators of the coideal of the shuffles**: the restrictions of the elements of the
image of `Lie^¡` to the sets of orders given by constraints on the two sides of a splitting. -/
def shGen (A : Type) [Fintype A] [DecidableEq A] : Set (OrdCo K A) :=
  {y | ∃ (z : Koszul.Dual K (ELie K) (rLie K) A) (side : A → Bool) (Φ : A → A → Bool → Prop),
    Valid side Φ ∧ y = restr (consSet Φ) (show NOrd A →₀ K from (toOrd K).app A z)}

/-- The decomposition of a generator lies in the coideal condition. -/
lemma decomp_shGen_mem (i : A) {y : OrdCo K (Without A i ⊕ B)}
    (hy : y ∈ shGen K (Without A i ⊕ B)) :
    GrCooperad.decomp (R := K) (C := OrdCo K) (B := B) i y
      ∈ LinearMap.range (LinearMap.lTensor (OrdCo K A) (Submodule.span K (shGen K B)).subtype)
        ⊔ LinearMap.range
          (LinearMap.rTensor (OrdCo K B) (Submodule.span K (shGen K A)).subtype) := by
  obtain ⟨z, side, Φ, hv, rfl⟩ := hy
  rcases isEmpty_or_nonempty B with hB | hB
  · have h0 : ∀ t : OrdCo K A ⊗[K] OrdCo K B, t = 0 := fun t => by
      induction t using TensorProduct.induction_on with
      | zero => rfl
      | tmul x w =>
        have hw : w = 0 := (Finsupp.ext fun L => (IsEmpty.false (Classical.choice L.2)).elim :
          (show NOrd B →₀ K from w) = 0)
        rw [hw, TensorProduct.tmul_zero]
      | add s t hs ht => rw [hs, ht, add_zero]
    rw [h0 (GrCooperad.decomp (R := K) (C := OrdCo K) (B := B) i _)]
    exact Submodule.zero_mem _
  · obtain ⟨m, hm⟩ : ∃ m, Fintype.card A = m + 1 :=
      ⟨Fintype.card A - 1, by have := Fintype.card_pos_iff.2 ⟨i⟩; omega⟩
    obtain ⟨l, hl⟩ : ∃ l, Fintype.card B = l + 1 :=
      ⟨Fintype.card B - 1, by have := Fintype.card_pos (α := B); omega⟩
    obtain ⟨f, -⟩ : ∃ f : Fin (m + 1) ≃ A, True := ⟨(Fintype.equivFinOfCardEq hm).symm, trivial⟩
    obtain ⟨g, -⟩ : ∃ g : Fin (l + 1) ≃ B, True := ⟨(Fintype.equivFinOfCardEq hl).symm, trivial⟩
    have h1' := (toOrd K).decomp_app (B := B) i
    have h1 := LinearMap.congr_fun h1' z
    obtain ⟨w, hw⟩ : ∃ w : NOrd (Without A i ⊕ B) →₀ K,
      w = (toOrd K).app (Without A i ⊕ B) z := ⟨_, rfl⟩
    have key := decompT_restr ((toOrd K).app A) ((toOrd K).app B) i w (consSet Φ)
      (consSet (consA i Φ)) (consSet (consB i Φ)) (comp_mem_consSet i Φ) _
      (SymSpecies.map (R := K) f (nu K m)) (SymSpecies.map (R := K) g (nu K l))
      (LieDual.decomp_eq i z f g) (by rw [hw]; exact h1)
    rw [← hw]
    have hmem : (restr (consSet (consA i Φ)) ((toOrd K).app A (SymSpecies.map (R := K) f (nu K m)))
          : OrdCo K A) ∈ Submodule.span K (shGen K A)
        ∨ (restr (consSet (consB i Φ)) ((toOrd K).app B (SymSpecies.map (R := K) g (nu K l)))
          : OrdCo K B) ∈ Submodule.span K (shGen K B) := by
      by_cases hs : (∃ b : B, side (Sum.inr b) = true) ∧ (∃ b : B, side (Sum.inr b) = false)
      · exact Or.inr (Submodule.subset_span ⟨_, _, _, valid_consB i hv hs.1 hs.2, rfl⟩)
      · have hs' : ∃ s₀ : Bool, ∀ b : B, side (Sum.inr b) = s₀ := by
          by_cases h1 : ∃ b : B, side (Sum.inr b) = true
          · refine ⟨true, fun b => ?_⟩
            by_contra hb
            exact hs ⟨h1, b, by simpa using hb⟩
          · refine ⟨false, fun b => ?_⟩
            by_contra hb
            exact h1 ⟨b, by simpa using hb⟩
        obtain ⟨s₀, hs₀⟩ := hs'
        exact Or.inl (Submodule.subset_span ⟨_, _, _, valid_consA i hv s₀ hs₀, rfl⟩)
    exact key ▸ smul_tmul_mem_sup (Submodule.span K (shGen K A)) (Submodule.span K (shGen K B))
      _ hmem

variable (K) in
/-- **The coideal of the shuffles** of the cooperad of signed linear orders. -/
noncomputable def shCoideal : GrCoideal K (OrdCo K) where
  sub A _ _ := Submodule.span K (shGen K A)
  par_mem {A} _ _ b {x} hx := by
    rw [par_eq]
    split_ifs
    · exact hx
    · exact Submodule.zero_mem _
  map_mem {A B} _ _ _ _ e {x} hx := by
    refine (Submodule.span_le.2 ?_ : Submodule.span K (shGen K A)
      ≤ (Submodule.span K (shGen K B)).comap (SymSpecies.map (R := K) (V := OrdCo K) e)) hx
    rintro _ ⟨z, side, Φ, hv, rfl⟩
    refine Submodule.subset_span ⟨SymSpecies.map (R := K) e z, fun b => side (e.symm b),
      fun b b' v => Φ (e.symm b) (e.symm b') v, ⟨?_, ?_, fun b b' v h => hv.same _ _ v h⟩, ?_⟩
    · obtain ⟨a, ha⟩ := hv.pos
      exact ⟨e a, by rw [Equiv.symm_apply_apply]; exact ha⟩
    · obtain ⟨a, ha⟩ := hv.neg
      exact ⟨e a, by rw [Equiv.symm_apply_apply]; exact ha⟩
    · show Lin.mapL K e (restr (consSet Φ) (show NOrd A →₀ K from (toOrd K).app A z)) = _
      rw [mapL_restr, map_consSet, (toOrd K).app_map]
      rfl
  counit_mem {x} hx := by
    have hempty : shGen K Unit = ∅ := Set.eq_empty_of_forall_notMem (by
      rintro _ ⟨z, side, Φ, hv, -⟩
      obtain ⟨a, ha⟩ := hv.pos
      obtain ⟨a', ha'⟩ := hv.neg
      cases a
      cases a'
      rw [ha] at ha'
      exact absurd ha' (by decide))
    rw [hempty, Submodule.span_empty, Submodule.mem_bot] at hx
    rw [hx, map_zero]
  decomp_mem {A B} _ _ _ _ i {x} hx := by
    refine (Submodule.span_le.2 ?_ : Submodule.span K (shGen K (Without A i ⊕ B))
      ≤ (LinearMap.range (LinearMap.lTensor (OrdCo K A) (Submodule.span K (shGen K B)).subtype)
        ⊔ LinearMap.range (LinearMap.rTensor (OrdCo K B)
          (Submodule.span K (shGen K A)).subtype)).comap
            (GrCooperad.decomp (R := K) (C := OrdCo K) (B := B) i)) hx
    exact fun y hy => decomp_shGen_mem i hy

/-! ## The shuffles are killed in `Com^¡` -/

/-- **The symmetrization of the orders on two inputs kills the shuffles.** -/
theorem jCom_gen_eq_zero {y : OrdCo K A} (hy : y ∈ (shCoideal K).sub A) :
    (jCom K).app A ((OrdCo.gen K).app A y) = 0 := by
  refine (Submodule.span_le.2 ?_ : Submodule.span K (shGen K A)
    ≤ LinearMap.ker ((jCom K).app A ∘ₗ (OrdCo.gen K).app A)) hy
  rintro _ ⟨z, side, Φ, hv, rfl⟩
  refine Subtype.ext (funext fun e => ?_)
  show restr (consSet Φ) (show NOrd A →₀ K from (toOrd K).app A z) (OrdCo.ord2 e.symm)
    + restr (consSet Φ) (show NOrd A →₀ K from (toOrd K).app A z)
      (OrdCo.ord2 ((Equiv.swap 0 1).trans e.symm)) = 0
  have h1 := coef_ord2_swap z e.symm
  have h2 := mem_consSet_two e.symm hv (OrdCo.ord2 e.symm)
    (OrdCo.ord2 ((Equiv.swap 0 1).trans e.symm))
  rw [restr_apply, restr_apply]
  by_cases h : OrdCo.ord2 e.symm ∈ consSet Φ
  · rw [if_pos h, if_pos (h2.1 h)]
    exact add_eq_zero_iff_eq_neg'.2 h1
  · rw [if_neg h, if_neg fun h' => h (h2.2 h'), add_zero]

omit [CharZero K] in
variable (K) in
/-- The shifted generators of `Com` have no vectors on at most one input. -/
lemma hredC (B : Type) [Fintype B] [DecidableEq B] (hB : Fintype.card B ≤ 1)
    (v : GrSpecies.Shift (ECom K) K B) : v = 0 :=
  (Subtype.ext (funext fun e => absurd ((Fintype.card_congr e).trans (Fintype.card_fin 2))
    (by omega)) : (show ECom K B from v) = 0)

variable (K) in
/-- The symmetrization of the orders on two inputs, on the quotient by the shuffles. -/
noncomputable def genQ : GrSpeciesHom K (shCoideal K).Quot (GrSpecies.Shift (ECom K) K) where
  app A _ _ := ((shCoideal K).sub A).liftQ
    ((Koszul.shiftHom (jCom K)).app A ∘ₗ (OrdCo.gen K).app A)
    (fun _ hy => LinearMap.mem_ker.2 (jCom_gen_eq_zero hy))
  app_map {A B} _ _ _ _ e x := by
    obtain ⟨y, rfl⟩ := (shCoideal K).proj_surjective A x
    show (Koszul.shiftHom (jCom K)).app B ((OrdCo.gen K).app B (SymSpecies.map (R := K) e y))
      = SymSpecies.map (R := K) e ((Koszul.shiftHom (jCom K)).app A ((OrdCo.gen K).app A y))
    rw [(OrdCo.gen K).app_map, (Koszul.shiftHom (jCom K)).app_map]
  app_par {A} _ _ b x := by
    obtain ⟨y, rfl⟩ := (shCoideal K).proj_surjective A x
    show (Koszul.shiftHom (jCom K)).app A ((OrdCo.gen K).app A (GrSpecies.par (R := K) b y))
      = GrSpecies.par (R := K) b ((Koszul.shiftHom (jCom K)).app A ((OrdCo.gen K).app A y))
    rw [(OrdCo.gen K).app_par, (Koszul.shiftHom (jCom K)).app_par]

/-- **The shuffles are killed in `Com^¡`**: the morphism from the signed linear orders factors
through the quotient by the coideal of the shuffles, by the universal property of the cut
cooperad. -/
theorem rho_eq_zero {y : OrdCo K A} (hy : y ∈ (shCoideal K).sub A) : (rho K).app A y = 0 := by
  obtain ⟨fbar, hfbar⟩ : ∃ fbar : GrCooperadHom K (shCoideal K).Quot (Koszul.Cut K (ECom K)),
      fbar = (FreeGrL.cofreeHomEquiv (R := K) (C := (shCoideal K).Quot)
        (V := GrSpecies.Shift (ECom K) K) (hredC K)).symm (genQ K) := ⟨_, rfl⟩
  have hgen : ∀ (B : Type) [Fintype B] [DecidableEq B] (x : OrdCo K B),
      FreeGrL.genCoef K (GrSpecies.Shift (ECom K) K) B
          (((Koszul.dualSub K (ECom K) (rCom K)).inclHom.comp (rho K)).app B x)
        = FreeGrL.genCoef K (GrSpecies.Shift (ECom K) K) B
          ((fbar.comp (shCoideal K).projHom).app B x) := by
    intro B _ _ x
    have h2 := (FreeGrL.cofreeHomEquiv (R := K) (C := (shCoideal K).Quot)
      (V := GrSpecies.Shift (ECom K) K) (hredC K)).apply_symm_apply (genQ K)
    rw [← hfbar] at h2
    have h3 := congrArg (fun φ : GrSpeciesHom K (shCoideal K).Quot (GrSpecies.Shift (ECom K) K) =>
      φ.app B ((shCoideal K).proj B x)) h2
    exact (genCoef_rho K x).trans h3.symm
  have h := FreeGrL.app_eq_of_genCoef (hredC K) hgen A y
  have h0 : (fbar.comp (shCoideal K).projHom).app A y = 0 := by
    show fbar.app A ((shCoideal K).proj A y) = 0
    rw [((shCoideal K).proj_eq_zero_iff y).2 hy, map_zero]
  exact (Koszul.dualSub K (ECom K) (rCom K)).incl_injective A
    ((h.trans h0).trans (map_zero _).symm)

end ComDual

end Operad
