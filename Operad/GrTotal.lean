/-
# Total composition in a graded operad

The homogeneous operations of a graded operad `P` with sign data form a set operad
(`SgnOp.instSetOperad`), so May's total composition applies to them. With the sign data of a
corolla — an order `L` of the inputs and no parity after them — the total composite of `m` with
operations `y a` inserted at its inputs is the Koszul composite `m ∘ (y_a)_a` read in the order
`L`: **it does not depend on the sign data of the inserted operations beyond their parities**
(`SgnOp.total_op_congr`), it is multilinear (`SgnOp.total_op_add_left`,
`SgnOp.total_op_update_add`), and **changing the order `L` to `L'` costs the Koszul sign of the
reordering** (`SgnOp.total_op_reorder`).
-/
import Operad.MayClass
import Operad.FreeGrRoot

universe u v w

namespace Operad

open Function Sym GerBV May

/-! ## Set operad morphisms commute with filling -/

namespace May

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {T : (A : Type) → [Fintype A] → [DecidableEq A] → Type w} [SetOperad T]
  (φ : SetOperadHom S T)
  {A : Type} [Fintype A] [DecidableEq A] {B : A → Type} [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]

lemma app_fill (x : S A) (y : (a : A) → S (B a)) (l : List A) (hl : l.Nodup) :
    φ.app _ (fill x y l hl) = fill (φ.app A x) (fun a => φ.app _ (y a)) l hl := by
  induction l with
  | nil => rw [fill_nil, fill_nil, φ.app_map]
  | cons a l ih => rw [fill_cons, fill_cons, φ.app_map, φ.app_comp, ih]

lemma app_total (x : S A) (y : (a : A) → S (B a)) :
    φ.app _ (SetOperad.total x y) = SetOperad.total (φ.app A x) (fun a => φ.app _ (y a)) := by
  rw [SetOperad.total, SetOperad.total, φ.app_map, app_fill]

end May

/-! ## The sign data of a filling -/

namespace SgnData

variable {A : Type} [Fintype A] [DecidableEq A] {B : A → Type} [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]

/-- The parity seen after the input `a` from the inputs filled in `l`: those after `a` in `L`. -/
noncomputable def aftL (L : LinOrd A) (c : A → Bool) (a : A) : List A → Bool
  | [] => false
  | a' :: l => xor (GrComposite.ltB L a a' && c a') (aftL L c a l)

/-- **The order of a filling** between two inputs not filled yet. -/
lemma fill_ord_inl (D : SgnData A) (d : (a : A) → SgnData (B a)) (l : List A) (hl : l.Nodup)
    (a b : {a : A // a ∉ l}) :
    (fill (S := SgnD) D d l hl).ord.lt (Sum.inl a) (Sum.inl b) ↔ D.ord.lt a.1 b.1 := by
  induction l with
  | nil => exact Iff.rfl
  | cons a₀ l ih =>
    exact ih (List.nodup_cons.1 hl).2 ⟨a.1, fun h => a.2 (List.mem_cons_of_mem a₀ h)⟩
      ⟨b.1, fun h => b.2 (List.mem_cons_of_mem a₀ h)⟩

/-- **The order of a filling** between an input of an inserted operation and an input not filled
yet. -/
lemma fill_ord_inr_inl (D : SgnData A) (d : (a : A) → SgnData (B a)) (l : List A)
    (hl : l.Nodup) (a : {a : A // a ∈ l}) (b : B a.1) (a' : {a : A // a ∉ l}) :
    (fill (S := SgnD) D d l hl).ord.lt (Sum.inr ⟨a, b⟩) (Sum.inl a') ↔ D.ord.lt a.1 a'.1 := by
  induction l with
  | nil => exact absurd a.2 (List.not_mem_nil)
  | cons a₀ l ih =>
    obtain ⟨ha₀, hl'⟩ := List.nodup_cons.1 hl
    have ha' : a'.1 ∉ l := fun h => a'.2 (List.mem_cons_of_mem a₀ h)
    by_cases h : a.1 = a₀
    · obtain ⟨a, ha⟩ := a
      simp only at h
      subst h
      show (LinOrd.comp _ _ _).lt _ _ ↔ _
      simp only [stepEquiv, Equiv.coe_fn_symm_mk, dif_pos, LinOrd.comp_lt,
        LinOrd.compLt_inr_inl]
      exact fill_ord_inl D d l hl' _ ⟨a'.1, ha'⟩
    · have hal : a.1 ∈ l := (List.mem_cons.1 a.2).resolve_left h
      show (LinOrd.comp _ _ _).lt _ _ ↔ _
      simp only [stepEquiv, Equiv.coe_fn_symm_mk, dif_neg h, LinOrd.comp_lt]
      exact ih hl' ⟨a.1, hal⟩ b ⟨a'.1, ha'⟩

/-- **The parity after an input not filled yet**: the parities of the operations inserted after
it, in addition to its own. -/
lemma fill_aft_inl (D : SgnData A) (d : (a : A) → SgnData (B a)) (l : List A) (hl : l.Nodup)
    (a : {a : A // a ∉ l}) :
    (fill (S := SgnD) D d l hl).aft (Sum.inl a)
      = xor (D.aft a.1) (aftL D.ord (fun a => (d a).tot) a.1 l) := by
  induction l with
  | nil => exact (Bool.xor_false _).symm
  | cons a₀ l ih =>
    obtain ⟨ha₀, hl'⟩ := List.nodup_cons.1 hl
    have ha : a.1 ∉ l := fun h => a.2 (List.mem_cons_of_mem a₀ h)
    have hne : a.1 ≠ a₀ := fun h => a.2 (by rw [h]; exact List.mem_cons_self)
    rw [fill_cons]
    show (SgnData.map _ (SgnData.comp _ _ _)).aft _ = _
    rw [SgnData.map_aft, show (stepEquiv (B := B) a₀ l ha₀).symm (Sum.inl a)
        = Sum.inl ⟨Sum.inl ⟨a.1, ha⟩, fun h => hne (congrArg Subtype.val (Sum.inl_injective h))⟩
        from rfl, SgnData.comp_aft_inl, ih hl' ⟨a.1, ha⟩, aftL]
    have hord := fill_ord_inl D d l hl' ⟨a.1, ha⟩ ⟨a₀, ha₀⟩
    by_cases h : D.ord.lt a.1 a₀
    · rw [if_pos (hord.2 h), (GrComposite.ltB_eq_true _ _ _).2 h, Bool.true_and]
      cases D.aft a.1 <;> cases (d a₀).tot <;> cases aftL D.ord (fun a => (d a).tot) a.1 l <;> rfl
    · rw [if_neg (fun h' => h (hord.1 h')),
        show GrComposite.ltB D.ord a.1 a₀ = false from Bool.eq_false_iff.2 fun h' =>
          h ((GrComposite.ltB_eq_true _ _ _).1 h'), Bool.false_and, Bool.false_xor]

/-- The sign of filling the inputs in `l` with the outer order `L` rather than `L'`. -/
noncomputable def rL (L L' : LinOrd A) (c : A → Bool) : List A → Bool
  | [] => false
  | a :: l => xor (rL L L' c l) (c a && xor (aftL L c a l) (aftL L' c a l))

omit [Fintype A] [DecidableEq A] in
lemma lt_swap_iff (L : LinOrd A) {a b : A} (h : a ≠ b) : L.lt b a ↔ ¬ L.lt a b :=
  ⟨fun h' h'' => GrEnd.lt_asymm L h'' h', fun h' => (L.total a b h).resolve_left h'⟩

omit [Fintype A] in
lemma sigma_aftL (R : Type u) [CommRing R] (L L' : LinOrd A) (c : A → Bool) (t : Bool) (a : A)
    (l : List A) (hl : l.Nodup) :
    σ R (t && xor (aftL L c a l) (aftL L' c a l))
      = ∏ b ∈ l.toFinset, σ R (t && c b && xor (GrComposite.ltB L a b) (GrComposite.ltB L' a b))
    := by
  induction l with
  | nil => simp [aftL]
  | cons b l ih =>
    obtain ⟨hb, hl'⟩ := List.nodup_cons.1 hl
    rw [List.toFinset_cons, Finset.prod_insert (by simpa using hb), ← ih hl', ← σ_xor, aftL,
      aftL]
    congr 1
    cases t <;> cases c b <;> cases GrComposite.ltB L a b <;> cases GrComposite.ltB L' a b <;>
      cases aftL L c a l <;> cases aftL L' c a l <;> rfl

omit [Fintype A] in
lemma prod_insert_sq {M : Type*} [CommMonoid M] (f : A → A → M) {a₀ : A} {F : Finset A}
    (h : a₀ ∉ F) (h0 : f a₀ a₀ = 1) :
    ∏ a ∈ insert a₀ F, ∏ b ∈ insert a₀ F, f a b
      = (∏ a ∈ F, ∏ b ∈ F, f a b) * ∏ b ∈ F, (f a₀ b * f b a₀) := by
  rw [Finset.prod_insert h, Finset.prod_insert h, h0, one_mul]
  simp only [Finset.prod_insert h, Finset.prod_mul_distrib]
  ac_rfl

omit [Fintype A] in
open Classical in
/-- **The sign of filling in another outer order is the Koszul sign of the reordering.** -/
lemma sigma_rL (R : Type u) [CommRing R] (L L' : LinOrd A) (c : A → Bool) (l : List A)
    (hl : l.Nodup) :
    σ R (rL L L' c l) = ∏ a ∈ l.toFinset, ∏ b ∈ l.toFinset,
      if L.lt a b ∧ L'.lt b a then σ R (c a && c b) else 1 := by
  induction l with
  | nil => simp [rL]
  | cons a₀ l ih =>
    obtain ⟨ha₀, hl'⟩ := List.nodup_cons.1 hl
    have hF : a₀ ∉ l.toFinset := by simpa using ha₀
    rw [rL, σ_xor, ih hl', sigma_aftL R L L' c (c a₀) a₀ l hl', List.toFinset_cons,
      prod_insert_sq _ hF (if_neg fun h => L.irrefl _ h.1)]
    congr 1
    refine Finset.prod_congr rfl fun b hb => ?_
    have hne : a₀ ≠ b := fun h => hF (h ▸ hb)
    have e1 := lt_swap_iff L hne
    have e2 := lt_swap_iff L' hne
    by_cases h1 : L.lt a₀ b <;> by_cases h2 : L'.lt a₀ b
    · rw [if_neg (fun h => e2.1 h.2 h2), if_neg (fun h => e1.1 h.1 h1),
        (GrComposite.ltB_eq_true _ _ _).2 h1, (GrComposite.ltB_eq_true _ _ _).2 h2]
      simp
    · rw [if_pos ⟨h1, e2.2 h2⟩, if_neg (fun h => e1.1 h.1 h1),
        (GrComposite.ltB_eq_true _ _ _).2 h1,
        Bool.eq_false_iff.2 fun h => h2 ((GrComposite.ltB_eq_true _ _ _).1 h)]
      simp
    · rw [if_neg (fun h => h1 h.1), if_pos ⟨e1.2 h1, h2⟩,
        Bool.eq_false_iff.2 fun h => h1 ((GrComposite.ltB_eq_true _ _ _).1 h),
        (GrComposite.ltB_eq_true _ _ _).2 h2]
      simp [Bool.and_comm]
    · rw [if_neg (fun h => h1 h.1), if_neg (fun h => h2 h.2),
        Bool.eq_false_iff.2 fun h => h1 ((GrComposite.ltB_eq_true _ _ _).1 h),
        Bool.eq_false_iff.2 fun h => h2 ((GrComposite.ltB_eq_true _ _ _).1 h)]
      simp

/-- **The parity after an input of an inserted operation**: its own in that operation, that of
its owner, and the parities of the operations inserted after its owner. -/
lemma fill_aft_inr (D : SgnData A) (d : (a : A) → SgnData (B a)) (l : List A) (hl : l.Nodup)
    (a : {a : A // a ∈ l}) (b : B a.1) :
    (fill (S := SgnD) D d l hl).aft (Sum.inr ⟨a, b⟩)
      = xor ((d a.1).aft b) (xor (D.aft a.1) (aftL D.ord (fun a => (d a).tot) a.1 l)) := by
  induction l with
  | nil => exact absurd a.2 List.not_mem_nil
  | cons a₀ l ih =>
    obtain ⟨ha₀, hl'⟩ := List.nodup_cons.1 hl
    rw [fill_cons]
    show (SgnData.map _ (SgnData.comp _ _ _)).aft _ = _
    rw [SgnData.map_aft]
    by_cases h : a.1 = a₀
    · obtain ⟨a, ha⟩ := a
      simp only at h
      subst h
      rw [show (stepEquiv (B := B) a l ha₀).symm (Sum.inr ⟨⟨a, ha⟩, b⟩) = Sum.inr b from by
          simp [stepEquiv],
        SgnData.comp_aft_inr, fill_aft_inl D d l hl' ⟨a, ha₀⟩, aftL, GrComposite.ltB_self,
        Bool.false_and, Bool.false_xor]
    · have hal : a.1 ∈ l := (List.mem_cons.1 a.2).resolve_left h
      rw [show (stepEquiv (B := B) a₀ l ha₀).symm (Sum.inr ⟨a, b⟩)
          = Sum.inl ⟨Sum.inr ⟨⟨a.1, hal⟩, b⟩, Sum.inr_ne_inl⟩ from by
          simp [stepEquiv, h],
        SgnData.comp_aft_inl, ih hl' ⟨a.1, hal⟩ b, aftL]
      have hord := fill_ord_inr_inl D d l hl' ⟨a.1, hal⟩ b ⟨a₀, ha₀⟩
      by_cases h' : D.ord.lt a.1 a₀
      · rw [if_pos (hord.2 h'), (GrComposite.ltB_eq_true _ _ _).2 h', Bool.true_and]
        cases (d a.1).aft b <;> cases D.aft a.1 <;> cases (d a₀).tot <;>
          cases aftL D.ord (fun a => (d a).tot) a.1 l <;> rfl
      · rw [if_neg (fun h'' => h' (hord.1 h'')),
          show GrComposite.ltB D.ord a.1 a₀ = false from Bool.eq_false_iff.2 fun h'' =>
            h' ((GrComposite.ltB_eq_true _ _ _).1 h''), Bool.false_and, Bool.false_xor]

omit [Fintype A] in
lemma sigma_aftL₁ (R : Type u) [CommRing R] (L : LinOrd A) (c : A → Bool) (t : Bool) (a : A)
    (l : List A) (hl : l.Nodup) :
    σ R (t && aftL L c a l) = ∏ b ∈ l.toFinset, σ R (t && GrComposite.ltB L a b && c b) := by
  induction l with
  | nil => simp [aftL]
  | cons b l ih =>
    obtain ⟨hb, hl'⟩ := List.nodup_cons.1 hl
    rw [List.toFinset_cons, Finset.prod_insert (by simpa using hb), ← ih hl', ← σ_xor, aftL]
    congr 1
    cases t <;> cases c b <;> cases GrComposite.ltB L a b <;> cases aftL L c a l <;> rfl

end SgnData

/-! ## Fillings of homogeneous operations with sign data -/

namespace SgnOp

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {A : Type} [Fintype A] [DecidableEq A] {B : A → Type} [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]

@[simp] lemma map_op {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) (p : SgnOp R P X) :
    (SetOperad.map e p).op = GrOperad.map (R := R) e p.op := rfl

@[simp] lemma map_dat {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) (p : SgnOp R P X) : (SetOperad.map e p).dat = SgnData.map e p.dat := rfl

@[simp] lemma comp_op {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (i : X) (p : SgnOp R P X) (p' : SgnOp R P Y) :
    (SetOperad.comp i p p').op
      = σ R (SgnData.sgn i p.dat p'.dat) • GrOperad.comp (R := R) i p.op p'.op := rfl

/-- **The sign data of a filling** is the filling of the sign data. -/
lemma fill_dat (x : SgnOp R P A) (y : (a : A) → SgnOp R P (B a)) (l : List A) (hl : l.Nodup) :
    (fill x y l hl).dat = fill (S := SgnD) x.dat (fun a => (y a).dat) l hl :=
  app_fill (SgnOp.proj R P) x y l hl

/-- **A filling only depends on the parities of the sign data of the inserted operations.** -/
lemma fill_op_congr (x : SgnOp R P A) {y y' : (a : A) → SgnOp R P (B a)} (l : List A)
    (hl : l.Nodup) (hop : ∀ a, (y a).op = (y' a).op) (htot : ∀ a, (y a).dat.tot = (y' a).dat.tot) :
    (fill x y l hl).op = (fill x y' l hl).op := by
  induction l with
  | nil => rfl
  | cons a₀ l ih =>
    obtain ⟨ha₀, hl'⟩ := List.nodup_cons.1 hl
    rw [fill_cons, fill_cons, map_op, map_op, comp_op, comp_op, ih hl', hop a₀]
    congr 3
    simp only [SgnData.sgn, fill_dat, SgnData.fill_aft_inl, htot]

/-- **A filling is linear in the outer operation**, for fixed sign data. -/
lemma fill_op_lin {x x₁ x₂ : SgnOp R P A} (c₁ c₂ : R) (h₁ : x₁.dat = x.dat) (h₂ : x₂.dat = x.dat)
    (h : x.op = c₁ • x₁.op + c₂ • x₂.op) (y : (a : A) → SgnOp R P (B a)) (l : List A)
    (hl : l.Nodup) :
    (fill x y l hl).op = c₁ • (fill x₁ y l hl).op + c₂ • (fill x₂ y l hl).op := by
  induction l with
  | nil =>
    simp only [fill_nil, map_op, h, map_add, map_smul]
  | cons a₀ l ih =>
    obtain ⟨ha₀, hl'⟩ := List.nodup_cons.1 hl
    have hd₁ : (fill x₁ y l hl').dat = (fill x y l hl').dat := by rw [fill_dat, fill_dat, h₁]
    have hd₂ : (fill x₂ y l hl').dat = (fill x y l hl').dat := by rw [fill_dat, fill_dat, h₂]
    rw [fill_cons, fill_cons, fill_cons, map_op, map_op, map_op, comp_op, comp_op, comp_op,
      ih hl', hd₁, hd₂]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_add]
    rw [smul_comm (σ R _) c₁, smul_comm (σ R _) c₂]

/-- **Filling in another outer order** costs the sign `rL`. -/
lemma fill_op_reorder {x x' : SgnOp R P A} (hop : x.op = x'.op) (haft : x.dat.aft = x'.dat.aft)
    (y : (a : A) → SgnOp R P (B a)) (l : List A) (hl : l.Nodup) :
    (fill x y l hl).op
      = σ R (SgnData.rL x.dat.ord x'.dat.ord (fun a => (y a).dat.tot) l) • (fill x' y l hl).op := by
  induction l with
  | nil => simp only [fill_nil, map_op, hop, SgnData.rL, σ_false, one_smul]
  | cons a₀ l ih =>
    obtain ⟨ha₀, hl'⟩ := List.nodup_cons.1 hl
    rw [fill_cons, fill_cons, map_op, map_op, comp_op, comp_op, ih hl',
      map_smul (GrOperad.comp (R := R) _), LinearMap.smul_apply, map_smul, map_smul, map_smul,
      smul_smul, smul_smul]
    congr 1
    simp only [SgnData.sgn, fill_dat, SgnData.fill_aft_inl, haft, SgnData.rL, ← σ_xor]
    congr 1
    cases (y a₀).dat.tot <;> cases x'.dat.aft a₀ <;>
      cases SgnData.aftL x.dat.ord (fun a => (y a).dat.tot) a₀ l <;>
      cases SgnData.aftL x'.dat.ord (fun a => (y a).dat.tot) a₀ l <;>
      cases SgnData.rL x.dat.ord x'.dat.ord (fun a => (y a).dat.tot) l <;> rfl

/-! ### Total composition -/

lemma total_op_eq_fill (x : SgnOp R P A) (y : (a : A) → SgnOp R P (B a)) (l : List A)
    (hl : l.Nodup) (hc : ∀ a, a ∈ l) :
    (SetOperad.total x y).op = GrOperad.map (R := R) (finalEquiv B l hc) (fill x y l hl).op := by
  rw [SetOperad.total_eq_fill x y l hl hc, map_op]

/-- **Total composition only depends on the parities of the sign data of the inserted
operations.** -/
lemma total_op_congr (x : SgnOp R P A) {y y' : (a : A) → SgnOp R P (B a)}
    (hop : ∀ a, (y a).op = (y' a).op) (htot : ∀ a, (y a).dat.tot = (y' a).dat.tot) :
    (SetOperad.total x y).op = (SetOperad.total x y').op := by
  rw [SetOperad.total, SetOperad.total, map_op, map_op,
    fill_op_congr x _ (Finset.nodup_toList _) hop htot]

/-- **Total composition is linear in the outer operation**, for fixed sign data. -/
lemma total_op_lin {x x₁ x₂ : SgnOp R P A} (c₁ c₂ : R) (h₁ : x₁.dat = x.dat)
    (h₂ : x₂.dat = x.dat) (h : x.op = c₁ • x₁.op + c₂ • x₂.op) (y : (a : A) → SgnOp R P (B a)) :
    (SetOperad.total x y).op = c₁ • (SetOperad.total x₁ y).op + c₂ • (SetOperad.total x₂ y).op := by
  rw [SetOperad.total, SetOperad.total, SetOperad.total, map_op, map_op, map_op,
    fill_op_lin c₁ c₂ h₁ h₂ h, map_add, map_smul, map_smul]

/-- **Total composition is linear in each inserted operation**, for fixed sign data. -/
lemma total_op_update (x : SgnOp R P A) (y : (a : A) → SgnOp R P (B a)) (a : A)
    {v v₁ v₂ : SgnOp R P (B a)} (c₁ c₂ : R) (h₁ : v₁.dat = v.dat) (h₂ : v₂.dat = v.dat)
    (h : v.op = c₁ • v₁.op + c₂ • v₂.op) :
    (SetOperad.total x (update y a v)).op
      = c₁ • (SetOperad.total x (update y a v₁)).op
        + c₂ • (SetOperad.total x (update y a v₂)).op := by
  have hf : ∀ w : SgnOp R P (B a), fill x (update y a w) (others a)
      (List.nodup_cons.1 (others_nodup a)).2 = fill x y (others a)
        (List.nodup_cons.1 (others_nodup a)).2 := fun w =>
    fill_congr _ _ _ fun b hb => by
      rw [Function.update_of_ne]
      rintro rfl
      exact (List.nodup_cons.1 (others_nodup b)).1 hb
  rw [total_eq_comp, total_eq_comp, total_eq_comp, map_op, map_op, map_op, comp_op, comp_op,
    comp_op, hf, hf, hf, update_self, update_self, update_self, h₁, h₂, h]
  simp only [map_add, map_smul, smul_add]
  rw [smul_comm (σ R _) c₁, smul_comm (σ R _) c₂]

/-- **Total composition in another outer order** costs the Koszul sign of the reordering. -/
lemma total_op_reorder {x x' : SgnOp R P A} (hop : x.op = x'.op) (haft : x.dat.aft = x'.dat.aft)
    (y : (a : A) → SgnOp R P (B a)) :
    (SetOperad.total x y).op
      = GrEnd.rsg R x.dat.ord x'.dat.ord (fun a => (y a).dat.tot) • (SetOperad.total x' y).op := by
  rw [SetOperad.total, SetOperad.total, map_op, map_op,
    fill_op_reorder hop haft y _ (Finset.nodup_toList _), map_smul,
    SgnData.sigma_rL R _ _ _ _ (Finset.nodup_toList _), Finset.toList_toFinset]
  rfl

/-- **A filling with rescaled inserted operations** is rescaled by the product of the scalars. -/
lemma fill_op_smul (x : SgnOp R P A) {y y' : (a : A) → SgnOp R P (B a)} (s : A → R)
    (hd : ∀ a, (y a).dat = (y' a).dat) (hop : ∀ a, (y a).op = s a • (y' a).op) (l : List A)
    (hl : l.Nodup) :
    (fill x y l hl).op = (l.map s).prod • (fill x y' l hl).op := by
  induction l with
  | nil => simp only [fill_nil, List.map_nil, List.prod_nil, one_smul]
  | cons a₀ l ih =>
    obtain ⟨ha₀, hl'⟩ := List.nodup_cons.1 hl
    have hdat : (fill x y l hl').dat = (fill x y' l hl').dat := by
      rw [fill_dat, fill_dat, show (fun a => (y a).dat) = fun a => (y' a).dat from funext hd]
    rw [fill_cons, fill_cons, map_op, map_op, comp_op, comp_op, ih hl', hop a₀, hdat, hd a₀,
      map_smul (GrOperad.comp (R := R) _), LinearMap.smul_apply, map_smul, map_smul, map_smul,
      map_smul, smul_comm (σ R _), smul_smul, List.map_cons, List.prod_cons, mul_comm (s a₀),
      map_smul, smul_smul, smul_smul]
    ring_nf

/-- **A total composite with rescaled inserted operations** is rescaled by the product of the
scalars. -/
lemma total_op_smul (x : SgnOp R P A) {y y' : (a : A) → SgnOp R P (B a)} (s : A → R)
    (hd : ∀ a, (y a).dat = (y' a).dat) (hop : ∀ a, (y a).op = s a • (y' a).op) :
    (SetOperad.total x y).op = (∏ a, s a) • (SetOperad.total x y').op := by
  rw [SetOperad.total, SetOperad.total, map_op, map_op,
    fill_op_smul x s hd hop _ (Finset.nodup_toList _), map_smul, Finset.prod_map_toList]

/-- **The parity after an input of a total composite.** -/
lemma total_aft (x : SgnOp R P A) (y : (a : A) → SgnOp R P (B a)) (a : A) (b : B a) :
    (SetOperad.total x y).dat.aft ⟨a, b⟩
      = xor ((y a).dat.aft b) (xor (x.dat.aft a) (SgnData.aftL x.dat.ord (fun a => (y a).dat.tot) a
          (Finset.univ : Finset A).toList)) := by
  rw [SetOperad.total, map_dat, SgnData.map_aft, fill_dat]
  exact SgnData.fill_aft_inr _ _ _ _ ⟨a, Finset.mem_toList.2 (Finset.mem_univ a)⟩ b

/-! ### Corollas -/

/-- The sign data of a corolla: an order of the inputs, no parity after them. -/
def corData (L : LinOrd A) (p : Bool) : SgnData A := ⟨L, fun _ => false, p⟩

/-- **The part of parity `p` of an operation, with the sign data of a corolla.** -/
noncomputable def cor (L : LinOrd A) (p : Bool) (x : P A) : SgnOp R P A :=
  mk (GrOperad.par (R := R) p x) (corData L p) (GrOperad.par_par_self (R := R) p x)

@[simp] lemma cor_op (L : LinOrd A) (p : Bool) (x : P A) :
    (cor (R := R) L p x).op = GrOperad.par (R := R) p x := rfl

@[simp] lemma cor_dat (L : LinOrd A) (p : Bool) (x : P A) : (cor (R := R) L p x).dat = corData L p :=
  rfl

lemma total_cor_lin (L : LinOrd A) (p : Bool) (c₁ c₂ : R) (x₁ x₂ : P A)
    (y : (a : A) → SgnOp R P (B a)) :
    (SetOperad.total (cor L p (c₁ • x₁ + c₂ • x₂)) y).op
      = c₁ • (SetOperad.total (cor L p x₁) y).op + c₂ • (SetOperad.total (cor L p x₂) y).op :=
  total_op_lin (x := cor L p (c₁ • x₁ + c₂ • x₂)) (x₁ := cor L p x₁) (x₂ := cor L p x₂) c₁ c₂ rfl
    rfl (by simp only [cor_op, map_add, map_smul]) y

lemma total_cor_update (x : SgnOp R P A) (L : ∀ a, LinOrd (B a)) (c : A → Bool)
    (y : (a : A) → P (B a)) (a : A) (c₁ c₂ : R) (v₁ v₂ : P (B a)) :
    (SetOperad.total x fun b => cor (L b) (c b) (update y a (c₁ • v₁ + c₂ • v₂) b)).op
      = c₁ • (SetOperad.total x fun b => cor (L b) (c b) (update y a v₁ b)).op
        + c₂ • (SetOperad.total x fun b => cor (L b) (c b) (update y a v₂ b)).op := by
  have e : ∀ v : P (B a), (fun b => cor (L b) (c b) (update y a v b))
      = update (fun b => cor (R := R) (L b) (c b) (y b)) a (cor (L a) (c a) v) := fun v =>
    funext fun b => apply_update (fun b => cor (R := R) (L b) (c b)) y a v b
  rw [e, e, e]
  exact total_op_update x _ a c₁ c₂ rfl rfl (by simp only [cor_op, map_add, map_smul])

lemma total_cor_eq_zero (x : SgnOp R P A) (L : ∀ a, LinOrd (B a)) (c : A → Bool)
    (y : (a : A) → P (B a)) {a : A} (h : GrOperad.par (R := R) (c a) (y a) = 0) :
    (SetOperad.total x fun b => cor (L b) (c b) (y b)).op = 0 := by
  have e : (fun b => cor (R := R) (L b) (c b) (y b))
      = update (fun b => cor (R := R) (L b) (c b) (y b)) a (cor (L a) (c a) (y a)) :=
    (update_eq_self a _).symm
  rw [e, total_op_update x _ a (0 : R) 0 (v₁ := cor (L a) (c a) (y a))
    (v₂ := cor (L a) (c a) (y a)) rfl rfl (by simp only [cor_op, h, smul_zero, add_zero])]
  simp only [zero_smul, add_zero]

lemma total_cor_add (L : LinOrd A) (p : Bool) (x₁ x₂ : P A) (y : (a : A) → SgnOp R P (B a)) :
    (SetOperad.total (cor L p (x₁ + x₂)) y).op
      = (SetOperad.total (cor L p x₁) y).op + (SetOperad.total (cor L p x₂) y).op := by
  have h := total_cor_lin L p 1 1 x₁ x₂ y
  simp only [one_smul] at h
  exact h

lemma total_cor_smul (L : LinOrd A) (p : Bool) (c : R) (x : P A)
    (y : (a : A) → SgnOp R P (B a)) :
    (SetOperad.total (cor L p (c • x)) y).op = c • (SetOperad.total (cor L p x) y).op := by
  have h := total_cor_lin L p c 0 x x y
  simp only [zero_smul, add_zero] at h
  exact h

lemma total_cor_update_add (x : SgnOp R P A) (L : ∀ a, LinOrd (B a)) (c : A → Bool)
    (y : (a : A) → P (B a)) (a : A) (v₁ v₂ : P (B a)) :
    (SetOperad.total x fun b => cor (L b) (c b) (update y a (v₁ + v₂) b)).op
      = (SetOperad.total x fun b => cor (L b) (c b) (update y a v₁ b)).op
        + (SetOperad.total x fun b => cor (L b) (c b) (update y a v₂ b)).op := by
  have h := total_cor_update x L c y a 1 1 v₁ v₂
  simp only [one_smul] at h
  exact h

lemma total_cor_update_smul (x : SgnOp R P A) (L : ∀ a, LinOrd (B a)) (c : A → Bool)
    (y : (a : A) → P (B a)) (a : A) (r : R) (v : P (B a)) :
    (SetOperad.total x fun b => cor (L b) (c b) (update y a (r • v) b)).op
      = r • (SetOperad.total x fun b => cor (L b) (c b) (update y a v b)).op := by
  have h := total_cor_update x L c y a r 0 v v
  simp only [zero_smul, add_zero] at h
  exact h

end SgnOp

/-! ## Composing into a total composite -/

namespace May

section CompTotal

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {A : Type} [Fintype A] [DecidableEq A] {B : A → Type} [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)] {Y : Type} [Fintype Y] [DecidableEq Y]

/-- **The padded family** in a set operad: `Z` at `j` and the unit elsewhere. -/
def padS {J : Type} [DecidableEq J] (j : J) (Z : S Y) (p : J) : S (Pad j Y p) :=
  if h : p = j then SetOperad.map (padIn h) Z else SetOperad.map (padOut h) SetOperad.one

/-- **Composing into a total composite** composes into one of the inserted operations: the total
composite with the padded family is that of the total composites of the inserted operations with
their padded families. -/
theorem comp_total (x : S A) (y : (a : A) → S (B a)) (j : Σ a, B a) (Z : S Y) :
    SetOperad.comp j (SetOperad.total x y) Z
      = SetOperad.map ((Equiv.sigmaAssoc fun a b => Pad j Y ⟨a, b⟩).symm.trans (padEquiv j Y))
        (SetOperad.total x fun a => SetOperad.total (y a) fun b => padS j Z ⟨a, b⟩) := by
  letI := SetOperad.toMaySetOperad S
  rw [← MaySetOperad.comp_toMaySetOperad, MaySetOperad.comp_def,
    ← SetOperad.total_assoc x y fun a b => padS j Z ⟨a, b⟩, ← SetOperad.map_trans,
    ← Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.refl_trans]
  rfl

/-- **A total composite with units** is a relabelling. -/
theorem total_units {X : Type} [Fintype X] [DecidableEq X] (u : S X) {C : X → Type}
    [∀ b, Fintype (C b)] [∀ b, DecidableEq (C b)] (w : (b : X) → S (C b)) (τ : ∀ b, Unit ≃ C b)
    (hw : ∀ b, w b = SetOperad.map (τ b) SetOperad.one) :
    SetOperad.total u w
      = SetOperad.map ((Equiv.sigmaPUnit X).symm.trans (Equiv.sigmaCongrRight τ)) u := by
  have h := SetOperad.total_map (Equiv.refl X) τ u (fun _ => SetOperad.one) w hw
  rw [SetOperad.map_refl] at h
  rw [← h, SetOperad.map_trans]
  congr 1
  conv_rhs => rw [← SetOperad.total_one_right u]
  rw [← SetOperad.map_trans, Equiv.self_trans_symm, SetOperad.map_refl]

/-- Relabelling a padding along a map sending exactly one element to the slot. -/
def padRel {X J : Type} [DecidableEq X] [DecidableEq J] {j₀ : X} {j : J} (κ : X → J)
    (hκ : ∀ b, κ b = j ↔ b = j₀) (b : X) : Pad j₀ Y b ≃ Pad j Y (κ b) where
  toFun
    | Sum.inl ⟨u, h⟩ => Sum.inl ⟨u, fun e => h ((hκ b).1 e)⟩
    | Sum.inr ⟨z, h⟩ => Sum.inr ⟨z, (hκ b).2 h⟩
  invFun
    | Sum.inl ⟨u, h⟩ => Sum.inl ⟨u, fun e => h ((hκ b).2 e)⟩
    | Sum.inr ⟨z, h⟩ => Sum.inr ⟨z, (hκ b).1 h⟩
  left_inv := by rintro (⟨u, h⟩ | ⟨z, h⟩) <;> rfl
  right_inv := by rintro (⟨u, h⟩ | ⟨z, h⟩) <;> rfl

lemma padS_rel {X J : Type} [DecidableEq X] [DecidableEq J] {j₀ : X} {j : J} (κ : X → J)
    (hκ : ∀ b, κ b = j ↔ b = j₀) (Z : S Y) (b : X) :
    padS j Z (κ b) = SetOperad.map (padRel κ hκ b) (padS j₀ Z b) := by
  by_cases h : b = j₀
  · rw [padS, padS, dif_pos ((hκ b).2 h), dif_pos h, ← SetOperad.map_trans]
    refine map_congr ?_ Z
    intro z
    rfl
  · rw [padS, padS, dif_neg (fun e => h ((hκ b).1 e)), dif_neg h, ← SetOperad.map_trans]
    refine map_congr ?_ (SetOperad.one : S Unit)
    intro u
    rfl

/-- **A partial composite is a total composite with a padded family.** -/
lemma comp_eq_total_padS {X : Type} [Fintype X] [DecidableEq X] (j₀ : X) (u : S X) (Z : S Y) :
    SetOperad.comp j₀ u Z = SetOperad.map (padEquiv j₀ Y) (SetOperad.total u (padS j₀ Z)) := by
  letI := SetOperad.toMaySetOperad S
  rw [← MaySetOperad.comp_toMaySetOperad, MaySetOperad.comp_def]
  rfl

end CompTotal

end May

/-! ### Total composition and the right action -/

namespace GrComposite

section ActPad

variable {S A : Type} [DecidableEq S] [DecidableEq A]

/-- **The inputs owned after composing at `i`**, as the padded inputs of a total composite. -/
def actPad (f : S → A) (i : S) (Y : Type) (a : A) :
    (Σ b : Fib f a, Pad (⟨f i, ⟨i, rfl⟩⟩ : Σ a, Fib f a) Y ⟨a, b⟩)
      ≃ Fib (actOwner (Y := Y) f i) a where
  toFun x := match x with
    | ⟨b, Sum.inl ⟨_, h⟩⟩ =>
        ⟨Sum.inl ⟨b.1, fun e => h (by
          obtain ⟨b, hb⟩ := b
          simp only at e
          subst e
          subst hb
          rfl)⟩, b.2⟩
    | ⟨_, Sum.inr ⟨y, h⟩⟩ => ⟨Sum.inr y, (congrArg Sigma.fst h).symm⟩
  invFun x := match x with
    | ⟨Sum.inl t, ht⟩ => ⟨⟨t.1, ht⟩, Sum.inl ⟨(), fun e => t.2
        (congrArg (fun p : (Σ a, Fib f a) => p.2.1) e)⟩⟩
    | ⟨Sum.inr y, hy⟩ => ⟨⟨i, hy⟩, Sum.inr ⟨y, by subst hy; rfl⟩⟩
  left_inv := by
    rintro ⟨⟨b, hb⟩, ⟨u, h⟩ | ⟨y, h⟩⟩
    · rfl
    · have e : b = i := congrArg (fun p : (Σ a, Fib f a) => p.2.1) h
      subst e
      rfl
  right_inv := by
    rintro ⟨t | y, h⟩ <;> rfl

end ActPad

section PadTotal

variable {T : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad T]
  {S A Y : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Fintype Y]
  [DecidableEq Y]

omit [Fintype A] in
/-- **Away from the owner of `i`**, the inserted operation of a total composite with the padded
family is relabelled. -/
lemma total_padS_ne (f : S → A) (i : S) {a : A} (h : f i ≠ a) (v : T (Fib f a)) (Z : T Y) :
    SetOperad.map (actPad f i Y a)
        (SetOperad.total v fun b => padS (⟨f i, ⟨i, rfl⟩⟩ : Σ a, Fib f a) Z ⟨a, b⟩)
      = SetOperad.map (actNe f i a h) v := by
  have hb : ∀ b : Fib f a, (⟨a, b⟩ : Σ a, Fib f a) ≠ ⟨f i, ⟨i, rfl⟩⟩ :=
    fun b e => h (congrArg Sigma.fst e).symm
  rw [total_units v _ (fun b => padOut (hb b)) (fun b => dif_neg (hb b)), ← SetOperad.map_trans]
  refine May.map_congr ?_ v
  intro b
  rfl

omit [Fintype A] in
/-- **At the owner of `i`**, the inserted operation of a total composite with the padded family
is the partial composite at `i`. -/
lemma total_padS_eq (f : S → A) (i : S) (v : T (Fib f (f i))) (Z : T Y) :
    SetOperad.map (actPad f i Y (f i))
        (SetOperad.total v fun b => padS (⟨f i, ⟨i, rfl⟩⟩ : Σ a, Fib f a) Z ⟨f i, b⟩)
      = SetOperad.map (actEq f i (f i) rfl) (SetOperad.comp (⟨i, rfl⟩ : Fib f (f i)) v Z) := by
  have hκ : ∀ b : Fib f (f i), (⟨f i, b⟩ : Σ a, Fib f a) = ⟨f i, ⟨i, rfl⟩⟩ ↔ b = ⟨i, rfl⟩ :=
    fun b => ⟨fun e => eq_of_heq (Sigma.mk.inj e).2, fun e => e ▸ rfl⟩
  have h1 := SetOperad.total_map (Equiv.refl _)
    (B' := fun b => Pad (⟨f i, ⟨i, rfl⟩⟩ : Σ a, Fib f a) Y ⟨f i, b⟩)
    (padRel (Y := Y) (Sigma.mk (f i)) hκ) v
    (padS (⟨i, rfl⟩ : Fib f (f i)) Z) (fun b => padS (⟨f i, ⟨i, rfl⟩⟩ : Σ a, Fib f a) Z ⟨f i, b⟩)
    (fun b => padS_rel (Sigma.mk (f i)) hκ Z b)
  rw [SetOperad.map_refl] at h1
  rw [← h1, comp_eq_total_padS, ← SetOperad.map_trans, ← SetOperad.map_trans]
  refine May.map_congr ?_ _
  rintro ⟨b, ⟨u, hu⟩ | ⟨y, hy⟩⟩
  · rfl
  · obtain rfl : b = ⟨i, rfl⟩ := hy
    rfl

end PadTotal

end GrComposite

/-! ## Total composition on graded composites -/

namespace GrComposite

variable {R : Type u} [CommRing R]
  {M : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M A)] [GrSpecies R M]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  (F : SymSpeciesHom R M P) {S : Type} [Fintype S] [DecidableEq S]

open SgnOp


/-- The part of a generator with outer parity `p` and inner parities `c`, totally composed after
mapping the outer operation along `F`. -/
noncomputable def totalGen (g : GrCompGen M P S) (p : Bool) (c : g.A → Bool) : P S :=
  GrOperad.map (R := R) g.e (SetOperad.total (cor (R := R) g.L p (F.app g.A g.m))
    fun a => cor (R := R) (ordOf (g.B a)) (c a) (g.y a)).op

/-- **The total composite of a generator.** -/
noncomputable def totalFun (g : GrCompGen M P S) : P S :=
  ∑ p : Bool, ∑ c : g.A → Bool, totalGen F g p c

lemma totalGen_add_m (g : GrCompGen M P S) (m' : M g.A) (p : Bool) (c : g.A → Bool) :
    totalGen F { g with m := g.m + m' } p c = totalGen F g p c + totalGen F { g with m := m' } p c
    := by
  simp only [totalGen, map_add, total_cor_add]

lemma totalGen_smul_m (g : GrCompGen M P S) (r : R) (p : Bool) (c : g.A → Bool) :
    totalGen F { g with m := r • g.m } p c = r • totalGen F g p c := by
  simp only [totalGen, map_smul, total_cor_smul]

lemma totalGen_add_y (g : GrCompGen M P S) (a : g.A) (z z' : P (g.B a)) (p : Bool)
    (c : g.A → Bool) :
    totalGen F { g with y := update g.y a (z + z') } p c
      = totalGen F { g with y := update g.y a z } p c
        + totalGen F { g with y := update g.y a z' } p c := by
  simp only [totalGen]
  rw [total_cor_update_add, map_add]

lemma totalGen_smul_y (g : GrCompGen M P S) (a : g.A) (r : R) (z : P (g.B a)) (p : Bool)
    (c : g.A → Bool) :
    totalGen F { g with y := update g.y a (r • z) } p c
      = r • totalGen F { g with y := update g.y a z } p c := by
  simp only [totalGen]
  rw [total_cor_update_smul, map_smul]

lemma cor_map {A A' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    (σ : A ≃ A') (L : LinOrd A') (p : Bool) (x : P A) :
    cor (R := R) L p (GrOperad.map (R := R) σ x)
      = SetOperad.map σ (cor (R := R) (LinOrd.map σ.symm L) p x) :=
  SgnOp.ext (GrOperad.map_par (R := R) σ p x).symm
    (SgnData.ext (LinOrd.ext fun a b => by simp [corData]) rfl rfl)

lemma totalGen_outer (g : GrCompGen M P S) {A : Type} [Fintype A] [DecidableEq A] (σ : A ≃ g.A)
    (m : M A) (p : Bool) (c : g.A → Bool) :
    totalGen F { g with m := SymSpecies.map (R := R) σ m } p c
      = totalGen F ⟨A, fun a => g.B (σ a), LinOrd.map σ.symm g.L, m, fun a => g.y (σ a),
          (Equiv.sigmaCongrLeft σ).trans g.e⟩ p (c ∘ σ) := by
  simp only [totalGen]
  rw [F.app_map, show SymSpecies.map (R := R) σ (F.app A m) = GrOperad.map (R := R) σ (F.app A m)
    from rfl, cor_map, ← SetOperad.total_map σ (fun a => Equiv.refl _) _
      (fun a => cor (R := R) (ordOf (g.B (σ a))) (c (σ a)) (g.y (σ a))) _
      (fun a => (SetOperad.map_refl _).symm), map_op, ← GrOperad.map_trans]
  refine gmap_congr (fun _ => rfl) _

lemma totalGen_inner (g : GrCompGen M P S) {B : g.A → Type} [∀ a, Fintype (B a)]
    [∀ a, DecidableEq (B a)] (τ : ∀ a, g.B a ≃ B a) (p : Bool) (c : g.A → Bool) :
    totalGen F ⟨g.A, B, g.L, g.m, fun a => SymSpecies.map (R := R) (τ a) (g.y a),
        (Equiv.sigmaCongrRight τ).symm.trans g.e⟩ p c = totalGen F g p c := by
  simp only [totalGen]
  have h := SetOperad.total_map (Equiv.refl g.A) τ (cor (R := R) g.L p (F.app g.A g.m))
    (fun a => cor (R := R) (ordOf (g.B a)) (c a) (g.y a))
    (fun a => SetOperad.map (τ a) (cor (R := R) (ordOf (g.B a)) (c a) (g.y a))) fun _ => rfl
  rw [SetOperad.map_refl] at h
  rw [total_op_congr _ (y := fun a => cor (R := R) (ordOf (B a)) (c a)
      (SymSpecies.map (R := R) (τ a) (g.y a)))
      (y' := fun a => SetOperad.map (τ a) (cor (R := R) (ordOf (g.B a)) (c a) (g.y a)))
      (fun a => (GrOperad.map_par (R := R) (τ a) (c a) (g.y a)).symm) (fun a => rfl),
    ← h, map_op, ← GrOperad.map_trans]
  refine gmap_congr (fun x => ?_) _
  obtain ⟨a, b⟩ := x
  show g.e ((Equiv.sigmaCongrRight τ).symm ⟨a, τ a b⟩) = g.e ⟨a, b⟩
  rw [show (Equiv.sigmaCongrRight τ).symm ⟨a, τ a b⟩ = ⟨a, b⟩ from by
    rw [Equiv.symm_apply_eq]
    rfl]

lemma totalFun_eq_single (g : GrCompGen M P S) (c₀ : g.A → Bool)
    (hy : ∀ a, GrSpecies.par (R := R) (c₀ a) (g.y a) = g.y a) :
    totalFun F g = ∑ p : Bool, totalGen F g p c₀ := by
  refine Finset.sum_congr rfl fun p _ => Finset.sum_eq_single c₀ (fun c _ hc => ?_) (by simp)
  obtain ⟨a, ha⟩ : ∃ a, c a ≠ c₀ a := by
    by_contra h
    exact hc (funext fun a => by_contra fun h' => h ⟨a, h'⟩)
  simp only [totalGen]
  rw [total_cor_eq_zero _ _ _ _ (a := a) (by
    rw [← hy a]
    exact (GrOperad.par_par (R := R) _ _ _).trans (if_neg ha)), map_zero]

lemma totalFun_reorder (g : GrCompGen M P S) (L' : LinOrd g.A) (c₀ : g.A → Bool)
    (hy : ∀ a, GrSpecies.par (R := R) (c₀ a) (g.y a) = g.y a) :
    totalFun F g = GrEnd.rsg R g.L L' c₀ • totalFun F { g with L := L' } := by
  rw [totalFun_eq_single F g c₀ hy, totalFun_eq_single F { g with L := L' } c₀ hy,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [totalGen]
  rw [total_op_reorder (x := cor (R := R) g.L p (F.app g.A g.m))
    (x' := cor (R := R) L' p (F.app g.A g.m)) rfl rfl, map_smul]
  rfl

lemma totalFun_respects : GrCompGen.Respects R (totalFun F (S := S)) where
  add_m g m' := by
    simp only [totalFun, totalGen_add_m, Finset.sum_add_distrib]
  smul_m g r := by
    simp only [totalFun, totalGen_smul_m, Finset.smul_sum]
  add_y g a z z' := by
    simp only [totalFun, totalGen_add_y, Finset.sum_add_distrib]
  smul_y g a r z := by
    simp only [totalFun, totalGen_smul_y, Finset.smul_sum]
  outer g A _ _ σ m := by
    simp only [totalFun, totalGen_outer]
    refine Finset.sum_congr rfl fun p _ => ?_
    exact Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl Bool)) _ _ fun c => rfl
  inner g B _ _ τ := by
    simp only [totalFun, totalGen_inner]
  reorder g L' c hy := totalFun_reorder F g L' c hy

variable (R) in
/-- **Total composition** `M ∘ P → P` after a morphism `F : M → P`. -/
noncomputable def total : GrComposite R M P S →ₗ[R] P S := lift (totalFun F) (totalFun_respects F)

@[simp] lemma total_mk (g : GrCompGen M P S) : total R F (mk R g) = totalFun F g :=
  lift_mk _ _ g

/-! ### Total composition is a morphism of right modules -/

section Act

variable {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]

/-- **Total composition after the right action at `i` is composition at `i`**, on a homogeneous
generator given by owners. -/
lemma totalGen_act (L : LinOrd A) (m : M A) (f : S → A) (yy : ∀ a, P (Fib f a)) (c : A → Bool)
    (hyy : ∀ a, GrOperad.par (R := R) (c a) (yy a) = yy a) (i : S) {q : Bool} (z : P Y)
    (hz : GrOperad.par (R := R) q z = z) (p : Bool) :
    totalGen F (actGen (R := R) L m f yy i z q) p (update c (f i) (xor (c (f i)) q))
      = GrOperad.comp (R := R) i (totalGen F (ownGen L m f yy) p c) z := by
  set x := cor (R := R) L p (F.app A m) with hx
  set ys : (a : A) → SgnOp R P (Fib f a) := fun a => cor (R := R) (ordOf (Fib f a)) (c a) (yy a)
    with hys
  set Zs := cor (R := R) (ordOf Y) q z with hZs
  set j : Σ a, Fib f a := ⟨f i, ⟨i, rfl⟩⟩ with hj
  set T := SetOperad.total x ys with hT
  set W : (a : A) → SgnOp R P (Σ b : Fib f a, Pad j Y ⟨a, b⟩) :=
    fun a => SetOperad.total (ys a) fun b => May.padS j Zs ⟨a, b⟩ with hW
  -- the right-hand side
  have hR1 : GrOperad.comp (R := R) i (totalGen F (ownGen L m f yy) p c) z
      = GrOperad.map (R := R) ((compEquiv (Equiv.sigmaFiberEquiv f) (Equiv.refl Y) j).trans
          (slotEquiv (rfl : Equiv.sigmaFiberEquiv f j = i))) (GrOperad.comp (R := R) j T.op z) :=
    GrOperad.comp_map_left (Equiv.sigmaFiberEquiv f) j i rfl T.op z
  have hR2 : GrOperad.comp (R := R) j T.op z
      = σ R (q && T.dat.aft j) • (SetOperad.comp j T Zs).op := by
    rw [comp_op, smul_smul, show Zs.op = z from hz,
      show SgnData.sgn j T.dat Zs.dat = (q && T.dat.aft j) from rfl, σ_mul_self, one_smul]
  have hR3 := May.comp_total x ys j Zs
  have hR4 := SetOperad.total_map (Equiv.refl A) (B' := Fib (actOwner (Y := Y) f i))
    (actPad f i Y) x W (fun a => SetOperad.map (actPad f i Y a) (W a)) fun _ => rfl
  rw [SetOperad.map_refl] at hR4
  -- the inserted operations, untwisted
  set c' := update c (f i) (xor (c (f i)) q) with hc'
  set ys₀ : (a : A) → SgnOp R P (Fib (actOwner (Y := Y) f i) a) := fun a =>
    cor (R := R) (ordOf (Fib (actOwner (Y := Y) f i) a)) (c' a) (actY (R := R) L f yy i z false a)
    with hys₀
  have hcomp : GrOperad.comp (R := R) (⟨i, rfl⟩ : Fib f (f i)) (yy (f i)) z
      = GrOperad.par (R := R) (xor (c (f i)) q)
          (GrOperad.comp (R := R) (⟨i, rfl⟩ : Fib f (f i)) (yy (f i)) z) :=
    (GrOperad.par_comp_hom _ rfl (hyy (f i)) hz).symm
  have hops : ∀ a, (SetOperad.map (actPad f i Y a) (W a)).op = (ys₀ a).op := by
    intro a
    by_cases h : f i = a
    · subst h
      rw [hW, total_padS_eq, map_op, comp_op]
      simp only [hys₀, hys, hZs, cor_op, hc', update_self]
      rw [actY, actLin_eq _ _ _ _ _ _ rfl, hyy, hz, ← GrOperad.map_par, ← hcomp]
      show GrOperad.map (R := R) _ (σ R (q && false) • _) = _
      rw [Bool.and_false, σ_false, one_smul]
    · rw [hW, total_padS_ne f i h, map_op]
      simp only [hys₀, hys, cor_op, hc', update_of_ne (Ne.symm h)]
      rw [actY, actLin_ne _ _ _ _ _ _ h, Bool.false_and, GrOperad.tw_false, hyy,
        ← GrOperad.map_par, hyy]
  have htots : ∀ a, (SetOperad.map (actPad f i Y a) (W a)).dat.tot = (ys₀ a).dat.tot := by
    intro a
    by_cases h : f i = a
    · subst h
      rw [hW, total_padS_eq]
      simp only [hys₀, hc', update_self]
      rfl
    · rw [hW, total_padS_ne f i h]
      simp only [hys₀, hc', update_of_ne (Ne.symm h)]
      rfl
  -- the twists
  have htw : (SetOperad.total x fun a => cor (R := R) (ordOf (Fib (actOwner (Y := Y) f i) a))
        (c' a) (actY (R := R) L f yy i z q a)).op
      = (∏ a, σ R ((q && ltB L (f i) a) && c a)) • (SetOperad.total x ys₀).op := by
    refine total_op_smul x (y' := ys₀) _ (fun _ => rfl) fun a => ?_
    simp only [hys₀, cor_op]
    by_cases h : f i = a
    · subst h
      rw [actY, actY, actLin_eq _ _ _ _ _ _ rfl, actLin_eq _ _ _ _ _ _ rfl, ltB_self,
        Bool.and_false, Bool.false_and, σ_false, one_smul]
    · have hv : GrOperad.par (R := R) (c a) (GrOperad.map (R := R) (actNe (Y := Y) f i a h) (yy a))
          = GrOperad.map (R := R) (actNe (Y := Y) f i a h) (yy a) := by
        rw [← GrOperad.map_par, hyy]
      rw [actY, actY, actLin_ne _ _ _ _ _ _ h, actLin_ne _ _ _ _ _ _ h, Bool.false_and,
        GrOperad.tw_false, hc', update_of_ne (Ne.symm h), GrOperad.tw_hom _ hv, map_smul, hv]
  have hsign : (∏ a, σ R ((q && ltB L (f i) a) && c a)) = σ R (q && T.dat.aft j) := by
    rw [hT, hj, total_aft, show (ys (f i)).dat.aft ⟨i, rfl⟩ = false from rfl,
      show x.dat.aft (f i) = false from rfl, Bool.false_xor, Bool.false_xor,
      show x.dat.ord = L from rfl, show (fun a => (ys a).dat.tot) = c from rfl,
      SgnData.sigma_aftL₁ R _ _ _ _ _ (Finset.nodup_toList _), Finset.toList_toFinset]
  -- assembling
  show GrOperad.map (R := R) (Equiv.sigmaFiberEquiv (actOwner (Y := Y) f i)) (SetOperad.total x
      fun a => cor (R := R) (ordOf (Fib (actOwner (Y := Y) f i) a)) (c' a)
        (actY (R := R) L f yy i z q a)).op = _
  rw [htw, hsign, hR1, hR2, hR3, map_op, map_smul, map_smul,
    total_op_congr x (y := ys₀) (y' := fun a => SetOperad.map (actPad f i Y a) (W a))
      (fun a => (hops a).symm) (fun a => (htots a).symm), ← hR4, map_op, ← GrOperad.map_trans,
    ← GrOperad.map_trans]
  congr 1
  refine gmap_congr ?_ _
  rintro ⟨a, b, ⟨u, hu⟩ | ⟨y, hy⟩⟩ <;> rfl

end Act

end GrComposite

end Operad
