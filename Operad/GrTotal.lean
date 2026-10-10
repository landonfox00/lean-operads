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

end SgnOp

end Operad
