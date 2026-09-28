/-
# The convolution algebra of a binary operad in low weight

The deformation complexes of binary quadratic operads that one computes by hand live in weights
one to three: cochains on the corollas, on the two-vertex trees and on the three-vertex trees.
This file gives those trees names and computes the signed convolution product and the bracket
on them, for cochains with values in any non-symmetric operad `Q`:

* the corolla `cor e`, the two combs `lc e e'` (child in the first slot) and `rc e e'` (child in
  the second slot), and the five three-vertex trees `ll`, `lr`, `bl`, `rl`, `rr`; every tree of
  arity two, three and four is one of these (`OfArity.eq_cor`, `eq_lc_or_rc`, `cases_four`);
* `compFin` of two cochains at a factored tree (`compFin_apply_graft`) and away from any
  factorization (`compFin_apply_eq_zero`);
* the values of `f ⋆ₛ g` (weights one and one), `f ⋆ₛ θ` and `θ ⋆ₛ f` (weights one and two), and of
  the brackets `⁅f, g⁆ₛ = f ⋆ₛ g + g ⋆ₛ f` and `⁅f, θ⁆ₛ = f ⋆ₛ θ - θ ⋆ₛ f`, tree by tree.

These are the formulas for the Maurer–Cartan equation and the twisted differentials `d¹`, `d²`.
-/
import Operad.KoszulDual
import Operad.DG

universe u v w

namespace Operad

open NSOperad BTree

namespace BTree.OfArity

variable {E : Type v}

/-- The corolla of a generator. -/
abbrev cor (e : E) : OfArity E 2 := corolla e

/-- The left comb: `e` with `e'` in its first slot. -/
def lc (e e' : E) : OfArity E 3 := ⟨node e (node e' leaf leaf) leaf, rfl⟩

/-- The right comb: `e` with `e'` in its second slot. -/
def rc (e e' : E) : OfArity E 3 := ⟨node e leaf (node e' leaf leaf), rfl⟩

/-- `((· ·) ·) ·` -/
def ll (e₁ e₂ e₃ : E) : OfArity E 4 := ⟨node e₁ (node e₂ (node e₃ leaf leaf) leaf) leaf, rfl⟩
/-- `(· (· ·)) ·` -/
def lr (e₁ e₂ e₃ : E) : OfArity E 4 := ⟨node e₁ (node e₂ leaf (node e₃ leaf leaf)) leaf, rfl⟩
/-- `(· ·) (· ·)`, with `e₂` on the left and `e₃` on the right. -/
def bl (e₁ e₂ e₃ : E) : OfArity E 4 :=
  ⟨node e₁ (node e₂ leaf leaf) (node e₃ leaf leaf), rfl⟩
/-- `· ((· ·) ·)` -/
def rl (e₁ e₂ e₃ : E) : OfArity E 4 := ⟨node e₁ leaf (node e₂ (node e₃ leaf leaf) leaf), rfl⟩
/-- `· (· (· ·))` -/
def rr (e₁ e₂ e₃ : E) : OfArity E 4 := ⟨node e₁ leaf (node e₂ leaf (node e₃ leaf leaf)), rfl⟩

private lemma arity_eq_one_iff {t : BTree E} : t.arity = 1 ↔ t = leaf :=
  ⟨eq_leaf_of_arity_eq_one, fun h => h ▸ rfl⟩

/-- Every tree of arity two is a corolla. -/
lemma eq_cor (t : OfArity E 2) : ∃ e, t = cor e := by
  obtain ⟨t, ht⟩ := t
  cases t with
  | leaf => simp [arity] at ht
  | node e l r =>
    simp only [arity_node] at ht
    have hl := arity_pos l
    have hr := arity_pos r
    obtain rfl := eq_leaf_of_arity_eq_one (show l.arity = 1 by omega)
    obtain rfl := eq_leaf_of_arity_eq_one (show r.arity = 1 by omega)
    exact ⟨e, rfl⟩

/-- Every tree of arity three is a comb. -/
lemma eq_lc_or_rc (t : OfArity E 3) : (∃ e e', t = lc e e') ∨ ∃ e e', t = rc e e' := by
  obtain ⟨t, ht⟩ := t
  cases t with
  | leaf => simp [arity] at ht
  | node e l r =>
    simp only [arity_node] at ht
    have hl := arity_pos l
    have hr := arity_pos r
    by_cases h : l.arity = 1
    · obtain rfl := eq_leaf_of_arity_eq_one h
      obtain ⟨e', he'⟩ := eq_cor (⟨r, by simp at ht; omega⟩ : OfArity E 2)
      have : r = node e' leaf leaf := congrArg Subtype.val he'
      subst this
      exact Or.inr ⟨e, e', rfl⟩
    · obtain rfl := eq_leaf_of_arity_eq_one (show r.arity = 1 by omega)
      obtain ⟨e', he'⟩ := eq_cor (⟨l, by omega⟩ : OfArity E 2)
      have : l = node e' leaf leaf := congrArg Subtype.val he'
      subst this
      exact Or.inl ⟨e, e', rfl⟩

/-- Every tree of arity four is one of the five shapes. -/
lemma cases_four (t : OfArity E 4) :
    (∃ e₁ e₂ e₃, t = ll e₁ e₂ e₃) ∨ (∃ e₁ e₂ e₃, t = lr e₁ e₂ e₃) ∨
    (∃ e₁ e₂ e₃, t = bl e₁ e₂ e₃) ∨ (∃ e₁ e₂ e₃, t = rl e₁ e₂ e₃) ∨
    (∃ e₁ e₂ e₃, t = rr e₁ e₂ e₃) := by
  obtain ⟨t, ht⟩ := t
  cases t with
  | leaf => simp [arity] at ht
  | node e₁ l r =>
    simp only [arity_node] at ht
    have hl := arity_pos l
    have hr := arity_pos r
    by_cases h1 : l.arity = 1
    · obtain rfl := eq_leaf_of_arity_eq_one h1
      rcases eq_lc_or_rc (⟨r, by simp at ht; omega⟩ : OfArity E 3) with ⟨e₂, e₃, h⟩ | ⟨e₂, e₃, h⟩
      · have : r = (lc e₂ e₃).1 := congrArg Subtype.val h
        subst this
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e₁, e₂, e₃, rfl⟩)))
      · have : r = (rc e₂ e₃).1 := congrArg Subtype.val h
        subst this
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e₁, e₂, e₃, rfl⟩)))
    · by_cases h2 : l.arity = 2
      · obtain ⟨e₂, he₂⟩ := eq_cor (⟨l, h2⟩ : OfArity E 2)
        obtain ⟨e₃, he₃⟩ := eq_cor (⟨r, by omega⟩ : OfArity E 2)
        have hl' : l = node e₂ leaf leaf := congrArg Subtype.val he₂
        have hr' : r = node e₃ leaf leaf := congrArg Subtype.val he₃
        subst hl' hr'
        exact Or.inr (Or.inr (Or.inl ⟨e₁, e₂, e₃, rfl⟩))
      · obtain rfl := eq_leaf_of_arity_eq_one (show r.arity = 1 by omega)
        rcases eq_lc_or_rc (⟨l, by omega⟩ : OfArity E 3) with ⟨e₂, e₃, h⟩ | ⟨e₂, e₃, h⟩
        · have : l = (lc e₂ e₃).1 := congrArg Subtype.val h
          subst this
          exact Or.inl ⟨e₁, e₂, e₃, rfl⟩
        · have : l = (rc e₂ e₃).1 := congrArg Subtype.val h
          subst this
          exact Or.inr (Or.inl ⟨e₁, e₂, e₃, rfl⟩)

end BTree.OfArity

namespace TConv

open BTree.OfArity

variable {R : Type u} [CommRing R] {E : Type v}
  {Q : ℕ → Type w} [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)] [NSOperad R Q]

/-- **`compFin` of two cochains at a factored tree.** -/
lemma compFin_apply_graft {m n : ℕ} (i : Fin m) (f : TConv R E Q m) (g : TConv R E Q n)
    (t₁ : OfArity E m) (t₂ : OfArity E n) (t : OfArity E (m - 1 + n))
    (h : t₁.1.graft i t₂.1 = t.1) :
    compFin (R := R) i f g t = compFin (R := R) (P := Q) i (f t₁) (g t₂) := by
  have hi := i.isLt
  unfold compFin
  rw [reindex_apply, comp_apply]
  rw [compFun_eq (i : ℕ) (m - i - 1) _ g (OfArity.cast (by omega) t₁) t₂
    (by rw [OfArity.cast_val, OfArity.cast_val]; exact h), reindex_apply]
  simp only [OfArity.cast_cast, OfArity.cast_self]

/-- **`compFin` of two cochains vanishes away from any factorization.** -/
lemma compFin_apply_eq_zero {m n : ℕ} (i : Fin m) (f : TConv R E Q m) (g : TConv R E Q n)
    (t : OfArity E (m - 1 + n))
    (h : ∀ (t₁ : OfArity E m) (t₂ : OfArity E n), t₁.1.graft i t₂.1 ≠ t.1) :
    compFin (R := R) i f g t = 0 := by
  have hi := i.isLt
  unfold compFin
  rw [reindex_apply, comp_apply]
  rw [compFun_eq_zero (i : ℕ) (m - i - 1) _ g (fun t₁ t₂ h' =>
    h (OfArity.cast (by omega) t₁) t₂ (by simpa using h')), map_zero]

lemma sstar_apply {j k : ℕ} (f : TConv R E Q (j + 1)) (g : TConv R E Q (k + 1))
    (t : OfArity E (j + k + 1)) :
    sstar (R := R) f g t = ∑ a : Fin (j + 1), ((-1 : R) ^ ((a : ℕ) * k)) • compFin (R := R) a f g t := by
  rw [sstar_def, Finset.sum_apply]
  rfl

/-! ## Weight one against weight one -/

section Two

variable (f g : TConv R E Q 2) (e e' : E)

lemma sstar_apply_lc :
    sstar (R := R) (j := 1) (k := 1) f g (lc e e')
      = compFin (R := R) (P := Q) (0 : Fin 2) (f (cor e)) (g (cor e')) := by
  rw [sstar_apply, Fin.sum_univ_two, compFin_apply_graft 0 f g (cor e) (cor e') _ rfl,
    compFin_apply_eq_zero 1 f g _ (fun t₁ t₂ h => ?_)]
  · simp
  · obtain ⟨x, rfl⟩ := eq_cor t₁
    simp [lc, cor, corolla, graft_node] at h

lemma sstar_apply_rc :
    sstar (R := R) (j := 1) (k := 1) f g (rc e e')
      = -compFin (R := R) (P := Q) (1 : Fin 2) (f (cor e)) (g (cor e')) := by
  rw [sstar_apply, Fin.sum_univ_two, compFin_apply_graft 1 f g (cor e) (cor e') _ rfl,
    compFin_apply_eq_zero 0 f g _ (fun t₁ t₂ h => ?_)]
  · simp
  · obtain ⟨x, rfl⟩ := eq_cor t₁
    obtain ⟨t₂, ht₂⟩ := t₂
    simp only [cor, corolla, Fin.val_zero, graft_node, arity_leaf, Nat.lt_one_iff, if_true,
      graft_leaf, rc, node.injEq] at h
    obtain ⟨_, rfl, _⟩ := h
    simp at ht₂

end Two

/-! ## Weight one against weight two -/

section Three

-- The same shape comparison closes every non-factorization branch; the tree names it needs vary
-- from branch to branch, so the list is kept uniform.
set_option linter.unusedSimpArgs false

variable (f : TConv R E Q 2) (θ : TConv R E Q 3) (e₁ e₂ e₃ : E)

private lemma graft_cor_zero (x : E) (s : BTree E) :
    (cor x).1.graft 0 s = node x s leaf := by
  simp [cor, corolla, graft_node]

private lemma graft_cor_one (x : E) (s : BTree E) :
    (cor x).1.graft 1 s = node x leaf s := by
  simp [cor, corolla, graft_node]

lemma sstar12_apply_ll :
    sstar (R := R) (j := 1) (k := 2) f θ (ll e₁ e₂ e₃)
      = compFin (R := R) (P := Q) (0 : Fin 2) (f (cor e₁)) (θ (lc e₂ e₃)) := by
  rw [sstar_apply, Fin.sum_univ_two, compFin_apply_graft 0 f θ (cor e₁) (lc e₂ e₃) _ rfl,
    compFin_apply_eq_zero 1 f θ _ (fun t₁ t₂ h => ?_)]
  · simp
  · obtain ⟨x, rfl⟩ := eq_cor t₁
    rw [Fin.val_one, graft_cor_one] at h
    simp [ll] at h

lemma sstar12_apply_lr :
    sstar (R := R) (j := 1) (k := 2) f θ (lr e₁ e₂ e₃)
      = compFin (R := R) (P := Q) (0 : Fin 2) (f (cor e₁)) (θ (rc e₂ e₃)) := by
  rw [sstar_apply, Fin.sum_univ_two, compFin_apply_graft 0 f θ (cor e₁) (rc e₂ e₃) _ rfl,
    compFin_apply_eq_zero 1 f θ _ (fun t₁ t₂ h => ?_)]
  · simp
  · obtain ⟨x, rfl⟩ := eq_cor t₁
    rw [Fin.val_one, graft_cor_one] at h
    simp [lr] at h

lemma sstar12_apply_bl : sstar (R := R) (j := 1) (k := 2) f θ (bl e₁ e₂ e₃) = 0 := by
  rw [sstar_apply, Fin.sum_univ_two, compFin_apply_eq_zero 0 f θ _ (fun t₁ t₂ h => ?_),
    compFin_apply_eq_zero 1 f θ _ (fun t₁ t₂ h => ?_)]
  · simp
  all_goals
    obtain ⟨x, rfl⟩ := eq_cor t₁
    simp only [Fin.val_zero, Fin.val_one, graft_cor_zero, graft_cor_one] at h
    simp [bl] at h

lemma sstar12_apply_rl :
    sstar (R := R) (j := 1) (k := 2) f θ (rl e₁ e₂ e₃)
      = compFin (R := R) (P := Q) (1 : Fin 2) (f (cor e₁)) (θ (lc e₂ e₃)) := by
  rw [sstar_apply, Fin.sum_univ_two, compFin_apply_graft 1 f θ (cor e₁) (lc e₂ e₃) _ rfl,
    compFin_apply_eq_zero 0 f θ _ (fun t₁ t₂ h => ?_)]
  · simp
  · obtain ⟨x, rfl⟩ := eq_cor t₁
    rw [Fin.val_zero, graft_cor_zero] at h
    simp [rl] at h

lemma sstar12_apply_rr :
    sstar (R := R) (j := 1) (k := 2) f θ (rr e₁ e₂ e₃)
      = compFin (R := R) (P := Q) (1 : Fin 2) (f (cor e₁)) (θ (rc e₂ e₃)) := by
  rw [sstar_apply, Fin.sum_univ_two, compFin_apply_graft 1 f θ (cor e₁) (rc e₂ e₃) _ rfl,
    compFin_apply_eq_zero 0 f θ _ (fun t₁ t₂ h => ?_)]
  · simp
  · obtain ⟨x, rfl⟩ := eq_cor t₁
    rw [Fin.val_zero, graft_cor_zero] at h
    simp [rr] at h

private lemma graft_lc (x y e : E) (i : ℕ) :
    (lc x y).1.graft i (cor e).1 = if i = 0 then (ll x y e).1 else if i = 1 then (lr x y e).1
      else (bl x y e).1 := by
  rcases i with _ | _ | i <;> simp [lc, cor, corolla, graft_node, ll, lr, bl]

private lemma graft_rc (x y e : E) (i : ℕ) :
    (rc x y).1.graft i (cor e).1 = if i = 0 then (bl x e y).1 else if i = 1 then (rl x y e).1
      else (rr x y e).1 := by
  rcases i with _ | _ | i <;> simp [rc, cor, corolla, graft_node, bl, rl, rr]

/-- The factorizations of a three-vertex tree at a cherry. -/
private lemma factor_cherry (i : ℕ) (t₁ : OfArity E 3) (e : E) :
    (∃ x y, t₁ = lc x y ∧ t₁.1.graft i (cor e).1 = if i = 0 then (ll x y e).1
      else if i = 1 then (lr x y e).1 else (bl x y e).1) ∨
    (∃ x y, t₁ = rc x y ∧ t₁.1.graft i (cor e).1 = if i = 0 then (bl x e y).1
      else if i = 1 then (rl x y e).1 else (rr x y e).1) := by
  rcases eq_lc_or_rc t₁ with ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩
  · exact Or.inl ⟨x, y, rfl, graft_lc x y e i⟩
  · exact Or.inr ⟨x, y, rfl, graft_rc x y e i⟩

lemma sstar21_apply_ll :
    sstar (R := R) (j := 2) (k := 1) θ f (ll e₁ e₂ e₃)
      = compFin (R := R) (P := Q) (0 : Fin 3) (θ (lc e₁ e₂)) (f (cor e₃)) := by
  rw [sstar_apply, Fin.sum_univ_three, compFin_apply_graft 0 θ f (lc e₁ e₂) (cor e₃) _ rfl]
  rw [compFin_apply_eq_zero 1 θ f _ (fun t₁ t₂ h => ?_),
    compFin_apply_eq_zero 2 θ f _ (fun t₁ t₂ h => ?_)]
  · simp
  all_goals
    obtain ⟨e, rfl⟩ := eq_cor t₂
    rcases factor_cherry _ t₁ e with ⟨x, y, rfl, hg⟩ | ⟨x, y, rfl, hg⟩ <;>
      rw [hg] at h <;> simp [ll, lr, bl, rl, rr] at h

lemma sstar21_apply_lr :
    sstar (R := R) (j := 2) (k := 1) θ f (lr e₁ e₂ e₃)
      = -compFin (R := R) (P := Q) (1 : Fin 3) (θ (lc e₁ e₂)) (f (cor e₃)) := by
  rw [sstar_apply, Fin.sum_univ_three, compFin_apply_graft 1 θ f (lc e₁ e₂) (cor e₃) _ rfl]
  rw [compFin_apply_eq_zero 0 θ f _ (fun t₁ t₂ h => ?_),
    compFin_apply_eq_zero 2 θ f _ (fun t₁ t₂ h => ?_)]
  · simp
  all_goals
    obtain ⟨e, rfl⟩ := eq_cor t₂
    rcases factor_cherry _ t₁ e with ⟨x, y, rfl, hg⟩ | ⟨x, y, rfl, hg⟩ <;>
      rw [hg] at h <;> simp [ll, lr, bl, rl, rr] at h

lemma sstar21_apply_bl :
    sstar (R := R) (j := 2) (k := 1) θ f (bl e₁ e₂ e₃)
      = compFin (R := R) (P := Q) (0 : Fin 3) (θ (rc e₁ e₃)) (f (cor e₂))
        + compFin (R := R) (P := Q) (2 : Fin 3) (θ (lc e₁ e₂)) (f (cor e₃)) := by
  rw [sstar_apply, Fin.sum_univ_three, compFin_apply_graft 0 θ f (rc e₁ e₃) (cor e₂) _ rfl,
    compFin_apply_graft 2 θ f (lc e₁ e₂) (cor e₃) _ rfl]
  rw [compFin_apply_eq_zero 1 θ f _ (fun t₁ t₂ h => ?_)]
  · simp
  · obtain ⟨e, rfl⟩ := eq_cor t₂
    rcases factor_cherry _ t₁ e with ⟨x, y, rfl, hg⟩ | ⟨x, y, rfl, hg⟩ <;>
      rw [hg] at h <;> simp [ll, lr, bl, rl, rr] at h

lemma sstar21_apply_rl :
    sstar (R := R) (j := 2) (k := 1) θ f (rl e₁ e₂ e₃)
      = -compFin (R := R) (P := Q) (1 : Fin 3) (θ (rc e₁ e₂)) (f (cor e₃)) := by
  rw [sstar_apply, Fin.sum_univ_three, compFin_apply_graft 1 θ f (rc e₁ e₂) (cor e₃) _ rfl]
  rw [compFin_apply_eq_zero 0 θ f _ (fun t₁ t₂ h => ?_),
    compFin_apply_eq_zero 2 θ f _ (fun t₁ t₂ h => ?_)]
  · simp
  all_goals
    obtain ⟨e, rfl⟩ := eq_cor t₂
    rcases factor_cherry _ t₁ e with ⟨x, y, rfl, hg⟩ | ⟨x, y, rfl, hg⟩ <;>
      rw [hg] at h <;> simp [ll, lr, bl, rl, rr] at h

lemma sstar21_apply_rr :
    sstar (R := R) (j := 2) (k := 1) θ f (rr e₁ e₂ e₃)
      = compFin (R := R) (P := Q) (2 : Fin 3) (θ (rc e₁ e₂)) (f (cor e₃)) := by
  rw [sstar_apply, Fin.sum_univ_three, compFin_apply_graft 2 θ f (rc e₁ e₂) (cor e₃) _ rfl]
  rw [compFin_apply_eq_zero 0 θ f _ (fun t₁ t₂ h => ?_),
    compFin_apply_eq_zero 1 θ f _ (fun t₁ t₂ h => ?_)]
  · simp
  all_goals
    obtain ⟨e, rfl⟩ := eq_cor t₂
    rcases factor_cherry _ t₁ e with ⟨x, y, rfl, hg⟩ | ⟨x, y, rfl, hg⟩ <;>
      rw [hg] at h <;> simp [ll, lr, bl, rl, rr] at h

end Three

/-! ## The brackets -/

/-- **The bracket of two weight-one cochains**: `⁅f, g⁆ₛ = f ⋆ₛ g + g ⋆ₛ f`. -/
lemma gbracket11_apply (f g : TConv R E Q 2) (t : OfArity E 3) :
    gbracket (R := R) (j := 1) (k := 1) f g t
      = sstar (R := R) (j := 1) (k := 1) f g t + sstar (R := R) (j := 1) (k := 1) g f t := by
  rw [gbracket, Pi.sub_apply, Pi.smul_apply, reindex_apply, reindex_self, OfArity.cast_self]
  norm_num

/-- **The bracket of a weight-one and a weight-two cochain**: `⁅f, θ⁆ₛ = f ⋆ₛ θ - θ ⋆ₛ f`. -/
lemma gbracket12_apply (f : TConv R E Q 2) (θ : TConv R E Q 3) (t : OfArity E 4) :
    gbracket (R := R) (j := 1) (k := 2) f θ t
      = sstar (R := R) (j := 1) (k := 2) f θ t - sstar (R := R) (j := 2) (k := 1) θ f t := by
  rw [gbracket, Pi.sub_apply, Pi.smul_apply, reindex_apply, reindex_self]
  norm_num

end TConv

end Operad
