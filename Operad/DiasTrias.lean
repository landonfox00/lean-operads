/-
# Presentations of the operads of dialgebras and of trialgebras

Loday's operad of associative dialgebras `Dias` is presented by two binary operations `⊣`, `⊢`
and five relations, and Loday and Ronco's operad of associative trialgebras `Trias` by three,
`⊣`, `⊢`, `⊥`, and eleven. Both operads are regular: they are the symmetrizations (`Operad.Reg`)
of their planar versions, the underlying planar operads of the pointed sets and of the nonempty
subsets (`Reg.hadamardIso`). So it suffices to present the planar versions, and the symmetric
presentations follow (`Reg.presIso`).

The planar presentations are proved by normal forms, in the calculus of operations of all arities
(`Operad.NSSetArr`):

* the generators are closed under rotation, every left comb of two of them being a right comb of
  two, so every operation of the presented operad is a right comb (`Arr.pres_isRComb`);
* after the first `⊣` of a right comb every later operation can be replaced by `⊣`, which makes
  the comb canonical (`DiasData.rcomb_norm`, `TriasData.rcomb_norm`);
* a canonical right comb is determined by the point, or by the set of marked inputs, that it
  evaluates to, and every point or nonempty set is the value of one.

The results are `PDias.presIso : NSPres DiasGen DiasRel ≅ toNSSet PointedSet`,
`PTrias.presIso : NSPres TriasGen TriasRel ≅ toNSSet NonemptySubset`, the symmetric
`DiasSet.presIso`, `TriasSet.presIso`, and the universal properties of the linear operads
`Dias.homEquiv`, `Trias.homEquiv`: a morphism out of `Dias R` (out of `Trias R`) into an operad
in modules is a choice of values of the generators satisfying the relations.
-/
import Operad.Regular

universe u v w

namespace Operad

open Sym NSSetOperad NSSetOperad.Arr

/-! ## Dialgebras -/

/-- The two operations of dialgebras: `x ⊣ y` points at `x`, `x ⊢ y` at `y`. -/
inductive DiOp
  | left
  | right
  deriving DecidableEq

/-- The generators of dialgebras. -/
inductive DiasGen : ℕ → Type
  | op (o : DiOp) : DiasGen 2

/-- The left comb `p ∘₁ q = p (q (·, ·), ·)`, as an expression. -/
def DiasGen.lc (p q : DiOp) : NSSyn DiasGen 3 :=
  NSSyn.comp 0 1 (NSSyn.gen (DiasGen.op p)) (NSSyn.gen (DiasGen.op q))

/-- The right comb `p ∘₂ q = p (·, q (·, ·))`, as an expression. -/
def DiasGen.rc (p q : DiOp) : NSSyn DiasGen 3 :=
  NSSyn.comp 1 0 (NSSyn.gen (DiasGen.op p)) (NSSyn.gen (DiasGen.op q))

open DiOp DiasGen in
/-- **The five relations of dialgebras**: `(x ⊣ y) ⊣ z = x ⊣ (y ⊣ z)`,
`(x ⊣ y) ⊣ z = x ⊣ (y ⊢ z)`, `(x ⊢ y) ⊣ z = x ⊢ (y ⊣ z)`, `(x ⊣ y) ⊢ z = x ⊢ (y ⊢ z)`,
`(x ⊢ y) ⊢ z = x ⊢ (y ⊢ z)`. -/
inductive DiasRel : ∀ n : ℕ, NSSyn DiasGen n → NSSyn DiasGen n → Prop
  | d1 : DiasRel 3 (lc left left) (rc left left)
  | d2 : DiasRel 3 (lc left left) (rc left right)
  | d3 : DiasRel 3 (lc left right) (rc right left)
  | d4 : DiasRel 3 (lc right left) (rc right right)
  | d5 : DiasRel 3 (lc right right) (rc right right)

/-- **Values of `⊣` and `⊢` satisfying the five relations**, in a planar set operad. -/
structure DiasData (S : ℕ → Type v) [NSSetOperad S] where
  /-- The values of the generators. -/
  op : DiOp → S 2
  d1 : leftComb (op .left) (op .left) = rightComb (op .left) (op .left)
  d2 : leftComb (op .left) (op .left) = rightComb (op .left) (op .right)
  d3 : leftComb (op .left) (op .right) = rightComb (op .right) (op .left)
  d4 : leftComb (op .right) (op .left) = rightComb (op .right) (op .right)
  d5 : leftComb (op .right) (op .right) = rightComb (op .right) (op .right)

namespace DiasData

variable {S : ℕ → Type v} [NSSetOperad S] (d : DiasData S)

/-- The generator values. -/
def gens : ∀ n, DiasGen n → S n := fun _ g => match g with | .op o => d.op o

lemma eval_lc (p q : DiOp) :
    (⟨3, NSSyn.eval d.gens (DiasGen.lc p q)⟩ : Arr S) = leftComb (d.op p) (d.op q) :=
  (leftComb_eq _ _).symm

lemma eval_rc (p q : DiOp) :
    (⟨3, NSSyn.eval d.gens (DiasGen.rc p q)⟩ : Arr S) = rightComb (d.op p) (d.op q) :=
  (rightComb_eq _ _).symm

/-- The generator values respect the relations. -/
theorem respects : NSPres.Respects DiasRel d.gens := by
  intro n x y h
  cases h
  · exact mk_eq_mk_iff.1 (by rw [eval_lc, eval_rc]; exact d.d1)
  · exact mk_eq_mk_iff.1 (by rw [eval_lc, eval_rc]; exact d.d2)
  · exact mk_eq_mk_iff.1 (by rw [eval_lc, eval_rc]; exact d.d3)
  · exact mk_eq_mk_iff.1 (by rw [eval_lc, eval_rc]; exact d.d4)
  · exact mk_eq_mk_iff.1 (by rw [eval_lc, eval_rc]; exact d.d5)

/-- **Rotation**: every left comb of two generators is a right comb of two. -/
theorem rotClosed : RotClosed (Set.range d.op) := by
  rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
  cases g <;> cases h
  · exact ⟨_, ⟨.left, rfl⟩, _, ⟨.left, rfl⟩, d.d1⟩
  · exact ⟨_, ⟨.right, rfl⟩, _, ⟨.left, rfl⟩, d.d3⟩
  · exact ⟨_, ⟨.right, rfl⟩, _, ⟨.right, rfl⟩, d.d4⟩
  · exact ⟨_, ⟨.right, rfl⟩, _, ⟨.right, rfl⟩, d.d5⟩

/-- **After a `⊣`, the next operation of a right comb can be taken to be `⊣`.** -/
lemma bin_left_right (o : DiOp) (X Y Z : Arr S) :
    bin (d.op .left) X (bin (d.op o) Y Z) = bin (d.op .left) X (bin (d.op .left) Y Z) := by
  cases o
  · rfl
  · exact (bin_right_of (d.d2.symm.trans d.d1) X Y Z)

end DiasData

namespace DiasData

/-- **The canonical form of a right comb**: every operation after the first `⊣` becomes `⊣`. -/
def norm : List DiOp → List DiOp
  | [] => []
  | .left :: l => .left :: List.replicate l.length .left
  | .right :: l => .right :: norm l

variable {S : ℕ → Type v} [NSSetOperad S] (d : DiasData S)

lemma bin_left_rcomb (X : Arr S) (l : List DiOp) :
    bin (d.op .left) X (rcomb (l.map d.op))
      = bin (d.op .left) X (rcomb ((List.replicate l.length DiOp.left).map d.op)) := by
  induction l generalizing X with
  | nil => rfl
  | cons o l ih =>
    rw [List.map_cons, rcomb_cons, d.bin_left_right, ih one, List.length_cons,
      List.replicate_succ, List.map_cons, rcomb_cons]

/-- **A right comb equals its canonical form**, in any operad with the relations. -/
theorem rcomb_norm (l : List DiOp) : rcomb (l.map d.op) = rcomb ((norm l).map d.op) := by
  induction l with
  | nil => rfl
  | cons o l ih =>
    cases o
    · rw [norm, List.map_cons, List.map_cons, rcomb_cons, rcomb_cons, bin_left_rcomb]
    · rw [norm, List.map_cons, List.map_cons, rcomb_cons, rcomb_cons, ih]

end DiasData

/-! ### The planar operad of pointed inputs -/

/-- **The planar operad of pointed inputs**, the planar version of dialgebras: an operation of
arity `n` is one of its inputs. -/
abbrev PDias : ℕ → Type := SetOperad.toNSSet PointedSet

namespace PDias

/-- An operation of arity `n`, as its point in `Fin n`. -/
def toFin {n : ℕ} (x : PDias n) : Fin n := x

/-- The point of an operation, as a number. -/
def pt (X : Arr PDias) : ℕ := (toFin X.2 : ℕ)

lemma pt_lt (X : Arr PDias) : pt X < X.1 := (toFin X.2).isLt

lemma pt_mk {n : ℕ} (x : PDias n) : pt ⟨n, x⟩ = (toFin x : ℕ) := rfl

/-- Operations are determined by their arity and point. -/
lemma arr_ext {X Y : Arr PDias} (h1 : X.1 = Y.1) (h2 : pt X = pt Y) : X = Y := by
  obtain ⟨n, x⟩ := X
  obtain ⟨m, y⟩ := Y
  obtain rfl : n = m := h1
  exact mk_eq_mk_iff.2 (Fin.ext h2)

@[simp] lemma pt_one : pt (one : Arr PDias) = 0 := rfl

/-- The point of a composite, in positional form. -/
lemma pt_mk_comp (a b : ℕ) {n : ℕ} (x : PDias (a + 1 + b)) (y : PDias n) :
    pt ⟨a + n + b, NSSetOperad.comp a b x y⟩ =
      if (toFin x : ℕ) < a then (toFin x : ℕ)
      else if (toFin x : ℕ) = a then a + (toFin y : ℕ) else (toFin x : ℕ) + n - 1 := by
  show ((insertEquiv a b n (PointedSet.comp (⟨a, by omega⟩ : Fin (a + 1 + b)) (toFin x)
    (toFin y)) : Fin _) : ℕ) = _
  by_cases h : toFin x = ⟨a, by omega⟩
  · rw [h, PointedSet.comp_self, insertEquiv_inr_val, if_neg (by simp), if_pos rfl]
  · have hx : (toFin x : ℕ) ≠ a := fun e => h (Fin.ext e)
    rw [PointedSet.comp_of_ne h, insertEquiv_inl_val, if_neg hx]

/-- **The point of a composite.** -/
lemma pt_comp (X : Arr PDias) {a : ℕ} (ha : a < X.1) (Y : Arr PDias) :
    pt (comp X a Y) = if pt X < a then pt X else if pt X = a then a + pt Y else pt X + Y.1 - 1 := by
  obtain ⟨b, x, rfl⟩ := exists_mk X ha
  obtain ⟨n, y⟩ := Y
  rw [mk_comp, pt_mk_comp]
  rfl

/-- **The point of a binary operation filled with `X` and `Y`.** -/
lemma pt_bin (g : PDias 2) (X Y : Arr PDias) :
    pt (bin g X Y) = if (toFin g : ℕ) = 0 then pt X else X.1 + pt Y := by
  have hZ : (comp ⟨2, g⟩ 1 Y).1 = Y.1 + 1 := by
    rw [comp_fst (by show 1 < 2; omega)]
    show 2 + Y.1 - 1 = Y.1 + 1
    omega
  have hg := (toFin g).isLt
  unfold bin
  rw [pt_comp _ (by omega), pt_comp _ (by show 1 < 2; omega), pt_mk]
  by_cases h0 : (toFin g : ℕ) = 0
  · simp [h0]
  · have h1 : (toFin g : ℕ) = 1 := by omega
    simp [h1]
    omega

end PDias

namespace DiOp

/-- The operation as a point of `{0, 1}`. -/
def toPD : DiOp → PDias 2
  | left => (0 : Fin 2)
  | right => (1 : Fin 2)

end DiOp

namespace PDias

/-- The point of a right comb. -/
def ptOf : List DiOp → ℕ
  | [] => 0
  | .left :: _ => 0
  | .right :: l => ptOf l + 1

lemma pt_rcomb (l : List DiOp) : pt (rcomb (l.map DiOp.toPD)) = ptOf l := by
  induction l with
  | nil => rfl
  | cons o l ih =>
    rw [List.map_cons, rcomb_cons, pt_bin]
    cases o
    · rfl
    · show (if (PDias.toFin (1 : Fin 2) : ℕ) = 0 then _ else _) = _
      rw [if_neg (by simp [PDias.toFin]), one_fst, ih, ptOf]
      omega

/-- **A canonical right comb is determined by its point.** -/
theorem norm_eq_of_ptOf_eq {l₁ l₂ : List DiOp} (h1 : l₁.length = l₂.length)
    (h2 : ptOf l₁ = ptOf l₂) : DiasData.norm l₁ = DiasData.norm l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons _ _ => simp at h1
  | cons o₁ l₁ ih =>
    cases l₂ with
    | nil => simp at h1
    | cons o₂ l₂ =>
      have hl : l₁.length = l₂.length := by simpa using h1
      cases o₁ <;> cases o₂
      · rw [DiasData.norm, DiasData.norm, hl]
      · simp [ptOf] at h2
      · simp [ptOf] at h2
      · rw [DiasData.norm, DiasData.norm, ih hl (by simpa [ptOf] using h2)]

/-- A right comb on `m + 1` inputs pointed at `k`. -/
def ofPt : ℕ → ℕ → List DiOp
  | 0, _ => []
  | m + 1, 0 => .left :: List.replicate m .left
  | m + 1, k + 1 => .right :: ofPt m k

lemma length_ofPt : ∀ (m k : ℕ), (ofPt m k).length = m
  | 0, _ => rfl
  | m + 1, 0 => by simp [ofPt]
  | m + 1, k + 1 => by simp [ofPt, length_ofPt m k]

lemma ptOf_ofPt : ∀ (m k : ℕ), k ≤ m → ptOf (ofPt m k) = k
  | 0, _, h => by simp only [Nat.le_zero] at h; subst h; rfl
  | m + 1, 0, _ => rfl
  | m + 1, k + 1, h => by simp [ofPt, ptOf, ptOf_ofPt m k (by omega)]

end PDias

section DiasPresentation

variable {p q p' q' : DiOp}

private lemma dias_lr (h : DiasRel 3 (DiasGen.lc p q) (DiasGen.rc p' q')) :
    leftComb (NSPres.gen (ρ := DiasRel) (DiasGen.op p)) (NSPres.gen (DiasGen.op q))
      = rightComb (NSPres.gen (DiasGen.op p')) (NSPres.gen (DiasGen.op q')) := by
  rw [leftComb_eq, rightComb_eq]
  exact congrArg (fun x => (⟨3, x⟩ : Arr (NSPres DiasGen DiasRel))) (NSPres.mk_eq_mk_of_rel h)

/-- **The generators of the presented operad** satisfy the relations. -/
def DiasData.pres : DiasData (NSPres DiasGen DiasRel) where
  op o := NSPres.gen (DiasGen.op o)
  d1 := dias_lr .d1
  d2 := dias_lr .d2
  d3 := dias_lr .d3
  d4 := dias_lr .d4
  d5 := dias_lr .d5

private lemma pd_eq {X Y : Arr PDias} (hX : X.1 = 3) (hY : Y.1 = 3) (h : PDias.pt X = PDias.pt Y) :
    X = Y :=
  PDias.arr_ext (hX.trans hY.symm) h

set_option linter.unusedSimpArgs false in
/-- **The points `0` and `1`** satisfy the relations. -/
def DiasData.points : DiasData PDias where
  op := DiOp.toPD
  d1 := by apply pd_eq <;> simp [leftComb, rightComb, PDias.pt_bin, DiOp.toPD, PDias.toFin]
  d2 := by apply pd_eq <;> simp [leftComb, rightComb, PDias.pt_bin, DiOp.toPD, PDias.toFin]
  d3 := by apply pd_eq <;> simp [leftComb, rightComb, PDias.pt_bin, DiOp.toPD, PDias.toFin]
  d4 := by apply pd_eq <;> simp [leftComb, rightComb, PDias.pt_bin, DiOp.toPD, PDias.toFin]
  d5 := by apply pd_eq <;> simp [leftComb, rightComb, PDias.pt_bin, DiOp.toPD, PDias.toFin]

end DiasPresentation

namespace PDias

/-- **The evaluation morphism**, sending `⊣` and `⊢` to the points `0` and `1`. -/
def ev : NSSetOperadHom (NSPres DiasGen DiasRel) PDias :=
  NSPres.lift DiasData.points.gens DiasData.points.respects

lemma map_ev_rcomb (l : List DiOp) :
    Arr.map ev (rcomb (l.map DiasData.pres.op)) = rcomb (l.map DiOp.toPD) := by
  rw [map_rcomb, List.map_map]
  rfl

private lemma exists_map_of_forall_mem_range {α β : Type*} {f : α → β} {l : List β}
    (h : ∀ x ∈ l, x ∈ Set.range f) : ∃ l' : List α, l = l'.map f := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons x l ih =>
    obtain ⟨a, rfl⟩ := h x (by simp)
    obtain ⟨l', rfl⟩ := ih (fun y hy => h y (by simp [hy]))
    exact ⟨a :: l', rfl⟩

/-- **Every operation of the presented operad is a right comb of generators.** -/
theorem exists_rcomb (X : Arr (NSPres DiasGen DiasRel)) :
    ∃ l : List DiOp, X = rcomb (l.map DiasData.pres.op) := by
  obtain ⟨l, hl, rfl⟩ := pres_isRComb DiasData.pres.rotClosed
    (fun n g => by cases g with | op o => exact isRComb_of_mem ⟨o, rfl⟩) X
  obtain ⟨l', rfl⟩ := exists_map_of_forall_mem_range hl
  exact ⟨l', rfl⟩

theorem map_ev_injective : Function.Injective (Arr.map ev) := by
  intro X Y h
  obtain ⟨l₁, rfl⟩ := exists_rcomb X
  obtain ⟨l₂, rfl⟩ := exists_rcomb Y
  rw [map_ev_rcomb, map_ev_rcomb] at h
  have h1 : l₁.length = l₂.length := by
    have := congrArg Sigma.fst h
    simpa using this
  have h2 : ptOf l₁ = ptOf l₂ := by rw [← pt_rcomb, ← pt_rcomb, h]
  rw [DiasData.pres.rcomb_norm l₁, DiasData.pres.rcomb_norm l₂, norm_eq_of_ptOf_eq h1 h2]

theorem map_ev_surjective : Function.Surjective (Arr.map ev) := by
  rintro ⟨n, x⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := (toFin x).2; omega⟩
  refine ⟨rcomb ((ofPt m (toFin x)).map DiasData.pres.op), ?_⟩
  rw [map_ev_rcomb]
  refine arr_ext (by simp [length_ofPt]) ?_
  rw [pt_rcomb, ptOf_ofPt _ _ (by have := (toFin x).2; omega)]
  rfl

theorem ev_bijective (n : ℕ) : Function.Bijective (ev.app n) := by
  constructor
  · intro x y h
    exact mk_eq_mk_iff.1 (map_ev_injective (a₁ := ⟨n, x⟩) (a₂ := ⟨n, y⟩)
      (by rw [map_mk, map_mk, h]))
  · intro s
    obtain ⟨⟨m, x⟩, hX⟩ := map_ev_surjective ⟨n, s⟩
    obtain rfl : m = n := congrArg Sigma.fst hX
    exact ⟨x, mk_eq_mk_iff.1 hX⟩

/-- **The planar operad of pointed inputs is presented by `⊣`, `⊢` and the five relations of
dialgebras.** -/
noncomputable def presIso : NSSetOperadIso (NSPres DiasGen DiasRel) PDias :=
  NSSetOperadIso.ofBijective ev ev_bijective

end PDias

/-- **Generator values respecting the relations are dialgebra data.** -/
def DiasData.equivRespects {S : ℕ → Type v} [NSSetOperad S] :
    {f : ∀ n, DiasGen n → S n // NSPres.Respects DiasRel f} ≃ DiasData S where
  toFun f :=
    { op := fun o => f.1 2 (.op o)
      d1 := by
        rw [leftComb_eq, rightComb_eq]
        exact mk_eq_mk_iff.2 (f.2 _ _ DiasRel.d1)
      d2 := by
        rw [leftComb_eq, rightComb_eq]
        exact mk_eq_mk_iff.2 (f.2 _ _ DiasRel.d2)
      d3 := by
        rw [leftComb_eq, rightComb_eq]
        exact mk_eq_mk_iff.2 (f.2 _ _ DiasRel.d3)
      d4 := by
        rw [leftComb_eq, rightComb_eq]
        exact mk_eq_mk_iff.2 (f.2 _ _ DiasRel.d4)
      d5 := by
        rw [leftComb_eq, rightComb_eq]
        exact mk_eq_mk_iff.2 (f.2 _ _ DiasRel.d5) }
  invFun d := ⟨d.gens, d.respects⟩
  left_inv f := Subtype.ext (funext fun _ => funext fun g => by cases g; rfl)
  right_inv _ := rfl

namespace DiasSet

/-- **Loday's presentation of dialgebras**: the set operad of dialgebras is presented by the
generators `⊣`, `⊢`, without symmetries, and the five relations with all their relabellings. -/
noncomputable def presIso : SetOperadIso (Pres DiasGen (symRel DiasRel)) DiasSet :=
  Reg.presIso.trans ((Reg.mapIso PDias.presIso).trans Reg.hadamardIso)

end DiasSet

namespace Dias

variable (R : Type u) [CommRing R] {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]

/-- **The universal property of `Dias`**: a morphism of operads in `R`-modules out of `Dias R` is a
choice of two binary operations `⊣`, `⊢` satisfying the five relations of dialgebras. -/
noncomputable def homEquiv :
    SymOperadHom R (Dias R) Q ≃ DiasData (SetOperad.toNSSet (Und R Q)) :=
  (linHomEquiv R).symm.trans <| DiasSet.presIso.precompEquiv.trans <| Pres.homEquiv.trans <|
    (Equiv.subtypeEquivRight (q := fun f =>
      NSPres.Respects (S := SetOperad.toNSSet (Und R Q)) DiasRel f)
        fun f => respects_symRel_iff DiasRel f).trans DiasData.equivRespects

end Dias

/-! ## Trialgebras -/

/-- The three operations of trialgebras: `x ⊣ y` marks `x`, `x ⊢ y` marks `y`, `x ⊥ y` both. -/
inductive TriOp
  | left
  | right
  | middle
  deriving DecidableEq

namespace TriOp

/-- Whether the first input is marked. -/
def fst : TriOp → Bool
  | left => true
  | right => false
  | middle => true

/-- Whether the second input is marked. -/
def snd : TriOp → Bool
  | left => false
  | right => true
  | middle => true

end TriOp

/-- The generators of trialgebras. -/
inductive TriasGen : ℕ → Type
  | op (o : TriOp) : TriasGen 2

/-- The left comb `p ∘₁ q = p (q (·, ·), ·)`, as an expression. -/
def TriasGen.lc (p q : TriOp) : NSSyn TriasGen 3 :=
  NSSyn.comp 0 1 (NSSyn.gen (TriasGen.op p)) (NSSyn.gen (TriasGen.op q))

/-- The right comb `p ∘₂ q = p (·, q (·, ·))`, as an expression. -/
def TriasGen.rc (p q : TriOp) : NSSyn TriasGen 3 :=
  NSSyn.comp 1 0 (NSSyn.gen (TriasGen.op p)) (NSSyn.gen (TriasGen.op q))

open TriOp TriasGen in
/-- **The eleven relations of trialgebras** (Loday–Ronco):
`(x ⊣ y) ⊣ z = x ⊣ (y ⊣ z)`, `(x ⊣ y) ⊣ z = x ⊣ (y ⊢ z)`, `(x ⊢ y) ⊣ z = x ⊢ (y ⊣ z)`,
`(x ⊣ y) ⊢ z = x ⊢ (y ⊢ z)`, `(x ⊢ y) ⊢ z = x ⊢ (y ⊢ z)`, `(x ⊣ y) ⊣ z = x ⊣ (y ⊥ z)`,
`(x ⊥ y) ⊣ z = x ⊥ (y ⊣ z)`, `(x ⊣ y) ⊥ z = x ⊥ (y ⊢ z)`, `(x ⊢ y) ⊥ z = x ⊢ (y ⊥ z)`,
`(x ⊥ y) ⊢ z = x ⊢ (y ⊢ z)`, `(x ⊥ y) ⊥ z = x ⊥ (y ⊥ z)`. -/
inductive TriasRel : ∀ n : ℕ, NSSyn TriasGen n → NSSyn TriasGen n → Prop
  | t1 : TriasRel 3 (lc left left) (rc left left)
  | t2 : TriasRel 3 (lc left left) (rc left right)
  | t3 : TriasRel 3 (lc left right) (rc right left)
  | t4 : TriasRel 3 (lc right left) (rc right right)
  | t5 : TriasRel 3 (lc right right) (rc right right)
  | t6 : TriasRel 3 (lc left left) (rc left middle)
  | t7 : TriasRel 3 (lc left middle) (rc middle left)
  | t8 : TriasRel 3 (lc middle left) (rc middle right)
  | t9 : TriasRel 3 (lc middle right) (rc right middle)
  | t10 : TriasRel 3 (lc right middle) (rc right right)
  | t11 : TriasRel 3 (lc middle middle) (rc middle middle)

/-- **Values of `⊣`, `⊢`, `⊥` satisfying the eleven relations**, in a planar set operad. -/
structure TriasData (S : ℕ → Type v) [NSSetOperad S] where
  /-- The values of the generators. -/
  op : TriOp → S 2
  t1 : leftComb (op .left) (op .left) = rightComb (op .left) (op .left)
  t2 : leftComb (op .left) (op .left) = rightComb (op .left) (op .right)
  t3 : leftComb (op .left) (op .right) = rightComb (op .right) (op .left)
  t4 : leftComb (op .right) (op .left) = rightComb (op .right) (op .right)
  t5 : leftComb (op .right) (op .right) = rightComb (op .right) (op .right)
  t6 : leftComb (op .left) (op .left) = rightComb (op .left) (op .middle)
  t7 : leftComb (op .left) (op .middle) = rightComb (op .middle) (op .left)
  t8 : leftComb (op .middle) (op .left) = rightComb (op .middle) (op .right)
  t9 : leftComb (op .middle) (op .right) = rightComb (op .right) (op .middle)
  t10 : leftComb (op .right) (op .middle) = rightComb (op .right) (op .right)
  t11 : leftComb (op .middle) (op .middle) = rightComb (op .middle) (op .middle)

namespace TriasData

variable {S : ℕ → Type v} [NSSetOperad S] (d : TriasData S)

/-- The generator values. -/
def gens : ∀ n, TriasGen n → S n := fun _ g => match g with | .op o => d.op o

lemma eval_lc (p q : TriOp) :
    (⟨3, NSSyn.eval d.gens (TriasGen.lc p q)⟩ : Arr S) = leftComb (d.op p) (d.op q) :=
  (leftComb_eq _ _).symm

lemma eval_rc (p q : TriOp) :
    (⟨3, NSSyn.eval d.gens (TriasGen.rc p q)⟩ : Arr S) = rightComb (d.op p) (d.op q) :=
  (rightComb_eq _ _).symm

/-- The generator values respect the relations. -/
theorem respects : NSPres.Respects TriasRel d.gens := by
  intro n x y h
  cases h
  · exact mk_eq_mk_iff.1 (by rw [eval_lc, eval_rc]; exact d.t1)
  · exact mk_eq_mk_iff.1 (by rw [eval_lc, eval_rc]; exact d.t2)
  · exact mk_eq_mk_iff.1 (by rw [eval_lc, eval_rc]; exact d.t3)
  · exact mk_eq_mk_iff.1 (by rw [eval_lc, eval_rc]; exact d.t4)
  · exact mk_eq_mk_iff.1 (by rw [eval_lc, eval_rc]; exact d.t5)
  · exact mk_eq_mk_iff.1 (by rw [eval_lc, eval_rc]; exact d.t6)
  · exact mk_eq_mk_iff.1 (by rw [eval_lc, eval_rc]; exact d.t7)
  · exact mk_eq_mk_iff.1 (by rw [eval_lc, eval_rc]; exact d.t8)
  · exact mk_eq_mk_iff.1 (by rw [eval_lc, eval_rc]; exact d.t9)
  · exact mk_eq_mk_iff.1 (by rw [eval_lc, eval_rc]; exact d.t10)
  · exact mk_eq_mk_iff.1 (by rw [eval_lc, eval_rc]; exact d.t11)

/-- **Rotation**: every left comb of two generators is a right comb of two. -/
theorem rotClosed : RotClosed (Set.range d.op) := by
  rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
  cases g <;> cases h
  · exact ⟨_, ⟨.left, rfl⟩, _, ⟨.left, rfl⟩, d.t1⟩
  · exact ⟨_, ⟨.right, rfl⟩, _, ⟨.left, rfl⟩, d.t3⟩
  · exact ⟨_, ⟨.middle, rfl⟩, _, ⟨.left, rfl⟩, d.t7⟩
  · exact ⟨_, ⟨.right, rfl⟩, _, ⟨.right, rfl⟩, d.t4⟩
  · exact ⟨_, ⟨.right, rfl⟩, _, ⟨.right, rfl⟩, d.t5⟩
  · exact ⟨_, ⟨.right, rfl⟩, _, ⟨.right, rfl⟩, d.t10⟩
  · exact ⟨_, ⟨.middle, rfl⟩, _, ⟨.right, rfl⟩, d.t8⟩
  · exact ⟨_, ⟨.right, rfl⟩, _, ⟨.middle, rfl⟩, d.t9⟩
  · exact ⟨_, ⟨.middle, rfl⟩, _, ⟨.middle, rfl⟩, d.t11⟩

/-- **After a `⊣`, the next operation of a right comb can be taken to be `⊣`.** -/
lemma bin_left_right (o : TriOp) (X Y Z : Arr S) :
    bin (d.op .left) X (bin (d.op o) Y Z) = bin (d.op .left) X (bin (d.op .left) Y Z) := by
  cases o
  · rfl
  · exact bin_right_of (d.t2.symm.trans d.t1) X Y Z
  · exact bin_right_of (d.t6.symm.trans d.t1) X Y Z

/-- **The canonical form of a right comb**: every operation after the first `⊣` becomes `⊣`. -/
def norm : List TriOp → List TriOp
  | [] => []
  | .left :: l => .left :: List.replicate l.length .left
  | .right :: l => .right :: norm l
  | .middle :: l => .middle :: norm l

lemma bin_left_rcomb (X : Arr S) (l : List TriOp) :
    bin (d.op .left) X (rcomb (l.map d.op))
      = bin (d.op .left) X (rcomb ((List.replicate l.length TriOp.left).map d.op)) := by
  induction l generalizing X with
  | nil => rfl
  | cons o l ih =>
    rw [List.map_cons, rcomb_cons, d.bin_left_right, ih one, List.length_cons,
      List.replicate_succ, List.map_cons, rcomb_cons]

/-- **A right comb equals its canonical form**, in any operad with the relations. -/
theorem rcomb_norm (l : List TriOp) : rcomb (l.map d.op) = rcomb ((norm l).map d.op) := by
  induction l with
  | nil => rfl
  | cons o l ih =>
    cases o
    · rw [norm, List.map_cons, List.map_cons, rcomb_cons, rcomb_cons, bin_left_rcomb]
    · rw [norm, List.map_cons, List.map_cons, rcomb_cons, rcomb_cons, ih]
    · rw [norm, List.map_cons, List.map_cons, rcomb_cons, rcomb_cons, ih]

end TriasData

/-! ### The planar operad of nonempty subsets -/

/-- **The planar operad of nonempty subsets**, the planar version of trialgebras. -/
abbrev PTrias : ℕ → Type := SetOperad.toNSSet NonemptySubset

namespace PTrias

/-! ## Indicators of operations of all arities -/

/-- The indicator of an operation, extended by `false` beyond its arity. -/
def val (X : Arr PTrias) (k : ℕ) : Bool :=
  if h : k < X.1 then (X.2 : NonemptySubset (Fin X.1)).1 ⟨k, h⟩ else false

lemma val_of_le {X : Arr PTrias} {k : ℕ} (h : X.1 ≤ k) : val X k = false := by
  unfold val
  rw [dif_neg (by omega)]

lemma val_mk {n : ℕ} (x : PTrias n) (k : Fin n) :
    val ⟨n, x⟩ k = (x : NonemptySubset (Fin n)).1 k := by
  unfold val
  rw [dif_pos k.2]

/-- Operations are determined by their arity and indicator. -/
lemma arr_ext {X Y : Arr PTrias} (h1 : X.1 = Y.1) (h2 : ∀ k, val X k = val Y k) : X = Y := by
  obtain ⟨n, x⟩ := X
  obtain ⟨m, y⟩ := Y
  obtain rfl : n = m := h1
  refine mk_eq_mk_iff.2 (Subtype.ext (funext fun k => ?_))
  rw [← val_mk, ← val_mk, h2]

@[simp] lemma val_one (k : ℕ) : val one k = decide (k = 0) := by
  unfold val
  by_cases h : k = 0
  · subst h
    rfl
  · rw [dif_neg (by show ¬ k < 1; omega)]
    simp [h]

/-- The indicator of a composite, in positional form. -/
lemma val_mk_comp (a b : ℕ) {n : ℕ} (x : PTrias (a + 1 + b)) (y : PTrias n) (k : ℕ) :
    val ⟨a + n + b, NSSetOperad.comp a b x y⟩ k =
      if k < a then val ⟨_, x⟩ k
      else if k < a + n then val ⟨_, x⟩ a && val ⟨n, y⟩ (k - a)
      else val ⟨_, x⟩ (k - n + 1) := by
  by_cases hk : k < a + n + b
  · rw [val_mk _ ⟨k, hk⟩]
    show NonemptySubset.compFun (⟨a, by omega⟩ : Fin (a + 1 + b)) x.1 y.1
      ((insertEquiv a b n).symm ⟨k, hk⟩) = _
    by_cases h1 : k < a
    · have : (insertEquiv a b n).symm ⟨k, hk⟩ = Sum.inl ⟨⟨k, by omega⟩, fun e => by
          have := congrArg Fin.val e; simp only at this; omega⟩ := by
        simp [insertEquiv, h1]
      rw [this, if_pos h1, val_mk _ ⟨k, by omega⟩]
      rfl
    · by_cases h2 : k < a + n
      · have : (insertEquiv a b n).symm ⟨k, hk⟩ = Sum.inr ⟨k - a, by omega⟩ := by
          simp [insertEquiv, h1, h2]
        rw [this, if_neg h1, if_pos h2, val_mk _ ⟨a, by omega⟩, val_mk _ ⟨k - a, by omega⟩]
        rfl
      · have : (insertEquiv a b n).symm ⟨k, hk⟩ = Sum.inl ⟨⟨k - n + 1, by omega⟩, fun e => by
            have := congrArg Fin.val e; simp only at this; omega⟩ := by
          simp [insertEquiv, h1, h2]
        rw [this, if_neg h1, if_neg h2, val_mk _ ⟨k - n + 1, by omega⟩]
        rfl
  · rw [val_of_le (by show a + n + b ≤ k; omega)]
    have h1 : ¬ k < a := by omega
    rw [if_neg h1]
    by_cases h2 : k < a + n
    · rw [if_pos h2, val_of_le (X := ⟨n, y⟩) (by show n ≤ k - a; omega), Bool.and_false]
    · rw [if_neg h2, val_of_le (by show a + 1 + b ≤ k - n + 1; omega)]

/-- **The indicator of a composite.** -/
lemma val_comp (X : Arr PTrias) {a : ℕ} (ha : a < X.1) (Y : Arr PTrias) (k : ℕ) :
    val (comp X a Y) k =
      if k < a then val X k
      else if k < a + Y.1 then val X a && val Y (k - a)
      else val X (k - Y.1 + 1) := by
  obtain ⟨b, x, rfl⟩ := exists_mk X ha
  obtain ⟨n, y⟩ := Y
  rw [mk_comp, val_mk_comp]

/-- **The indicator of a binary operation filled with `X` and `Y`.** -/
lemma val_bin (g : PTrias 2) (X Y : Arr PTrias) (k : ℕ) :
    val (bin g X Y) k =
      if k < X.1 then val ⟨2, g⟩ 0 && val X k else val ⟨2, g⟩ 1 && val Y (k - X.1) := by
  have hZ : (comp ⟨2, g⟩ 1 Y).1 = Y.1 + 1 := by
    rw [comp_fst (by show 1 < 2; omega)]
    show 2 + Y.1 - 1 = Y.1 + 1
    omega
  unfold bin
  rw [val_comp _ (by omega)]
  simp only [Nat.not_lt_zero, if_false, Nat.zero_add, Nat.sub_zero]
  by_cases hk : k < X.1
  · rw [if_pos hk, if_pos hk, val_comp _ (by show 1 < 2; omega), if_pos (by omega)]
  · rw [if_neg hk, if_neg hk, val_comp _ (by show 1 < 2; omega), if_neg (by omega)]
    by_cases h2 : k - X.1 + 1 < 1 + Y.1
    · rw [if_pos h2, show k - X.1 + 1 - 1 = k - X.1 by omega]
    · rw [if_neg h2, val_of_le (by show 2 ≤ k - X.1 + 1 - Y.1 + 1; omega),
        val_of_le (X := Y) (by omega), Bool.and_false]


/-- The indicator of a right comb. -/
def marks : List TriOp → ℕ → Bool
  | [], k => decide (k = 0)
  | o :: _, 0 => o.fst
  | o :: l, k + 1 => o.snd && marks l k

lemma marks_of_lt {l : List TriOp} {k : ℕ} (h : l.length < k) : marks l k = false := by
  induction l generalizing k with
  | nil => simp only [marks, decide_eq_false_iff_not]; simp at h; omega
  | cons o l ih =>
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by simp at h; omega⟩
    simp only [marks, ih (show l.length < k by simp at h; omega), Bool.and_false]

lemma exists_marks (l : List TriOp) : ∃ k, marks l k = true := by
  induction l with
  | nil => exact ⟨0, rfl⟩
  | cons o l ih =>
    cases o
    · exact ⟨0, rfl⟩
    · obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, by simp [marks, TriOp.snd, hk]⟩
    · exact ⟨0, rfl⟩

/-- **A canonical right comb is determined by its indicator.** -/
theorem norm_eq_of_marks_eq {l₁ l₂ : List TriOp} (h1 : l₁.length = l₂.length)
    (h2 : ∀ k, marks l₁ k = marks l₂ k) : TriasData.norm l₁ = TriasData.norm l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons _ _ => simp at h1
  | cons o₁ l₁ ih =>
    cases l₂ with
    | nil => simp at h1
    | cons o₂ l₂ =>
      have h0 := h2 0
      have hs : ∀ k, (o₁.snd && marks l₁ k) = (o₂.snd && marks l₂ k) := fun k => h2 (k + 1)
      have hl : l₁.length = l₂.length := by simpa using h1
      cases o₁ <;> cases o₂
      · rw [TriasData.norm, TriasData.norm, hl]
      · simp [marks, TriOp.fst] at h0
      · obtain ⟨k, hk⟩ := exists_marks l₂
        simpa [TriOp.snd, hk] using (hs k).symm
      · simp [marks, TriOp.fst] at h0
      · rw [TriasData.norm, TriasData.norm, ih hl (fun k => by simpa [TriOp.snd] using hs k)]
      · simp [marks, TriOp.fst] at h0
      · obtain ⟨k, hk⟩ := exists_marks l₁
        simpa [TriOp.snd, hk] using hs k
      · simp [marks, TriOp.fst] at h0
      · rw [TriasData.norm, TriasData.norm, ih hl (fun k => by simpa [TriOp.snd] using hs k)]

/-- A right comb with a prescribed indicator on `{0, …, m}`. -/
def ofMarks : ℕ → (ℕ → Bool) → List TriOp
  | 0, _ => []
  | m + 1, s =>
    if s 0 then
      if (List.range (m + 1)).any (fun k => s (k + 1)) then
        .middle :: ofMarks m (fun k => s (k + 1))
      else .left :: List.replicate m .left
    else .right :: ofMarks m (fun k => s (k + 1))

lemma length_ofMarks (m : ℕ) (s : ℕ → Bool) : (ofMarks m s).length = m := by
  induction m generalizing s with
  | zero => rfl
  | succ m ih =>
    unfold ofMarks
    split_ifs <;> simp [ih]

/-- **Every nonempty indicator is the indicator of a right comb.** -/
theorem marks_ofMarks (m : ℕ) (s : ℕ → Bool) (hs : ∃ k ≤ m, s k = true) {k : ℕ} (hk : k ≤ m) :
    marks (ofMarks m s) k = s k := by
  induction m generalizing s k with
  | zero =>
    obtain rfl : k = 0 := by omega
    obtain ⟨j, hj, hsj⟩ := hs
    obtain rfl : j = 0 := by omega
    rw [hsj]
    rfl
  | succ m ih =>
    unfold ofMarks
    by_cases h0 : s 0 = true
    · rw [if_pos h0]
      by_cases hany : ((List.range (m + 1)).any (fun k => s (k + 1))) = true
      · rw [if_pos hany]
        rcases k with _ | k
        · rw [h0]; rfl
        · have hs' : ∃ j ≤ m, s (j + 1) = true := by
            obtain ⟨j, hj, hsj⟩ := List.any_eq_true.1 hany
            exact ⟨j, by simp at hj; omega, hsj⟩
          simp only [marks, TriOp.snd, Bool.true_and]
          exact ih (fun j => s (j + 1)) hs' (by omega)
      · rw [if_neg hany]
        rcases k with _ | k
        · rw [h0]; rfl
        · simp only [marks, TriOp.snd, Bool.false_and]
          have : ¬ s (k + 1) = true := fun hsk =>
            hany (List.any_eq_true.2 ⟨k, List.mem_range.2 (by omega), hsk⟩)
          simpa using this
    · rw [if_neg h0]
      rcases k with _ | k
      · simp only [marks, TriOp.fst]; simpa using h0
      · have hs' : ∃ j ≤ m, s (j + 1) = true := by
          obtain ⟨j, hj, hsj⟩ := hs
          rcases j with _ | j
          · exact absurd hsj h0
          · exact ⟨j, by omega, hsj⟩
        simp only [marks, TriOp.snd, Bool.true_and]
        exact ih (fun j => s (j + 1)) hs' (by omega)

end PTrias

namespace TriOp

/-- The operation as a subset of `{0, 1}`. -/
def toPT (o : TriOp) : PTrias 2 :=
  ⟨![o.fst, o.snd], by cases o <;> first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩⟩

@[simp] lemma val_toPT_zero (o : TriOp) : PTrias.val ⟨2, o.toPT⟩ 0 = o.fst := rfl

@[simp] lemma val_toPT_one (o : TriOp) : PTrias.val ⟨2, o.toPT⟩ 1 = o.snd := rfl

end TriOp

section TriasPresentation

variable {p q p' q' : TriOp}

private lemma trias_lr (h : TriasRel 3 (TriasGen.lc p q) (TriasGen.rc p' q')) :
    leftComb (NSPres.gen (ρ := TriasRel) (TriasGen.op p)) (NSPres.gen (TriasGen.op q))
      = rightComb (NSPres.gen (TriasGen.op p')) (NSPres.gen (TriasGen.op q')) := by
  rw [leftComb_eq, rightComb_eq]
  exact congrArg (fun x => (⟨3, x⟩ : Arr (NSPres TriasGen TriasRel))) (NSPres.mk_eq_mk_of_rel h)

/-- **The generators of the presented operad** satisfy the relations. -/
def TriasData.pres : TriasData (NSPres TriasGen TriasRel) where
  op o := NSPres.gen (TriasGen.op o)
  t1 := trias_lr .t1
  t2 := trias_lr .t2
  t3 := trias_lr .t3
  t4 := trias_lr .t4
  t5 := trias_lr .t5
  t6 := trias_lr .t6
  t7 := trias_lr .t7
  t8 := trias_lr .t8
  t9 := trias_lr .t9
  t10 := trias_lr .t10
  t11 := trias_lr .t11

private lemma pt_eq {X Y : Arr PTrias} (hX : X.1 = 3) (hY : Y.1 = 3)
    (h0 : PTrias.val X 0 = PTrias.val Y 0) (h1 : PTrias.val X 1 = PTrias.val Y 1)
    (h2 : PTrias.val X 2 = PTrias.val Y 2) : X = Y := by
  refine PTrias.arr_ext (hX.trans hY.symm) fun k => ?_
  rcases k with _ | _ | _ | k
  · exact h0
  · exact h1
  · exact h2
  · rw [PTrias.val_of_le (by omega), PTrias.val_of_le (by omega)]

set_option linter.unusedSimpArgs false in
/-- **The subsets `{0}`, `{1}`, `{0, 1}`** satisfy the relations. -/
def TriasData.subsets : TriasData PTrias where
  op := TriOp.toPT
  t1 := by apply pt_eq <;> simp [leftComb, rightComb, PTrias.val_bin, TriOp.fst, TriOp.snd]
  t2 := by apply pt_eq <;> simp [leftComb, rightComb, PTrias.val_bin, TriOp.fst, TriOp.snd]
  t3 := by apply pt_eq <;> simp [leftComb, rightComb, PTrias.val_bin, TriOp.fst, TriOp.snd]
  t4 := by apply pt_eq <;> simp [leftComb, rightComb, PTrias.val_bin, TriOp.fst, TriOp.snd]
  t5 := by apply pt_eq <;> simp [leftComb, rightComb, PTrias.val_bin, TriOp.fst, TriOp.snd]
  t6 := by apply pt_eq <;> simp [leftComb, rightComb, PTrias.val_bin, TriOp.fst, TriOp.snd]
  t7 := by apply pt_eq <;> simp [leftComb, rightComb, PTrias.val_bin, TriOp.fst, TriOp.snd]
  t8 := by apply pt_eq <;> simp [leftComb, rightComb, PTrias.val_bin, TriOp.fst, TriOp.snd]
  t9 := by apply pt_eq <;> simp [leftComb, rightComb, PTrias.val_bin, TriOp.fst, TriOp.snd]
  t10 := by apply pt_eq <;> simp [leftComb, rightComb, PTrias.val_bin, TriOp.fst, TriOp.snd]
  t11 := by apply pt_eq <;> simp [leftComb, rightComb, PTrias.val_bin, TriOp.fst, TriOp.snd]

end TriasPresentation

namespace PTrias

/-- **The evaluation morphism**, sending `⊣`, `⊢`, `⊥` to the subsets `{0}`, `{1}`, `{0, 1}`. -/
def ev : NSSetOperadHom (NSPres TriasGen TriasRel) PTrias :=
  NSPres.lift TriasData.subsets.gens TriasData.subsets.respects

lemma val_rcomb (l : List TriOp) (k : ℕ) : val (rcomb (l.map TriOp.toPT)) k = marks l k := by
  induction l generalizing k with
  | nil => rw [List.map_nil, rcomb_nil, val_one]; rfl
  | cons o l ih =>
    rw [List.map_cons, rcomb_cons, val_bin]
    rcases k with _ | k
    · simp [marks]
    · simp only [one_fst, show ¬ k + 1 < 1 by omega, if_false, TriOp.val_toPT_one,
        Nat.add_sub_cancel, ih]
      rfl

lemma map_ev_rcomb (l : List TriOp) :
    Arr.map ev (rcomb (l.map TriasData.pres.op)) = rcomb (l.map TriOp.toPT) := by
  rw [map_rcomb, List.map_map]
  rfl

private lemma exists_map_of_forall_mem_range {α β : Type*} {f : α → β} {l : List β}
    (h : ∀ x ∈ l, x ∈ Set.range f) : ∃ l' : List α, l = l'.map f := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons x l ih =>
    obtain ⟨a, rfl⟩ := h x (by simp)
    obtain ⟨l', rfl⟩ := ih (fun y hy => h y (by simp [hy]))
    exact ⟨a :: l', rfl⟩

/-- **Every operation of the presented operad is a right comb of generators.** -/
theorem exists_rcomb (X : Arr (NSPres TriasGen TriasRel)) :
    ∃ l : List TriOp, X = rcomb (l.map TriasData.pres.op) := by
  obtain ⟨l, hl, rfl⟩ := pres_isRComb TriasData.pres.rotClosed
    (fun n g => by cases g with | op o => exact isRComb_of_mem ⟨o, rfl⟩) X
  obtain ⟨l', rfl⟩ := exists_map_of_forall_mem_range hl
  exact ⟨l', rfl⟩

theorem map_ev_injective : Function.Injective (Arr.map ev) := by
  intro X Y h
  obtain ⟨l₁, rfl⟩ := exists_rcomb X
  obtain ⟨l₂, rfl⟩ := exists_rcomb Y
  rw [map_ev_rcomb, map_ev_rcomb] at h
  have h1 : l₁.length = l₂.length := by
    have := congrArg Sigma.fst h
    simpa using this
  have h2 : ∀ k, marks l₁ k = marks l₂ k := fun k => by rw [← val_rcomb, ← val_rcomb, h]
  rw [TriasData.pres.rcomb_norm l₁, TriasData.pres.rcomb_norm l₂, norm_eq_of_marks_eq h1 h2]

theorem map_ev_surjective : Function.Surjective (Arr.map ev) := by
  rintro ⟨n, x⟩
  obtain ⟨a, ha⟩ := (x : NonemptySubset (Fin n)).2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := a.2; omega⟩
  have hs : ∃ k ≤ m, val ⟨m + 1, x⟩ k = true :=
    ⟨a, by have := a.2; omega, by rw [val_mk]; exact ha⟩
  refine ⟨rcomb ((ofMarks m (val ⟨m + 1, x⟩)).map TriasData.pres.op), ?_⟩
  rw [map_ev_rcomb]
  refine arr_ext (by simp [length_ofMarks]) fun k => ?_
  rw [val_rcomb]
  by_cases hk : k ≤ m
  · exact marks_ofMarks m _ hs hk
  · rw [marks_of_lt (by rw [length_ofMarks]; omega), val_of_le (by show m + 1 ≤ k; omega)]

theorem ev_bijective (n : ℕ) : Function.Bijective (ev.app n) := by
  constructor
  · intro x y h
    exact mk_eq_mk_iff.1 (map_ev_injective (a₁ := ⟨n, x⟩) (a₂ := ⟨n, y⟩)
      (by rw [map_mk, map_mk, h]))
  · intro s
    obtain ⟨⟨m, x⟩, hX⟩ := map_ev_surjective ⟨n, s⟩
    obtain rfl : m = n := congrArg Sigma.fst hX
    exact ⟨x, mk_eq_mk_iff.1 hX⟩

/-- **The planar operad of nonempty subsets is presented by `⊣`, `⊢`, `⊥` and the eleven
relations of trialgebras.** -/
noncomputable def presIso : NSSetOperadIso (NSPres TriasGen TriasRel) PTrias :=
  NSSetOperadIso.ofBijective ev ev_bijective

end PTrias

/-- **Generator values respecting the relations are trialgebra data.** -/
def TriasData.equivRespects {S : ℕ → Type v} [NSSetOperad S] :
    {f : ∀ n, TriasGen n → S n // NSPres.Respects TriasRel f} ≃ TriasData S where
  toFun f :=
    { op := fun o => f.1 2 (.op o)
      t1 := by rw [leftComb_eq, rightComb_eq]; exact mk_eq_mk_iff.2 (f.2 _ _ TriasRel.t1)
      t2 := by rw [leftComb_eq, rightComb_eq]; exact mk_eq_mk_iff.2 (f.2 _ _ TriasRel.t2)
      t3 := by rw [leftComb_eq, rightComb_eq]; exact mk_eq_mk_iff.2 (f.2 _ _ TriasRel.t3)
      t4 := by rw [leftComb_eq, rightComb_eq]; exact mk_eq_mk_iff.2 (f.2 _ _ TriasRel.t4)
      t5 := by rw [leftComb_eq, rightComb_eq]; exact mk_eq_mk_iff.2 (f.2 _ _ TriasRel.t5)
      t6 := by rw [leftComb_eq, rightComb_eq]; exact mk_eq_mk_iff.2 (f.2 _ _ TriasRel.t6)
      t7 := by rw [leftComb_eq, rightComb_eq]; exact mk_eq_mk_iff.2 (f.2 _ _ TriasRel.t7)
      t8 := by rw [leftComb_eq, rightComb_eq]; exact mk_eq_mk_iff.2 (f.2 _ _ TriasRel.t8)
      t9 := by rw [leftComb_eq, rightComb_eq]; exact mk_eq_mk_iff.2 (f.2 _ _ TriasRel.t9)
      t10 := by rw [leftComb_eq, rightComb_eq]; exact mk_eq_mk_iff.2 (f.2 _ _ TriasRel.t10)
      t11 := by rw [leftComb_eq, rightComb_eq]; exact mk_eq_mk_iff.2 (f.2 _ _ TriasRel.t11) }
  invFun d := ⟨d.gens, d.respects⟩
  left_inv f := Subtype.ext (funext fun _ => funext fun g => by cases g; rfl)
  right_inv _ := rfl

namespace TriasSet

/-- **Loday and Ronco's presentation of trialgebras**: the set operad of trialgebras is presented
by the generators `⊣`, `⊢`, `⊥`, without symmetries, and the eleven relations with all their
relabellings. -/
noncomputable def presIso : SetOperadIso (Pres TriasGen (symRel TriasRel)) TriasSet :=
  Reg.presIso.trans ((Reg.mapIso PTrias.presIso).trans Reg.hadamardIso)

end TriasSet

namespace Trias

variable (R : Type u) [CommRing R] {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]

/-- **The universal property of `Trias`**: a morphism of operads in `R`-modules out of `Trias R` is
a choice of three binary operations `⊣`, `⊢`, `⊥` satisfying the eleven relations of
trialgebras. -/
noncomputable def homEquiv :
    SymOperadHom R (Trias R) Q ≃ TriasData (SetOperad.toNSSet (Und R Q)) :=
  (linHomEquiv R).symm.trans <| TriasSet.presIso.precompEquiv.trans <| Pres.homEquiv.trans <|
    (Equiv.subtypeEquivRight (q := fun f =>
      NSPres.Respects (S := SetOperad.toNSSet (Und R Q)) TriasRel f)
        fun f => respects_symRel_iff TriasRel f).trans TriasData.equivRespects

end Trias

end Operad
