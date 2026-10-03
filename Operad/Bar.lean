/-
# The bar construction of a graded operad

Let `P` be a graded operad and `I` an ideal of `P`, for instance the augmentation ideal of an
augmented operad. **The bar construction** `B(P, I)` (`BarCoop`) is the cut cooperad of the free
graded operad on the suspension `s I` (`BarGen`) with the bar differential, which contracts the
edges of trees, merging the decorations of their ends by the composition of `P`:
`s a ⊛ᵢ s b = (-1)^{|a|} s (a ∘ᵢ b)`, relabelled to the positions of the merged vertex
(`barMerge`).

* The merge is compatible with the linearity relations of the free graded operad on `s I`
  (`barMerge_relHyp`), so **the bar differential descends** to the quotient (`Bar.d`).
* The merge is associative up to the linearity relations, by the associativity of `P` in the
  positions of the merged vertices (`assoc_seq_pos`, `assoc_par_pos`), in series and in parallel
  (`barMerge_assocHyp`), so **the bar differential squares to zero** (`Bar.d_d`).
* It is odd, commutes with relabellings, kills the counit and the coaugmentation (`Bar.d_one`),
  and is a coderivation of the cut cooperad: **the bar construction is a dg cooperad**
  (`Bar.instDGCooperad`).
-/
import Operad.BarSquare
import Operad.CofreeGrL
import Operad.DGCooperad

universe u v

namespace Operad

open Sym GerBV TreeOfArity FreeGr
open scoped TensorProduct

/-! ## Order isomorphisms onto standard orders -/

/-- **The positions of a composite**, for an input given as an element of `Fin n`. -/
noncomputable def posEquivF {n : ℕ} (q : Fin n) (l m : ℕ) (h : m + 1 = n + l) :
    Without (Fin n) q ⊕ Fin l ≃ Fin m :=
  (LinOrd.comp q (LinOrd.std n) (LinOrd.std l)).toRank.trans (finCongr (by
    rw [Fintype.card_sum, Reg.card_without, Fintype.card_fin, Fintype.card_fin]
    have := q.2
    omega))

lemma posEquiv_eq (n a l m : ℕ) (h : a < n ∧ m + 1 = n + l) :
    posEquiv n a l m h = posEquivF ⟨a, h.1⟩ l m h.2 := rfl

lemma map_posEquivF {n l m : ℕ} (q : Fin n) (h : m + 1 = n + l) :
    LinOrd.map (posEquivF q l m h) (LinOrd.comp q (LinOrd.std n) (LinOrd.std l))
      = LinOrd.std m :=
  map_toRank _ _

/-- **Order isomorphisms onto a standard order are unique.** -/
lemma equiv_eq_of_map {X : Type} [Fintype X] [DecidableEq X] {m : ℕ} (L : LinOrd X)
    {e₁ e₂ : X ≃ Fin m} (h₁ : LinOrd.map e₁ L = LinOrd.std m)
    (h₂ : LinOrd.map e₂ L = LinOrd.std m) : e₁ = e₂ := by
  have key : ∀ e : X ≃ Fin m, LinOrd.map e L = LinOrd.std m → ∀ x, (e x : ℕ) = L.rank x := by
    intro e he x
    have := LinOrd.rank_map e L (e x)
    rw [he, LinOrd.rank_std, Equiv.symm_apply_apply] at this
    exact this
  exact Equiv.ext fun x => Fin.ext ((key e₁ h₁ x).trans (key e₂ h₂ x).symm)

lemma posEquivF_inr {n l m : ℕ} (q : Fin n) (h : m + 1 = n + l) (j : Fin l) :
    (posEquivF q l m h (Sum.inr j) : ℕ) = q + j := by
  show (LinOrd.comp q (LinOrd.std n) (LinOrd.std l)).rank (Sum.inr j) = _
  rw [LinOrd.rank_comp_inr, LinOrd.rank_std, LinOrd.rank_std]

lemma posEquivF_inl_of_lt {n l m : ℕ} (q : Fin n) (h : m + 1 = n + l) (a : Without (Fin n) q)
    (ha : a.1 < q) : (posEquivF q l m h (Sum.inl a) : ℕ) = a.1 := by
  show (LinOrd.comp q (LinOrd.std n) (LinOrd.std l)).rank (Sum.inl a) = _
  rw [LinOrd.rank_comp_inl_of_lt _ _ _ _ ha, LinOrd.rank_std]

lemma posEquivF_inl_of_gt {n l m : ℕ} (q : Fin n) (h : m + 1 = n + l) (a : Without (Fin n) q)
    (ha : q < a.1) : (posEquivF q l m h (Sum.inl a) : ℕ) + 1 = a.1 + l := by
  show (LinOrd.comp q (LinOrd.std n) (LinOrd.std l)).rank (Sum.inl a) + 1 = _
  rw [LinOrd.rank_comp_inl_of_gt _ _ _ _ ha, LinOrd.rank_std, Fintype.card_fin]
  have : q.1 < a.1.1 := ha
  omega

/-! ## The species of an ideal -/

section IdealSp

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  (I : GrOperadIdeal R P)

/-- **The elements of an ideal**, as a graded linear species. -/
@[nolint unusedArguments]
def IdealSp (A : Type) [Fintype A] [DecidableEq A] : Type v := I.sub A

instance (A : Type) [Fintype A] [DecidableEq A] : AddCommGroup (IdealSp I A) :=
  inferInstanceAs (AddCommGroup (I.sub A))

instance (A : Type) [Fintype A] [DecidableEq A] : Module R (IdealSp I A) :=
  inferInstanceAs (Module R (I.sub A))

/-- An element of the ideal, as an operation. -/
def IdealSp.val {A : Type} [Fintype A] [DecidableEq A] (x : IdealSp I A) : P A :=
  (x : I.sub A).1

/-- An operation of the ideal, as an element. -/
def IdealSp.mk {A : Type} [Fintype A] [DecidableEq A] (x : P A) (hx : x ∈ I.sub A) :
    IdealSp I A :=
  (⟨x, hx⟩ : I.sub A)

@[simp] lemma IdealSp.val_mk {A : Type} [Fintype A] [DecidableEq A] (x : P A)
    (hx : x ∈ I.sub A) : IdealSp.val I (IdealSp.mk I x hx) = x := rfl

lemma IdealSp.mem {A : Type} [Fintype A] [DecidableEq A] (x : IdealSp I A) :
    IdealSp.val I x ∈ I.sub A := (x : I.sub A).2

lemma IdealSp.ext {A : Type} [Fintype A] [DecidableEq A] {x y : IdealSp I A}
    (h : IdealSp.val I x = IdealSp.val I y) : x = y :=
  Subtype.ext h

/-- **The elements of an ideal form a graded linear species.** -/
noncomputable instance IdealSp.instGrSpecies : GrSpecies R (IdealSp I) where
  map e := (GrOperad.map (R := R) e).restrict fun _ hx => I.map_mem e hx
  map_refl x := Subtype.ext (GrOperad.map_refl (R := R) (x : I.sub _).1)
  map_trans e f x := Subtype.ext (GrOperad.map_trans (R := R) e f (x : I.sub _).1)
  par b := (GrOperad.par (R := R) b).restrict fun _ hx => I.par_mem b hx
  par_add x := Subtype.ext (GrOperad.par_add (R := R) (x : I.sub _).1)
  par_par b b' x := by
    refine Subtype.ext ?_
    show GrOperad.par (R := R) b (GrOperad.par (R := R) b' (x : I.sub _).1) = _
    rw [GrOperad.par_par]
    split_ifs <;> rfl
  map_par e b x := Subtype.ext (GrOperad.map_par (R := R) e b (x : I.sub _).1)

variable {I}

@[simp] lemma IdealSp.val_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (e : A ≃ B) (x : IdealSp I A) :
    IdealSp.val I (SymSpecies.map (R := R) e x) = GrOperad.map (R := R) e (IdealSp.val I x) :=
  rfl

@[simp] lemma IdealSp.val_par {A : Type} [Fintype A] [DecidableEq A] (b : Bool)
    (x : IdealSp I A) :
    IdealSp.val I (GrSpecies.par (R := R) b x) = GrOperad.par (R := R) b (IdealSp.val I x) :=
  rfl

@[simp] lemma IdealSp.val_add {A : Type} [Fintype A] [DecidableEq A] (x y : IdealSp I A) :
    IdealSp.val I (x + y) = IdealSp.val I x + IdealSp.val I y := rfl

@[simp] lemma IdealSp.val_smul {A : Type} [Fintype A] [DecidableEq A] (c : R) (x : IdealSp I A) :
    IdealSp.val I (c • x) = c • IdealSp.val I x := rfl

@[simp] lemma IdealSp.val_zero {A : Type} [Fintype A] [DecidableEq A] :
    IdealSp.val I (0 : IdealSp I A) = 0 := rfl

end IdealSp

/-! ## The merge function of the bar construction -/

section Merge

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  (I : GrOperadIdeal R P)

/-- **The generators of the bar construction**: the suspension of the ideal. -/
abbrev BarGen := GrSpecies.Shift (IdealSp I) R

/-- **The decorations of bar trees**: homogeneous elements of the suspension of the ideal. -/
abbrev BarT (k : ℕ) := GrGen R (BarGen I) k

variable {I}

/-- The operation of `P` underlying a decoration. -/
def BarT.val {k : ℕ} (x : BarT I k) : P (Fin k) := IdealSp.val I x.1.1

lemma BarT.mem {k : ℕ} (x : BarT I k) : x.val ∈ I.sub (Fin k) := IdealSp.mem I x.1.1

/-- A decoration of parity `b` in the suspension has parity `!b` in `P`. -/
lemma BarT.par_val {k : ℕ} (x : BarT I k) : GrOperad.par (R := R) (!x.1.2) x.val = x.val :=
  congrArg (IdealSp.val I) x.2

variable (I) in
/-- **The value of merging two decorations**: `s a ⊛ⱼ s b = (-1)^{|a|} s (a ∘ⱼ b)`, in the
positions of the merged vertex. -/
noncomputable def barVal {k l : ℕ} (x : BarT I k) (q : Fin k) (y : BarT I l) (m : ℕ)
    (h : m + 1 = k + l) : P (Fin m) :=
  σ R (!x.1.2) • GrOperad.map (R := R) (posEquivF q l m h) (GrOperad.comp (R := R) q x.val y.val)

lemma barVal_mem {k l : ℕ} (x : BarT I k) (q : Fin k) (y : BarT I l) (m : ℕ)
    (h : m + 1 = k + l) : barVal I x q y m h ∈ I.sub (Fin m) :=
  Submodule.smul_mem _ _ (I.map_mem _ (I.comp_mem_left _ _ x.mem))

lemma par_barVal {k l : ℕ} (x : BarT I k) (q : Fin k) (y : BarT I l) (m : ℕ)
    (h : m + 1 = k + l) :
    GrOperad.par (R := R) (xor x.1.2 y.1.2) (barVal I x q y m h) = barVal I x q y m h := by
  unfold barVal
  rw [map_smul, ← GrOperad.map_par, ← x.par_val, ← y.par_val]
  have := GrOperad.comp_par (R := R) q (!x.1.2) (!y.1.2) x.val y.val
  rw [show xor (!x.1.2) (!y.1.2) = xor x.1.2 y.1.2 by cases x.1.2 <;> cases y.1.2 <;> rfl]
    at this
  rw [this]

variable (I) in
/-- **The merge function of the bar construction.** -/
noncomputable def barMerge : MergeFn (BarT I) := fun k l x j y m =>
  if h : j < k ∧ m + 1 = k + l then
    ⟨(IdealSp.mk I (barVal I x ⟨j, h.1⟩ y m h.2) (barVal_mem x _ y m h.2), !(xor x.1.2 y.1.2)),
      IdealSp.ext I (by
        show GrOperad.par (R := R) (!!(xor x.1.2 y.1.2)) (barVal I x ⟨j, h.1⟩ y m h.2) = _
        rw [Bool.not_not, par_barVal]
        rfl)⟩
  else ⟨(0, !(xor x.1.2 y.1.2)), map_zero _⟩

/-- **The bar merge adds the parities, plus one.** -/
lemma barMerge_odd : MergeFn.Odd (grGenPar R (BarGen I)) (barMerge I) := by
  intro k l x j y m
  unfold barMerge
  split_ifs <;> rfl

lemma barMerge_val {k l j m : ℕ} (x : BarT I k) (y : BarT I l) (h : j < k ∧ m + 1 = k + l) :
    (barMerge I k l x j y m).val = barVal I x ⟨j, h.1⟩ y m h.2 := by
  unfold barMerge
  rw [dif_pos h]
  rfl

lemma barMerge_par {k l j m : ℕ} (x : BarT I k) (y : BarT I l) :
    (barMerge I k l x j y m).1.2 = !(xor x.1.2 y.1.2) := by
  unfold barMerge
  split_ifs <;> rfl

end Merge

/-! ## Associativity in the positions of the merged vertex -/

section Positions

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]

lemma linOrd_map_trans {X Y Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z] (e : X ≃ Y) (f : Y ≃ Z) (L : LinOrd X) :
    LinOrd.map (e.trans f) L = LinOrd.map f (LinOrd.map e L) :=
  SetOperad.map_trans (S := fun A _ _ => LinOrd A) e f L

lemma linOrd_map_refl {X : Type} [Fintype X] [DecidableEq X] (L : LinOrd X) :
    LinOrd.map (Equiv.refl X) L = L :=
  SetOperad.map_refl (S := fun A _ _ => LinOrd A) L

lemma map_symm_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) (x : P A) : GrOperad.map (R := R) e.symm (GrOperad.map (R := R) e x) = x := by
  rw [← GrOperad.map_trans, Equiv.self_trans_symm, GrOperad.map_refl]

/-- **Sequential associativity, in the positions of merged vertices.** -/
lemma assoc_seq_pos {kx lg lh m₁ m₂ m : ℕ} (p : Fin kx) (j : Fin lg) (q : Fin m₂)
    (h₁ : m₁ + 1 = lg + lh) (h₂ : m₂ + 1 = kx + lg) (h : m + 1 = kx + m₁)
    (h' : m + 1 = m₂ + lh) (hq : posEquivF p lg m₂ h₂ (Sum.inr j) = q) (a : P (Fin kx))
    (b : P (Fin lg)) (c : P (Fin lh)) :
    GrOperad.map (R := R) (posEquivF q lh m h') (GrOperad.comp (R := R) q
        (GrOperad.map (R := R) (posEquivF p lg m₂ h₂) (GrOperad.comp (R := R) p a b)) c)
      = GrOperad.map (R := R) (posEquivF p m₁ m h) (GrOperad.comp (R := R) p a
          (GrOperad.map (R := R) (posEquivF j lh m₁ h₁) (GrOperad.comp (R := R) j b c))) := by
  subst hq
  have h1 := GrOperad.map_comp (R := R) (P := P) (posEquivF p lg m₂ h₂) (Equiv.refl (Fin lh))
    (Sum.inr j) (GrOperad.comp (R := R) p a b) c
  rw [GrOperad.map_refl] at h1
  have h3 : GrOperad.comp (R := R) p a (GrOperad.map (R := R) (posEquivF j lh m₁ h₁)
        (GrOperad.comp (R := R) j b c))
      = GrOperad.map (R := R) (compEquiv (Equiv.refl (Fin kx)) (posEquivF j lh m₁ h₁) p)
          (GrOperad.comp (R := R) p a (GrOperad.comp (R := R) j b c)) := by
    have e := GrOperad.map_comp (R := R) (P := P) (Equiv.refl (Fin kx)) (posEquivF j lh m₁ h₁)
      p a (GrOperad.comp (R := R) j b c)
    rw [GrOperad.map_refl] at e
    exact e.symm
  have h2 : GrOperad.comp (R := R) (Sum.inr j) (GrOperad.comp (R := R) p a b) c
      = GrOperad.map (R := R) (seqEquiv p j (Fin lh)).symm
          (GrOperad.comp (R := R) p a (GrOperad.comp (R := R) j b c)) := by
    rw [← GrOperad.comp_assoc_seq (R := R) p j a b c, map_symm_map]
  rw [← h1, h2, h3, ← GrOperad.map_trans, ← GrOperad.map_trans]
  erw [← GrOperad.map_trans]
  congr 2
  apply equiv_eq_of_map
    (LinOrd.comp p (LinOrd.std kx) (LinOrd.comp j (LinOrd.std lg) (LinOrd.std lh)))
  · rw [linOrd_map_trans, linOrd_map_trans]
    have e1 : LinOrd.map (seqEquiv p j (Fin lh)).symm
        (LinOrd.comp p (LinOrd.std kx) (LinOrd.comp j (LinOrd.std lg) (LinOrd.std lh)))
        = LinOrd.comp (Sum.inr j) (LinOrd.comp p (LinOrd.std kx) (LinOrd.std lg))
            (LinOrd.std lh) := by
      have e := SetOperad.comp_assoc_seq (S := fun A _ _ => LinOrd A) p j (LinOrd.std kx)
        (LinOrd.std lg) (LinOrd.std lh)
      change LinOrd.map (seqEquiv p j (Fin lh)) (LinOrd.comp (Sum.inr j)
        (LinOrd.comp p (LinOrd.std kx) (LinOrd.std lg)) (LinOrd.std lh))
        = LinOrd.comp p (LinOrd.std kx) (LinOrd.comp j (LinOrd.std lg) (LinOrd.std lh)) at e
      rw [← e, ← linOrd_map_trans, Equiv.self_trans_symm, linOrd_map_refl]
    rw [e1]
    have e2 := SetOperad.map_comp (S := fun A _ _ => LinOrd A) (posEquivF p lg m₂ h₂)
      (Equiv.refl (Fin lh)) (Sum.inr j) (LinOrd.comp p (LinOrd.std kx) (LinOrd.std lg))
      (LinOrd.std lh)
    refine (congrArg (LinOrd.map _) e2).trans ?_
    show LinOrd.map _ (LinOrd.comp _ (LinOrd.map (posEquivF p lg m₂ h₂)
      (LinOrd.comp p (LinOrd.std kx) (LinOrd.std lg))) (LinOrd.map (Equiv.refl _)
        (LinOrd.std lh))) = _
    rw [map_posEquivF, linOrd_map_refl, map_posEquivF]
  · rw [linOrd_map_trans]
    have e3 := SetOperad.map_comp (S := fun A _ _ => LinOrd A) (Equiv.refl (Fin kx))
      (posEquivF j lh m₁ h₁) p (LinOrd.std kx) (LinOrd.comp j (LinOrd.std lg) (LinOrd.std lh))
    refine (congrArg (LinOrd.map _) e3).trans ?_
    show LinOrd.map _ (LinOrd.comp p (LinOrd.map (Equiv.refl _) (LinOrd.std kx))
      (LinOrd.map (posEquivF j lh m₁ h₁) (LinOrd.comp j (LinOrd.std lg) (LinOrd.std lh)))) = _
    rw [map_posEquivF, linOrd_map_refl, map_posEquivF]

/-- **Parallel associativity, in the positions of merged vertices.** -/
lemma assoc_par_pos {kx l₁ l₂ m₁ m₂ m : ℕ} {p₁ p₂ : Fin kx} (hp : p₁ < p₂) (q₁ : Fin m₂)
    (q₂ : Fin m₁) (h₁ : m₁ + 1 = kx + l₁) (h₂ : m₂ + 1 = kx + l₂) (h : m + 1 = m₁ + l₂)
    (h' : m + 1 = m₂ + l₁)
    (hq₂ : posEquivF p₁ l₁ m₁ h₁ (Sum.inl ⟨p₂, (Fin.ne_of_lt hp).symm⟩) = q₂)
    (hq₁ : posEquivF p₂ l₂ m₂ h₂ (Sum.inl ⟨p₁, Fin.ne_of_lt hp⟩) = q₁) (a : P (Fin kx))
    {r₁ r₂ : Bool} {b₁ : P (Fin l₁)} {b₂ : P (Fin l₂)} (hb₁ : GrOperad.par (R := R) r₁ b₁ = b₁)
    (hb₂ : GrOperad.par (R := R) r₂ b₂ = b₂) :
    GrOperad.map (R := R) (posEquivF q₂ l₂ m h) (GrOperad.comp (R := R) q₂
        (GrOperad.map (R := R) (posEquivF p₁ l₁ m₁ h₁) (GrOperad.comp (R := R) p₁ a b₁)) b₂)
      = σ R (r₁ && r₂) • GrOperad.map (R := R) (posEquivF q₁ l₁ m h') (GrOperad.comp (R := R) q₁
          (GrOperad.map (R := R) (posEquivF p₂ l₂ m₂ h₂) (GrOperad.comp (R := R) p₂ a b₂)) b₁) := by
  subst hq₁ hq₂
  have hne : p₁ ≠ p₂ := Fin.ne_of_lt hp
  have hL := GrOperad.map_comp (R := R) (P := P) (posEquivF p₁ l₁ m₁ h₁) (Equiv.refl (Fin l₂))
    (Sum.inl ⟨p₂, Ne.symm hne⟩) (GrOperad.comp (R := R) p₁ a b₁) b₂
  rw [GrOperad.map_refl] at hL
  have hR := GrOperad.map_comp (R := R) (P := P) (posEquivF p₂ l₂ m₂ h₂) (Equiv.refl (Fin l₁))
    (Sum.inl ⟨p₁, hne⟩) (GrOperad.comp (R := R) p₂ a b₂) b₁
  rw [GrOperad.map_refl] at hR
  have hpar : GrOperad.comp (R := R) (Sum.inl ⟨p₂, Ne.symm hne⟩)
        (GrOperad.comp (R := R) p₁ a b₁) b₂
      = σ R (r₁ && r₂) • GrOperad.map (R := R) (parEquiv hne (Fin l₁) (Fin l₂)).symm
          (GrOperad.comp (R := R) (Sum.inl ⟨p₁, hne⟩) (GrOperad.comp (R := R) p₂ a b₂) b₁) := by
    rw [← map_smul, ← GrOperad.comp_assoc_par (R := R) hne a hb₁ hb₂, map_symm_map]
  rw [← hL, ← hR, hpar, map_smul, map_smul, ← GrOperad.map_trans, ← GrOperad.map_trans,
    ← GrOperad.map_trans]
  congr 3
  apply equiv_eq_of_map (LinOrd.comp (Sum.inl ⟨p₁, hne⟩)
    (LinOrd.comp p₂ (LinOrd.std kx) (LinOrd.std l₂)) (LinOrd.std l₁))
  · rw [linOrd_map_trans, linOrd_map_trans]
    have e1 : LinOrd.map (parEquiv hne (Fin l₁) (Fin l₂)).symm (LinOrd.comp (Sum.inl ⟨p₁, hne⟩)
        (LinOrd.comp p₂ (LinOrd.std kx) (LinOrd.std l₂)) (LinOrd.std l₁))
        = LinOrd.comp (Sum.inl ⟨p₂, Ne.symm hne⟩)
            (LinOrd.comp p₁ (LinOrd.std kx) (LinOrd.std l₁)) (LinOrd.std l₂) := by
      have e := SetOperad.comp_assoc_par (S := fun A _ _ => LinOrd A) hne (LinOrd.std kx)
        (LinOrd.std l₁) (LinOrd.std l₂)
      change LinOrd.map (parEquiv hne (Fin l₁) (Fin l₂)) (LinOrd.comp (Sum.inl ⟨p₂, Ne.symm hne⟩)
        (LinOrd.comp p₁ (LinOrd.std kx) (LinOrd.std l₁)) (LinOrd.std l₂))
        = LinOrd.comp (Sum.inl ⟨p₁, hne⟩) (LinOrd.comp p₂ (LinOrd.std kx) (LinOrd.std l₂))
            (LinOrd.std l₁) at e
      rw [← e, ← linOrd_map_trans, Equiv.self_trans_symm, linOrd_map_refl]
    rw [e1]
    have e2 := SetOperad.map_comp (S := fun A _ _ => LinOrd A) (posEquivF p₁ l₁ m₁ h₁)
      (Equiv.refl (Fin l₂)) (Sum.inl ⟨p₂, Ne.symm hne⟩)
      (LinOrd.comp p₁ (LinOrd.std kx) (LinOrd.std l₁)) (LinOrd.std l₂)
    refine (congrArg (LinOrd.map _) e2).trans ?_
    show LinOrd.map _ (LinOrd.comp _ (LinOrd.map (posEquivF p₁ l₁ m₁ h₁)
      (LinOrd.comp p₁ (LinOrd.std kx) (LinOrd.std l₁))) (LinOrd.map (Equiv.refl _)
        (LinOrd.std l₂))) = _
    rw [map_posEquivF, linOrd_map_refl, map_posEquivF]
  · rw [linOrd_map_trans]
    have e3 := SetOperad.map_comp (S := fun A _ _ => LinOrd A) (posEquivF p₂ l₂ m₂ h₂)
      (Equiv.refl (Fin l₁)) (Sum.inl ⟨p₁, hne⟩)
      (LinOrd.comp p₂ (LinOrd.std kx) (LinOrd.std l₂)) (LinOrd.std l₁)
    refine (congrArg (LinOrd.map _) e3).trans ?_
    show LinOrd.map _ (LinOrd.comp _ (LinOrd.map (posEquivF p₂ l₂ m₂ h₂)
      (LinOrd.comp p₂ (LinOrd.std kx) (LinOrd.std l₂))) (LinOrd.map (Equiv.refl _)
        (LinOrd.std l₁))) = _
    rw [map_posEquivF, linOrd_map_refl, map_posEquivF]

end Positions

/-! ## The linearity relations -/

section LinRel

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]

local notation "𝒥" => GrOperadIdeal.span R (grLinRel R V)

lemma gen_eq_lgen {k : ℕ} (x : GrGen R V k) {v : V (Fin k)} {b : Bool} (hv : x.1.1 = v)
    (hb : x.1.2 = b) (h : GrSpecies.par (R := R) b v = v) :
    gen (R := R) (gp := grGenPar R V) x = lgen v b h := by
  obtain ⟨⟨v', b'⟩, h'⟩ := x
  subst hv hb
  rfl

/-- **Additivity of generators**, modulo the linearity relations. -/
lemma gen_sub_mem_add {k : ℕ} (x y z : GrGen R V k) (hy : y.1.2 = x.1.2) (hz : z.1.2 = x.1.2)
    (h : x.1.1 = y.1.1 + z.1.1) :
    gen (R := R) (gp := grGenPar R V) x - gen y - gen z ∈ (𝒥).sub (Fin k) := by
  have hy' : GrSpecies.par (R := R) x.1.2 y.1.1 = y.1.1 := by rw [← hy]; exact y.2
  have hz' : GrSpecies.par (R := R) x.1.2 z.1.1 = z.1.1 := by rw [← hz]; exact z.2
  refine GrOperadIdeal.subset_span k (Or.inl (Or.inl ⟨x.1.2, y.1.1, z.1.1, hy', hz', ?_⟩))
  rw [gen_eq_lgen x h rfl (by rw [map_add, hy', hz']), gen_eq_lgen y rfl hy hy',
    gen_eq_lgen z rfl hz hz']

/-- **Homogeneity of generators**, modulo the linearity relations. -/
lemma gen_sub_mem_smul {k : ℕ} (x y : GrGen R V k) (c : R) (hy : y.1.2 = x.1.2)
    (h : x.1.1 = c • y.1.1) :
    gen (R := R) (gp := grGenPar R V) x - c • gen y ∈ (𝒥).sub (Fin k) := by
  have hy' : GrSpecies.par (R := R) x.1.2 y.1.1 = y.1.1 := by rw [← hy]; exact y.2
  refine GrOperadIdeal.subset_span k (Or.inl (Or.inr ⟨x.1.2, c, y.1.1, hy', ?_⟩))
  rw [gen_eq_lgen x h rfl (by rw [map_smul, hy']), gen_eq_lgen y rfl hy hy']

/-- **Equivariance of generators**, modulo the linearity relations. -/
lemma map_gen_sub_mem {k : ℕ} (τ : Fin k ≃ Fin k) (x y : GrGen R V k) (hy : y.1.2 = x.1.2)
    (h : x.1.1 = SymSpecies.map (R := R) τ y.1.1) :
    GrOperad.map (R := R) τ (gen (R := R) (gp := grGenPar R V) y) - gen x ∈ (𝒥).sub (Fin k) := by
  have hy' : GrSpecies.par (R := R) x.1.2 y.1.1 = y.1.1 := by rw [← hy]; exact y.2
  refine GrOperadIdeal.subset_span k (Or.inr ⟨x.1.2, τ, y.1.1, hy', ?_⟩)
  rw [gen_eq_lgen x h rfl (by rw [← GrSpecies.map_par, hy']), gen_eq_lgen y rfl hy hy']

omit [GrSpecies R V] in
lemma unitCoeff_gen {T : ℕ → Type v} {gp : ∀ k, T k → Bool} {k : ℕ} (g : T k) :
    unitCoeff gp R (Fin k) (gen (R := R) (gp := gp) g) = 0 := by
  rw [FreeGr.gen, unitCoeff_bas]
  rfl

/-- **The bar differential kills the linearity relations**, whatever the merge function. -/
lemma barD_of_linRel (μ : MergeFn (GrGen R V)) {n : ℕ} {r : FreeGr R (grGenPar R V) (Fin n)}
    (hr : r ∈ grLinRel R V n) : barD μ (grGenPar R V) R (Fin n) r = 0 := by
  rcases hr with (⟨b, v, w, hv, hw, rfl⟩ | ⟨b, a, v, hv, rfl⟩) | ⟨b, τ, v, hv, rfl⟩
  · simp only [map_sub, lgen, barD_gen, sub_zero]
  · simp only [map_sub, map_smul, lgen, barD_gen, smul_zero, sub_zero]
  · rw [map_sub, ← map_barD]
    simp only [lgen, barD_gen, map_zero, sub_zero]

/-- The linearity relations have no unit component. -/
lemma unitCoeff_of_linRel {n : ℕ} {r : FreeGr R (grGenPar R V) (Fin n)}
    (hr : r ∈ grLinRel R V n) : unitCoeff (grGenPar R V) R (Fin n) r = 0 := by
  rcases hr with (⟨b, v, w, hv, hw, rfl⟩ | ⟨b, a, v, hv, rfl⟩) | ⟨b, τ, v, hv, rfl⟩
  · simp only [map_sub, lgen, unitCoeff_gen, sub_zero]
  · simp only [map_sub, map_smul, lgen, unitCoeff_gen, smul_zero, sub_zero]
  · simp only [map_sub, unitCoeff_map, lgen, unitCoeff_gen, sub_zero]

/-- The linearity relations are homogeneous. -/
lemma par_of_linRel {n : ℕ} {r : FreeGr R (grGenPar R V) (Fin n)} (hr : r ∈ grLinRel R V n) :
    ∃ b, GrOperad.par (R := R) b r = r := by
  have hg : ∀ {k : ℕ} (b : Bool) (v : V (Fin k)) (h : GrSpecies.par (R := R) b v = v),
      GrOperad.par (R := R) b (lgen v b h) = lgen v b h :=
    fun b v h => par_gen (R := R) (gp := grGenPar R V) ⟨(v, b), h⟩
  rcases hr with (⟨b, v, w, hv, hw, rfl⟩ | ⟨b, a, v, hv, rfl⟩) | ⟨b, τ, v, hv, rfl⟩
  · exact ⟨b, by rw [map_sub, map_sub, hg, hg, hg]⟩
  · exact ⟨b, by rw [map_sub, map_smul, hg, hg]⟩
  · exact ⟨b, by rw [map_sub, ← GrOperad.map_par, hg, hg]⟩

end LinRel

/-! ## The bar merge and the linearity relations -/

section BarRel

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {I : GrOperadIdeal R P}

local notation "𝒥" => GrOperadIdeal.span R (grLinRel R (BarGen I))

lemma BarT.eq_add {k : ℕ} {x y z : BarT I k} (h : x.val = y.val + z.val) :
    x.1.1 = y.1.1 + z.1.1 :=
  IdealSp.ext I h

lemma BarT.eq_smul {k : ℕ} {x y : BarT I k} (c : R) (h : x.val = c • y.val) :
    x.1.1 = c • y.1.1 :=
  IdealSp.ext I h

lemma BarT.eq_map {k : ℕ} {x y : BarT I k} (τ : Fin k ≃ Fin k)
    (h : x.val = GrOperad.map (R := R) τ y.val) : x.1.1 = SymSpecies.map (R := R) τ y.1.1 :=
  IdealSp.ext I h

lemma barVal_add_right {k l : ℕ} (x : BarT I k) (q : Fin k) {y z w : BarT I l}
    (h : y.val = z.val + w.val) (m : ℕ) (hm : m + 1 = k + l) :
    barVal I x q y m hm = barVal I x q z m hm + barVal I x q w m hm := by
  unfold barVal
  rw [h, map_add, map_add, smul_add]

lemma barVal_smul_right {k l : ℕ} (x : BarT I k) (q : Fin k) {y z : BarT I l} (c : R)
    (h : y.val = c • z.val) (m : ℕ) (hm : m + 1 = k + l) :
    barVal I x q y m hm = c • barVal I x q z m hm := by
  unfold barVal
  rw [h, map_smul, map_smul, smul_comm]

lemma barVal_add_left {k l : ℕ} {x y z : BarT I k} (hy : y.1.2 = x.1.2) (hz : z.1.2 = x.1.2)
    (h : x.val = y.val + z.val) (q : Fin k) (w : BarT I l) (m : ℕ) (hm : m + 1 = k + l) :
    barVal I x q w m hm = barVal I y q w m hm + barVal I z q w m hm := by
  unfold barVal
  rw [hy, hz, h, map_add, LinearMap.add_apply, map_add, smul_add]

lemma barVal_smul_left {k l : ℕ} {x y : BarT I k} (c : R) (hy : y.1.2 = x.1.2)
    (h : x.val = c • y.val) (q : Fin k) (w : BarT I l) (m : ℕ) (hm : m + 1 = k + l) :
    barVal I x q w m hm = c • barVal I y q w m hm := by
  unfold barVal
  rw [hy, h, LinearMap.map_smul₂, map_smul, smul_comm]

lemma barVal_map_right {k l : ℕ} (x : BarT I k) (q : Fin k) (τ : Fin l ≃ Fin l)
    {y z : BarT I l} (h : y.val = GrOperad.map (R := R) τ z.val) (m : ℕ) (hm : m + 1 = k + l) :
    barVal I x q y m hm = GrOperad.map (R := R) ((posEquivF q l m hm).symm.trans
      ((compEquiv (Equiv.refl (Fin k)) τ q).trans (posEquivF q l m hm))) (barVal I x q z m hm) := by
  unfold barVal
  rw [h, map_smul]
  congr 1
  have e := GrOperad.map_comp (R := R) (P := P) (Equiv.refl (Fin k)) τ q x.val z.val
  rw [GrOperad.map_refl] at e
  have e' : GrOperad.comp (R := R) q x.val (GrOperad.map (R := R) τ z.val)
      = GrOperad.map (R := R) (compEquiv (Equiv.refl (Fin k)) τ q)
          (GrOperad.comp (R := R) q x.val z.val) := e.symm
  rw [e', ← GrOperad.map_trans]
  erw [← GrOperad.map_trans]
  congr 2
  ext t
  simp

lemma barVal_map_left {k l : ℕ} (τ : Fin k ≃ Fin k) {x y : BarT I k} (hy : y.1.2 = x.1.2)
    (h : x.val = GrOperad.map (R := R) τ y.val) (q : Fin k) (w : BarT I l) (m : ℕ)
    (hm : m + 1 = k + l) :
    barVal I x (τ q) w m hm = GrOperad.map (R := R) ((posEquivF q l m hm).symm.trans
      ((compEquiv τ (Equiv.refl (Fin l)) q).trans (posEquivF (τ q) l m hm)))
        (barVal I y q w m hm) := by
  unfold barVal
  rw [hy, h, map_smul]
  congr 1
  have e := GrOperad.map_comp (R := R) (P := P) τ (Equiv.refl (Fin l)) q y.val w.val
  rw [GrOperad.map_refl] at e
  rw [← e, ← GrOperad.map_trans, ← GrOperad.map_trans]
  congr 2
  ext t
  simp

/-- **Merge-composing two generators of the bar construction.** -/
lemma mcomp_gen_bar {k l : ℕ} (c : BarT I k) (i : Fin k) (g : BarT I l) (m : ℕ)
    (h : m + 1 = k + l) :
    mcomp (barMerge I) (grGenPar R (BarGen I)) R i (gen (R := R) (gp := grGenPar R (BarGen I)) c)
        (gen g)
      = GrOperad.map (R := R) (posEquivF i l m h).symm (gen (barMerge I k l c i g m)) :=
  mcomp_gen_gen (barMerge I) c i g m h

/-- **Merging a generator with a linearity relation** lands in the ideal of the linearity
relations. -/
lemma barMerge_gen_left {n : ℕ} {r : FreeGr R (grGenPar R (BarGen I)) (Fin n)}
    (hr : r ∈ grLinRel R (BarGen I) n) {k : ℕ} (c : BarT I k) (i : Fin k) :
    mcomp (barMerge I) (grGenPar R (BarGen I)) R i
      (gen (R := R) (gp := grGenPar R (BarGen I)) c) r ∈ (𝒥).sub _ := by
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = k + n := ⟨k + n - 1, by have := i.2; omega⟩
  have hi : (i : ℕ) < k ∧ m + 1 = k + n := ⟨i.2, hm⟩
  rcases hr with (⟨b, v, w, hv, hw, rfl⟩ | ⟨b, a, v, hv, rfl⟩) | ⟨b, τ, v, hv, rfl⟩
  · simp only [map_sub, lgen, mcomp_gen_bar c i _ m hm]
    rw [← map_sub, ← map_sub]
    refine (𝒥).map_mem _ (gen_sub_mem_add _ _ _ (by simp only [barMerge_par])
      (by simp only [barMerge_par]) (BarT.eq_add ?_))
    rw [barMerge_val _ _ hi, barMerge_val _ _ hi, barMerge_val _ _ hi]
    exact barVal_add_right c _ rfl m _
  · simp only [map_sub, map_smul, lgen, mcomp_gen_bar c i _ m hm]
    rw [← map_smul, ← map_sub]
    refine (𝒥).map_mem _ (gen_sub_mem_smul _ _ a (by simp only [barMerge_par])
      (BarT.eq_smul a ?_))
    rw [barMerge_val _ _ hi, barMerge_val _ _ hi]
    exact barVal_smul_right c _ a rfl m _
  · rw [map_sub, mcomp_map_right]
    simp only [lgen, mcomp_gen_bar c i _ m hm]
    have hρ : (posEquivF i n m hm).symm.trans (compEquiv (Equiv.refl (Fin k)) τ i)
        = ((posEquivF i n m hm).symm.trans ((compEquiv (Equiv.refl (Fin k)) τ i).trans
            (posEquivF i n m hm))).trans (posEquivF i n m hm).symm := by
      ext t
      exact (Equiv.symm_apply_apply (posEquivF i n m hm)
        (compEquiv (Equiv.refl (Fin k)) τ i ((posEquivF i n m hm).symm t))).symm
    have key : ∀ X : FreeGr R (grGenPar R (BarGen I)) (Fin m),
        GrOperad.map (R := R) (compEquiv (Equiv.refl (Fin k)) τ i)
            (GrOperad.map (R := R) (posEquivF i n m hm).symm X)
          = GrOperad.map (R := R) (posEquivF i n m hm).symm (GrOperad.map (R := R)
              ((posEquivF i n m hm).symm.trans ((compEquiv (Equiv.refl (Fin k)) τ i).trans
                (posEquivF i n m hm))) X) := by
      intro X
      rw [← GrOperad.map_trans, ← GrOperad.map_trans, hρ]
      rfl
    rw [key, ← map_sub]
    refine (𝒥).map_mem _ (map_gen_sub_mem _ _ _ (by simp only [barMerge_par])
      (BarT.eq_map _ ?_))
    rw [barMerge_val _ _ hi, barMerge_val _ _ hi]
    exact barVal_map_right c _ τ rfl m _

/-- **Merging a linearity relation with a generator** lands in the ideal of the linearity
relations. -/
lemma barMerge_gen_right {n : ℕ} {r : FreeGr R (grGenPar R (BarGen I)) (Fin n)}
    (hr : r ∈ grLinRel R (BarGen I) n) {k : ℕ} (c : BarT I k) (i : Fin n) :
    mcomp (barMerge I) (grGenPar R (BarGen I)) R i r
      (gen (R := R) (gp := grGenPar R (BarGen I)) c) ∈ (𝒥).sub _ := by
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = n + k := ⟨n + k - 1, by have := i.2; omega⟩
  rcases hr with (⟨b, v, w, hv, hw, rfl⟩ | ⟨b, a, v, hv, rfl⟩) | ⟨b, τ, v, hv, rfl⟩
  · have hi : (i : ℕ) < n ∧ m + 1 = n + k := ⟨i.2, hm⟩
    simp only [map_sub, LinearMap.sub_apply, lgen, mcomp_gen_bar _ i c m hm]
    rw [← map_sub, ← map_sub]
    refine (𝒥).map_mem _ (gen_sub_mem_add _ _ _ (by simp only [barMerge_par])
      (by simp only [barMerge_par]) (BarT.eq_add ?_))
    rw [barMerge_val _ _ hi, barMerge_val _ _ hi, barMerge_val _ _ hi]
    exact barVal_add_left (by rfl) (by rfl) (by rfl) _ c m _
  · have hi : (i : ℕ) < n ∧ m + 1 = n + k := ⟨i.2, hm⟩
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, lgen,
      mcomp_gen_bar _ i c m hm]
    rw [← map_smul, ← map_sub]
    refine (𝒥).map_mem _ (gen_sub_mem_smul _ _ a (by simp only [barMerge_par])
      (BarT.eq_smul a ?_))
    rw [barMerge_val _ _ hi, barMerge_val _ _ hi]
    exact barVal_smul_left a (by rfl) (by rfl) _ c m _
  · obtain ⟨i', rfl⟩ := τ.surjective i
    have hi : ((τ i' : Fin n) : ℕ) < n ∧ m + 1 = n + k := ⟨(τ i').2, hm⟩
    have hi' : (i' : ℕ) < n ∧ m + 1 = n + k := ⟨i'.2, hm⟩
    rw [map_sub, LinearMap.sub_apply, mcomp_map_left]
    simp only [lgen, mcomp_gen_bar _ _ c m hm]
    have key : ∀ X : FreeGr R (grGenPar R (BarGen I)) (Fin m),
        GrOperad.map (R := R) (compEquiv τ (Equiv.refl (Fin k)) i')
            (GrOperad.map (R := R) (posEquivF i' k m hm).symm X)
          = GrOperad.map (R := R) (posEquivF (τ i') k m hm).symm (GrOperad.map (R := R)
              ((posEquivF i' k m hm).symm.trans ((compEquiv τ (Equiv.refl (Fin k)) i').trans
                (posEquivF (τ i') k m hm))) X) := by
      intro X
      rw [← GrOperad.map_trans, ← GrOperad.map_trans]
      congr 2
      ext t
      simp
    rw [key, ← map_sub]
    refine (𝒥).map_mem _ (map_gen_sub_mem _ _ _ (by simp only [barMerge_par])
      (BarT.eq_map _ ?_))
    rw [barMerge_val _ _ hi, barMerge_val _ _ hi']
    exact barVal_map_left τ (by rfl) (by rfl) i' c m _

variable (I) in
/-- **The bar merge is compatible with the linearity relations.** -/
theorem barMerge_relHyp :
    RelHyp (barMerge I) (grGenPar R (BarGen I)) R (grLinRel R (BarGen I)) where
  barD_eq _ _ hr := barD_of_linRel _ hr
  unitCoeff_eq _ _ hr := unitCoeff_of_linRel hr
  homog _ _ hr := par_of_linRel hr
  gen_left _ _ hr _ c i := barMerge_gen_left hr c i
  gen_right _ _ hr _ c i := barMerge_gen_right hr c i

/-- **Merges in series**, in values. -/
lemma barMerge_val_seq {kx lg lh : ℕ} (x : BarT I kx) (g : BarT I lg) (hh : BarT I lh)
    {p j m₁ m₂ m : ℕ} (hp : p < kx) (hj : j < lg) (h₁ : m₁ + 1 = lg + lh)
    (h₂ : m₂ + 1 = kx + lg) (h : m + 1 = kx + m₁) :
    (barMerge I m₂ lh (barMerge I kx lg x p g m₂) (p + j) hh m).val
      = (-σ R x.1.2) • (barMerge I kx m₁ x p (barMerge I lg lh g j hh m₁) m).val := by
  have h' : m + 1 = m₂ + lh := by omega
  have hq : p + j < m₂ := by omega
  rw [barMerge_val _ _ ⟨hq, h'⟩, barMerge_val _ _ ⟨hp, h⟩]
  unfold barVal
  rw [barMerge_par, barMerge_val _ _ ⟨hp, h₂⟩, barMerge_val _ _ ⟨hj, h₁⟩]
  unfold barVal
  simp only [map_smul, LinearMap.smul_apply, smul_smul]
  rw [assoc_seq_pos ⟨p, hp⟩ ⟨j, hj⟩ ⟨p + j, hq⟩ h₁ h₂ h h' (Fin.ext (posEquivF_inr _ _ _))]
  congr 1
  generalize x.1.2 = a
  generalize g.1.2 = b
  cases a <;> cases b <;> simp

/-- **Merges in parallel**, in values. -/
lemma barMerge_val_par {kx l₁ l₂ : ℕ} (x : BarT I kx) (a₁ : BarT I l₁) (a₂ : BarT I l₂)
    {p₁ p₂ p₂' m₁ m₂ m : ℕ} (hp : p₁ < p₂) (hp₂ : p₂ < kx) (hp' : p₂' + 1 = p₂ + l₁)
    (h₁ : m₁ + 1 = kx + l₁) (h₂ : m₂ + 1 = kx + l₂) (h : m + 1 = m₁ + l₂) :
    (barMerge I m₂ l₁ (barMerge I kx l₂ x p₂ a₂ m₂) p₁ a₁ m).val
      = (-σ R (a₁.1.2 && a₂.1.2)) •
          (barMerge I m₁ l₂ (barMerge I kx l₁ x p₁ a₁ m₁) p₂' a₂ m).val := by
  have hp₁ : p₁ < kx := by omega
  have h' : m + 1 = m₂ + l₁ := by omega
  have hq₁ : p₁ < m₂ := by omega
  have hq₂ : p₂' < m₁ := by omega
  have hpF : (⟨p₁, hp₁⟩ : Fin kx) < ⟨p₂, hp₂⟩ := hp
  have e₂ : posEquivF (⟨p₁, hp₁⟩ : Fin kx) l₁ m₁ h₁
      (Sum.inl ⟨⟨p₂, hp₂⟩, (Fin.ne_of_lt hpF).symm⟩) = ⟨p₂', hq₂⟩ := by
    apply Fin.ext
    have := posEquivF_inl_of_gt (⟨p₁, hp₁⟩ : Fin kx) h₁ ⟨⟨p₂, hp₂⟩, (Fin.ne_of_lt hpF).symm⟩ hpF
    simp only at this ⊢
    omega
  have e₁ : posEquivF (⟨p₂, hp₂⟩ : Fin kx) l₂ m₂ h₂
      (Sum.inl ⟨⟨p₁, hp₁⟩, Fin.ne_of_lt hpF⟩) = ⟨p₁, hq₁⟩ :=
    Fin.ext (posEquivF_inl_of_lt (⟨p₂, hp₂⟩ : Fin kx) h₂ ⟨⟨p₁, hp₁⟩, Fin.ne_of_lt hpF⟩ hpF)
  rw [barMerge_val _ _ ⟨hq₁, h'⟩, barMerge_val _ _ ⟨hq₂, h⟩]
  unfold barVal
  rw [barMerge_par, barMerge_par, barMerge_val _ _ ⟨hp₂, h₂⟩, barMerge_val _ _ ⟨hp₁, h₁⟩]
  unfold barVal
  simp only [map_smul, LinearMap.smul_apply, smul_smul]
  rw [assoc_par_pos hpF ⟨p₁, hq₁⟩ ⟨p₂', hq₂⟩ h₁ h₂ h h' e₂ e₁ x.val a₁.par_val a₂.par_val,
    smul_smul]
  congr 1
  generalize x.1.2 = c
  generalize a₁.1.2 = b₁
  generalize a₂.1.2 = b₂
  cases c <;> cases b₁ <;> cases b₂ <;> simp

variable (I) in
/-- **The bar merge is associative** modulo the linearity relations, in series and in
parallel. -/
theorem barMerge_assocHyp : AssocHyp (barMerge I) (grGenPar R (BarGen I)) R (𝒥) where
  series kx lg lh x g hh p j m₁ m₂ m hp hj h₁ h₂ h := by
    have e := gen_sub_mem_smul (barMerge I m₂ lh (barMerge I kx lg x p g m₂) (p + j) hh m)
      (barMerge I kx m₁ x p (barMerge I lg lh g j hh m₁) m) (-σ R x.1.2)
      (by
        simp only [barMerge_par]
        generalize x.1.2 = a
        generalize g.1.2 = b
        generalize hh.1.2 = c
        cases a <;> cases b <;> cases c <;> rfl)
      (BarT.eq_smul _ (barMerge_val_seq x g hh hp hj h₁ h₂ h))
    rw [neg_smul, sub_neg_eq_add, add_comm] at e
    exact e
  parallel kx l₁ l₂ x a₁ a₂ p₁ p₂ p₂' m₁ m₂ m hp hp₂ hp' h₁ h₂ h := by
    have e := gen_sub_mem_smul (barMerge I m₂ l₁ (barMerge I kx l₂ x p₂ a₂ m₂) p₁ a₁ m)
      (barMerge I m₁ l₂ (barMerge I kx l₁ x p₁ a₁ m₁) p₂' a₂ m) (-σ R (a₁.1.2 && a₂.1.2))
      (by
        simp only [barMerge_par]
        generalize x.1.2 = a
        generalize a₁.1.2 = b
        generalize a₂.1.2 = c
        cases a <;> cases b <;> cases c <;> rfl)
      (BarT.eq_smul _ (barMerge_val_par x a₁ a₂ hp hp₂ hp' h₁ h₂ h))
    rw [neg_smul, sub_neg_eq_add, add_comm] at e
    exact e

end BarRel

/-! ## The bar construction -/

section BarCoop

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  (I : GrOperadIdeal R P)

local notation "𝒥" => GrOperadIdeal.span R (grLinRel R (BarGen I))

/-- **The bar construction** of a graded operad relative to an ideal: the cut cooperad on the
suspension of the ideal, with the bar differential. -/
def BarCoop (A : Type) [Fintype A] [DecidableEq A] : Type (max u v) := FreeGrL R (BarGen I) A

noncomputable instance (A : Type) [Fintype A] [DecidableEq A] : AddCommGroup (BarCoop I A) :=
  inferInstanceAs (AddCommGroup (FreeGrL R (BarGen I) A))

noncomputable instance (A : Type) [Fintype A] [DecidableEq A] : Module R (BarCoop I A) :=
  inferInstanceAs (Module R (FreeGrL R (BarGen I) A))

namespace Bar

/-- **The bar differential**, descended to the quotient by the linearity relations. -/
noncomputable def d (A : Type) [Fintype A] [DecidableEq A] :
    FreeGrL R (BarGen I) A →ₗ[R] FreeGrL R (BarGen I) A :=
  Submodule.mapQ _ _ (barD (barMerge I) (grGenPar R (BarGen I)) R A)
    fun _ hz => barD_mem (barMerge I) barMerge_odd (barMerge_relHyp I) hz

variable {I}

lemma d_proj {A : Type} [Fintype A] [DecidableEq A] (x : FreeGr R (grGenPar R (BarGen I)) A) :
    d I A ((𝒥).proj A x) = (𝒥).proj A (barD (barMerge I) (grGenPar R (BarGen I)) R A x) :=
  rfl

/-- **The bar differential squares to zero.** -/
theorem d_d {A : Type} [Fintype A] [DecidableEq A] (X : FreeGrL R (BarGen I) A) :
    d I A (d I A X) = 0 := by
  obtain ⟨x, rfl⟩ := (𝒥).proj_surjective A X
  rw [d_proj, d_proj, GrOperadIdeal.proj_eq_zero_iff]
  exact barD_barD_mem (𝒥) barMerge_odd (barMerge_assocHyp I) x

lemma tw_proj {A : Type} [Fintype A] [DecidableEq A] (x : FreeGr R (grGenPar R (BarGen I)) A) :
    GrOperad.par (R := R) false ((𝒥).proj A x) - GrOperad.par (R := R) true ((𝒥).proj A x)
      = (𝒥).proj A (GrSpecies.tw (R := R) (V := FreeGr R (grGenPar R (BarGen I))) true x) := by
  rw [GrSpecies.tw_apply, σ_true, neg_one_smul, ← sub_eq_add_neg, map_sub]
  rfl

variable (I) in
/-- **The bar construction is a dg cooperad.** -/
noncomputable instance instDGCooperad : DGCooperad R (BarCoop I) :=
  { (inferInstance : GrCooperad R (FreeGrL R (BarGen I))) with
    d := fun {A} _ _ => d I A
    d_d := fun {A} _ _ X => d_d X
    d_par := fun {A} _ _ b X => by
      obtain ⟨x, rfl⟩ := (𝒥).proj_surjective A X
      show (𝒥).proj A (barD (barMerge I) (grGenPar R (BarGen I)) R A (GrOperad.par (R := R) b x))
        = (𝒥).proj A (GrOperad.par (R := R) (!b) (barD (barMerge I) _ R A x))
      rw [par_barD barMerge_odd (!b) x, Bool.not_not]
    map_d := fun {A B} _ _ _ _ e X => by
      obtain ⟨x, rfl⟩ := (𝒥).proj_surjective A X
      show (𝒥).proj B (GrOperad.map (R := R) e (barD (barMerge I) (grGenPar R (BarGen I)) R A x))
        = (𝒥).proj B (barD (barMerge I) _ R B (GrOperad.map (R := R) e x))
      rw [map_barD]
    counit_d := fun X => by
      obtain ⟨x, rfl⟩ := (𝒥).proj_surjective Unit X
      exact counit_barD x
    decomp_d := fun {A B} _ _ _ _ i X => by
      obtain ⟨x, rfl⟩ := (𝒥).proj_surjective _ X
      have key : TensorProduct.map ((𝒥).proj A) ((𝒥).proj B) (GrCooperad.decomp (R := R) i
            (barD (barMerge I) (grGenPar R (BarGen I)) R _ x))
          = TensorProduct.map (d I A) (LinearMap.id (R := R) (M := FreeGrL R (BarGen I) B))
              (TensorProduct.map ((𝒥).proj A) ((𝒥).proj B) (GrCooperad.decomp (R := R) i x))
            + TensorProduct.map
                (GrOperad.par (R := R) (P := FreeGrL R (BarGen I)) (A := A) false
                  - GrOperad.par (R := R) (P := FreeGrL R (BarGen I)) (A := A) true) (d I B)
              (TensorProduct.map ((𝒥).proj A) ((𝒥).proj B) (GrCooperad.decomp (R := R) i x)) := by
        rw [decomp_barD barMerge_odd i x]
        generalize GrCooperad.decomp (R := R) (C := FreeGr R (grGenPar R (BarGen I))) i x = z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul a b =>
          simp only [TensorProduct.map_tmul, map_add, LinearMap.id_apply]
          rw [LinearMap.sub_apply, tw_proj]
          rfl
        | add a b ha hb =>
          simp only [map_add] at ha hb ⊢
          rw [add_add_add_comm, ha, hb, add_add_add_comm]
      exact key }

/-- **The bar construction is coaugmented** by the trivial tree. -/
noncomputable instance instCoaug : GrCooperad.Coaug R (BarCoop I) :=
  inferInstanceAs (GrCooperad.Coaug R (FreeGrL R (BarGen I)))

/-- **The bar differential kills the coaugmentation.** -/
theorem d_one : DGCooperad.d (R := R) (C := BarCoop I) (GrCooperad.Coaug.one (R := R)) = 0 := by
  show (𝒥).proj Unit (barD (barMerge I) (grGenPar R (BarGen I)) R Unit
    (GrCooperad.Coaug.one (R := R) (C := FreeGr R (grGenPar R (BarGen I))))) = 0
  rw [barD_one, map_zero]

end Bar

end BarCoop

end Operad
