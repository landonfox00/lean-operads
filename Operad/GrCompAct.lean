/-
# The right action of a graded operad on a graded composite

For a graded linear species `V` and a graded operad `C`, the graded composite `V ∘ C` is a right
module over `C`: an operation `z` composes into an input `i` of `v ⊗ y₁ ⊗ ⋯ ⊗ yₖ` by composing it
into the inner operation `y_a` owning `i`, after moving it across the inner operations read after
`y_a`, with the Koszul sign (`GrComposite.act`):

  `(v ⊗ y₁ ⊗ ⋯ ⊗ yₖ) ◁ᵢ z = ± v ⊗ y₁ ⊗ ⋯ ⊗ (y_a ∘ᵢ z) ⊗ ⋯ ⊗ yₖ`.

It is computed on generators given by owners (`GrComposite.ownGen`): the inputs of the result are
owned as before, the inputs of `z` by `a`.
-/
import Operad.GrCompOwn

universe u v w

namespace Operad

open Function Sym GerBV

/-! ## Reordering signs, after an input -/

namespace GrComposite

section RsgAfter

variable {R : Type u} [CommRing R] {A : Type} [Fintype A] [DecidableEq A]

open Classical in
/-- **The Koszul signs of an operation composed after the input `j`** in two orders, and the
reordering signs before and after it is composed. -/
lemma rsg_update_mul_after (L L' : LinOrd A) (c : A → Bool) (j : A) (q : Bool) :
    (∏ a, if ltB L j a then σ R (q && c a) else 1) * GrEnd.rsg R L L' (update c j (xor (c j) q))
      = GrEnd.rsg R L L' c * ∏ a, if ltB L' j a then σ R (q && c a) else 1 := by
  simp only [ltB_eq_true]
  rw [rsg_update, ← Finset.prod_mul_distrib, mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun a _ => ?_
  have hs : σ R (q && c a) * σ R (q && c a) = 1 := σ_mul_self R _
  by_cases haj : a = j
  · subst haj
    simp only [L.irrefl, L'.irrefl, and_false, if_false, mul_one]
  rcases L.total a j haj with h1 | h1 <;> rcases L'.total a j haj with h2 | h2 <;>
    simp only [h1, h2, GrEnd.lt_asymm _ h1, GrEnd.lt_asymm _ h2, and_true, and_false, if_true,
      if_false, mul_one, one_mul, hs]

end RsgAfter

end GrComposite

variable {R : Type u} [CommRing R]
  {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrOperad R C]

namespace GrComposite

section Owners

variable {S : Type} [DecidableEq S] {Y : Type} {A : Type} [DecidableEq A]

/-- **The owners after composing at the input `i`**: the inputs of the inserted operation are
owned by the owner of `i`. -/
def actOwner (f : S → A) (i : S) : Without S i ⊕ Y → A :=
  Sum.elim (fun s => f s.1) fun _ => f i

/-- The inputs owned by another input of the outer operation are unchanged. -/
def actNe (f : S → A) (i : S) (a : A) (h : f i ≠ a) : Fib f a ≃ Fib (actOwner (Y := Y) f i) a where
  toFun s := ⟨Sum.inl ⟨s.1, fun e => h (by rw [← s.2, e])⟩, s.2⟩
  invFun s := match s with
    | ⟨Sum.inl t, ht⟩ => ⟨t.1, ht⟩
    | ⟨Sum.inr _, ht⟩ => absurd ht h
  left_inv _ := rfl
  right_inv := by
    rintro ⟨t | t, ht⟩
    · rfl
    · exact absurd ht h

/-- The inputs owned by the owner of `i`: those other than `i`, and the inputs of the inserted
operation. -/
def actEq (f : S → A) (i : S) (a : A) (h : f i = a) :
    Without (Fib f a) ⟨i, h⟩ ⊕ Y ≃ Fib (actOwner (Y := Y) f i) a where
  toFun x := match x with
    | Sum.inl t => ⟨Sum.inl ⟨t.1.1, fun e => t.2 (Subtype.ext e)⟩, t.1.2⟩
    | Sum.inr y => ⟨Sum.inr y, h⟩
  invFun x := match x with
    | ⟨Sum.inl t, ht⟩ => Sum.inl ⟨⟨t.1, ht⟩, fun e => t.2 (congrArg Subtype.val e)⟩
    | ⟨Sum.inr y, _⟩ => Sum.inr y
  left_inv := by
    rintro (t | y) <;> rfl
  right_inv := by
    rintro ⟨t | y, ht⟩ <;> rfl

end Owners

variable {S : Type} [Fintype S] [DecidableEq S] {Y : Type} [Fintype Y] [DecidableEq Y]

section ActGen

variable {A : Type} [Fintype A] [DecidableEq A]

/-- **The inner operations after composing `z` at the input `i`**: `z` composed into the inner
operation owning `i`, the inner operations read after it twisted by the parity `q` of `z`. -/
noncomputable def actLin (L : LinOrd A) (f : S → A) (i : S) (z : C Y) (q : Bool) (a : A) :
    C (Fib f a) →ₗ[R] C (Fib (actOwner (Y := Y) f i) a) :=
  if h : f i = a then
      (GrOperad.map (R := R) (actEq f i a h)).comp
        ((GrOperad.comp (R := R) (P := C) (⟨i, h⟩ : Fib f a)).flip z)
    else (GrOperad.tw (R := R) (P := C) (q && ltB L (f i) a)).comp
      (GrOperad.map (R := R) (actNe f i a h))

/-- **The inner operations after composing `z` at the input `i`**: `z` composed into the inner
operation owning `i`, the inner operations read after it twisted by the parity `q` of `z`. -/
noncomputable def actY (L : LinOrd A) (f : S → A) (y : ∀ a, C (Fib f a)) (i : S) (z : C Y)
    (q : Bool) : ∀ a, C (Fib (actOwner (Y := Y) f i) a) :=
  fun a => actLin (R := R) L f i z q a (y a)

omit [Fintype A] in
lemma actLin_eq (L : LinOrd A) (f : S → A) (i : S) (z : C Y) (q : Bool) (a : A) (h : f i = a)
    (x : C (Fib f a)) :
    actLin (R := R) L f i z q a x
      = GrOperad.map (R := R) (actEq f i a h) (GrOperad.comp (R := R) (⟨i, h⟩ : Fib f a) x z) := by
  rw [actLin, dif_pos h]
  rfl

omit [Fintype A] in
lemma actLin_ne (L : LinOrd A) (f : S → A) (i : S) (z : C Y) (q : Bool) (a : A) (h : f i ≠ a)
    (x : C (Fib f a)) :
    actLin (R := R) L f i z q a x = GrOperad.tw (R := R) (P := C) (q && ltB L (f i) a)
      (GrOperad.map (R := R) (actNe f i a h) x) := by
  rw [actLin, dif_neg h]
  rfl

omit [Fintype A] in
lemma actY_update (L : LinOrd A) (f : S → A) (y : ∀ a, C (Fib f a)) (i : S) (z : C Y)
    (q : Bool) (b : A) (w : C (Fib f b)) :
    actY (R := R) L f (update y b w) i z q
      = update (actY (R := R) L f y i z q) b (actLin (R := R) L f i z q b w) :=
  funext fun a => apply_update (fun a => ⇑(actLin (R := R) L f i z q a)) y b w a

/-- The generator obtained by composing `z` of parity `q` at the input `i`. -/
noncomputable abbrev actGen (L : LinOrd A) (m : V A) (f : S → A) (y : ∀ a, C (Fib f a)) (i : S)
    (z : C Y) (q : Bool) : GrCompGen V C (Without S i ⊕ Y) :=
  ownGen L m (actOwner f i) (actY (R := R) L f y i z q)

end ActGen

/-! ## The action on generators -/

section ActFun

/-- The inner operations of a generator, on the inputs they own. -/
noncomputable abbrev ownY (g : GrCompGen V C S) (a : g.A) : C (Fib (owner g) a) :=
  GrOperad.map (R := R) (fibEquiv g a) (g.y a)

variable (R) in
/-- The action of `z` at `i` on the data of a generator given by owners. -/
noncomputable def actOwn {A : Type} [Fintype A] [DecidableEq A] (L : LinOrd A) (m : V A)
    (f : S → A) (y : ∀ a, C (Fib f a)) (i : S) (z : C Y) : GrComposite R V C (Without S i ⊕ Y) :=
  ∑ q : Bool, mk R (actGen (R := R) L m f y i (GrOperad.par (R := R) q z) q)

variable (R) in
/-- **The action of `z` at `i` on a generator.** -/
noncomputable def actFun (i : S) (z : C Y) (g : GrCompGen V C S) :
    GrComposite R V C (Without S i ⊕ Y) :=
  actOwn R g.L g.m (owner g) (ownY (R := R) g) i z

end ActFun

/-! ## Linearity -/

section Lin

variable {A : Type} [Fintype A] [DecidableEq A]

lemma actOwn_add_m (L : LinOrd A) (m m' : V A) (f : S → A) (y : ∀ a, C (Fib f a)) (i : S)
    (z : C Y) : actOwn R L (m + m') f y i z = actOwn R L m f y i z + actOwn R L m' f y i z := by
  unfold actOwn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  exact mk_add_m (actGen (R := R) L m f y i (GrOperad.par (R := R) q z) q) m'

lemma actOwn_smul_m (L : LinOrd A) (c : R) (m : V A) (f : S → A) (y : ∀ a, C (Fib f a)) (i : S)
    (z : C Y) : actOwn R L (c • m) f y i z = c • actOwn R L m f y i z := by
  unfold actOwn
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  exact mk_smul_m (actGen (R := R) L m f y i (GrOperad.par (R := R) q z) q) c

lemma actOwn_update_add (L : LinOrd A) (m : V A) (f : S → A) (y : ∀ a, C (Fib f a)) (i : S)
    (z : C Y) (b : A) (w w' : C (Fib f b)) :
    actOwn R L m f (update y b (w + w')) i z
      = actOwn R L m f (update y b w) i z + actOwn R L m f (update y b w') i z := by
  unfold actOwn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  show mkY (actGen (R := R) L m f y i (GrOperad.par (R := R) q z) q)
      (actY (R := R) L f (update y b (w + w')) i (GrOperad.par (R := R) q z) q)
    = mkY (actGen (R := R) L m f y i (GrOperad.par (R := R) q z) q)
        (actY (R := R) L f (update y b w) i (GrOperad.par (R := R) q z) q)
      + mkY (actGen (R := R) L m f y i (GrOperad.par (R := R) q z) q)
        (actY (R := R) L f (update y b w') i (GrOperad.par (R := R) q z) q)
  rw [actY_update, actY_update, actY_update, map_add, MultilinearMap.map_update_add]

lemma actOwn_update_smul (L : LinOrd A) (m : V A) (f : S → A) (y : ∀ a, C (Fib f a)) (i : S)
    (z : C Y) (b : A) (c : R) (w : C (Fib f b)) :
    actOwn R L m f (update y b (c • w)) i z = c • actOwn R L m f (update y b w) i z := by
  unfold actOwn
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  show mkY (actGen (R := R) L m f y i (GrOperad.par (R := R) q z) q)
      (actY (R := R) L f (update y b (c • w)) i (GrOperad.par (R := R) q z) q)
    = c • mkY (actGen (R := R) L m f y i (GrOperad.par (R := R) q z) q)
        (actY (R := R) L f (update y b w) i (GrOperad.par (R := R) q z) q)
  rw [actY_update, actY_update, map_smul, MultilinearMap.map_update_smul]

end Lin

omit [Fintype S] [DecidableEq S] [Fintype Y] [DecidableEq Y] in
lemma gmap_congr {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    {e e' : X ≃ Z} (h : ∀ a, e a = e' a) (x : C X) :
    GrOperad.map (R := R) e x = GrOperad.map (R := R) e' x := by
  rw [Equiv.ext h]

omit [Fintype S] [DecidableEq S] [Fintype Y] [DecidableEq Y] in
lemma gmap_comp_congr {X X' Z : Type} [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X']
    [Fintype Z] [DecidableEq Z] (e : X ≃ X') (f : X' ≃ Z) (g : X ≃ Z) (h : ∀ a, f (e a) = g a)
    (x : C X) : GrOperad.map (R := R) f (GrOperad.map (R := R) e x) = GrOperad.map (R := R) g x := by
  rw [← GrOperad.map_trans]
  exact gmap_congr h x

/-! ## Relabelling the outer operation -/

section Outer

variable {A A' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']

omit [Fintype S] [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A] [Fintype A']
  [DecidableEq A'] in
lemma actOwner_comp (σ : A' ≃ A) (f : S → A) (i : S) :
    σ.symm ∘ actOwner (Y := Y) f i = actOwner (σ.symm ∘ f) i :=
  funext fun x => by cases x <;> rfl

omit [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] in
lemma ltB_map (e : A ≃ A') (L : LinOrd A) (b b' : A') :
    ltB (LinOrd.map e L) b b' = ltB L (e.symm b) (e.symm b') := rfl

/-- **The action commutes with relabelling the outer operation.** -/
lemma actOwn_outer (σ : A' ≃ A) (L : LinOrd A) (m : V A') (f : S → A) (y : ∀ a, C (Fib f a))
    (i : S) (z : C Y) :
    actOwn R L (SymSpecies.map (R := R) σ m) f y i z
      = actOwn R (LinOrd.map σ.symm L) m (σ.symm ∘ f)
          (fun a' => GrOperad.map (R := R) (fibOuter σ f a') (y (σ a'))) i z := by
  unfold actOwn
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [mk_ownGen_outer σ L m (actOwner f i), mk_ownGen_congr _ m (actOwner_comp σ f i)]
  congr 2
  funext a'
  show GrOperad.map (R := R) _ (GrOperad.map (R := R) (fibOuter σ (actOwner f i) a')
      (actLin (R := R) L f i (GrOperad.par (R := R) q z) q (σ a') (y (σ a'))))
    = actLin (R := R) (LinOrd.map σ.symm L) (σ.symm ∘ f) i (GrOperad.par (R := R) q z) q a'
        (GrOperad.map (R := R) (fibOuter σ f a') (y (σ a')))
  by_cases h : f i = σ a'
  · have h' : (σ.symm ∘ f) i = a' := by simp [h]
    rw [actLin_eq _ _ _ _ _ _ h, actLin_eq _ _ _ _ _ _ h']
    have hc := GrOperad.map_comp (R := R) (fibOuter σ f a') (Equiv.refl Y) (⟨i, h⟩ : Fib f (σ a'))
      (y (σ a')) (GrOperad.par (R := R) q z)
    rw [GrOperad.map_refl] at hc
    show _ = GrOperad.map (R := R) (actEq (σ.symm ∘ f) i a' h')
      (GrOperad.comp (R := R) ((fibOuter σ f a') ⟨i, h⟩)
        (GrOperad.map (R := R) (fibOuter σ f a') (y (σ a'))) (GrOperad.par (R := R) q z))
    rw [← hc]
    simp only [← GrOperad.map_trans]
    refine (gmap_comp_congr _ _ _ ?_ _).symm
    rintro (⟨⟨t, ht⟩, hne⟩ | x) <;> rfl
  · have h' : (σ.symm ∘ f) i ≠ a' := fun e => h (by rw [← e]; simp)
    rw [actLin_ne _ _ _ _ _ _ h, actLin_ne _ _ _ _ _ _ h', ltB_map, Equiv.symm_symm,
      show σ ((σ.symm ∘ f) i) = f i by simp]
    rw [GrOperad.map_tw, GrOperad.map_tw]
    congr 1
    simp only [← GrOperad.map_trans]
    apply gmap_congr
    intro x
    exact Subtype.ext rfl

end Outer

/-! ## Owners, reordering -/

section Reorder

variable {A : Type} [Fintype A] [DecidableEq A]

lemma actOwn_congr (L : LinOrd A) (m : V A) {f f' : S → A} (hf : f = f')
    (y : ∀ a, C (Fib f a)) (i : S) (z : C Y) :
    actOwn R L m f y i z = actOwn R L m f' (fun a =>
      GrOperad.map (R := R) (Equiv.subtypeEquivRight fun s => by rw [hf]) (y a)) i z := by
  subst hf
  congr 1
  funext a
  rw [show (Equiv.subtypeEquivRight _ : Fib f a ≃ Fib f a) = Equiv.refl _ from
    Equiv.ext fun _ => rfl, GrOperad.map_refl]

omit [Fintype A] in
/-- **The twists of a homogeneous family of inner operations** are signs. -/
lemma actY_hom (L : LinOrd A) (f : S → A) (y : ∀ a, C (Fib f a)) (i : S) (z : C Y) (q : Bool)
    (c : A → Bool) (hy : ∀ a, GrOperad.par (R := R) (c a) (y a) = y a) (a : A) :
    actY (R := R) L f y i z q a
      = (if ltB L (f i) a then σ R (q && c a) else 1) • actY (R := R) L f y i z false a := by
  unfold actY
  by_cases h : f i = a
  · subst h
    rw [actLin_eq _ _ _ _ _ _ rfl, actLin_eq _ _ _ _ _ _ rfl, ltB_self, if_neg Bool.false_ne_true,
      one_smul]
  · rw [actLin_ne _ _ _ _ _ _ h, actLin_ne _ _ _ _ _ _ h, Bool.false_and, GrOperad.tw_false,
      GrOperad.tw_hom _ (c := c a) (by rw [← GrOperad.map_par, hy])]
    by_cases hl : ltB L (f i) a
    · simp [hl]
    · simp [hl]

omit [Fintype A] in
lemma actY_false_indep (L L' : LinOrd A) (f : S → A) (y : ∀ a, C (Fib f a)) (i : S) (z : C Y) :
    actY (R := R) L f y i z false = actY (R := R) L' f y i z false := by
  funext a
  unfold actY actLin
  split_ifs <;> simp

omit [Fintype A] in
lemma actY_false_par (L : LinOrd A) (f : S → A) (y : ∀ a, C (Fib f a)) (i : S) (z : C Y)
    (q : Bool) (hz : GrOperad.par (R := R) q z = z) (c : A → Bool)
    (hy : ∀ a, GrOperad.par (R := R) (c a) (y a) = y a) (a : A) :
    GrOperad.par (R := R) (update c (f i) (xor (c (f i)) q) a) (actY (R := R) L f y i z false a)
      = actY (R := R) L f y i z false a := by
  unfold actY
  by_cases h : f i = a
  · subst h
    rw [actLin_eq _ _ _ _ _ _ rfl, update_self, ← GrOperad.map_par, ← hy, ← hz,
      GrOperad.comp_par, hy, hz]
  · rw [actLin_ne _ _ _ _ _ _ h, update_of_ne (Ne.symm h), Bool.false_and, GrOperad.tw_false,
      ← GrOperad.map_par, hy]

/-- **Reordering the inner operations before the action.** -/
lemma mk_actGen_reorder (L L' : LinOrd A) (m : V A) (f : S → A) (y : ∀ a, C (Fib f a)) (i : S)
    (z : C Y) (q : Bool) (hz : GrOperad.par (R := R) q z = z) (c : A → Bool)
    (hy : ∀ a, GrOperad.par (R := R) (c a) (y a) = y a) :
    mk R (actGen (R := R) L m f y i z q)
      = GrEnd.rsg R L L' c • mk R (actGen (R := R) L' m f y i z q) := by
  have hL : ∀ L₀ : LinOrd A, mk R (actGen (R := R) L₀ m f y i z q)
      = (∏ a, if ltB L₀ (f i) a then σ R (q && c a) else 1)
        • mk R (ownGen L₀ m (actOwner f i) (actY (R := R) L f y i z false)) := fun L₀ => by
    have := (mkY (R := R) (ownGen L₀ m (actOwner f i) (actY (R := R) L f y i z false))).map_smul_univ
      (fun a => if ltB L₀ (f i) a then σ R (q && c a) else 1) (actY (R := R) L f y i z false)
    refine Eq.trans ?_ this
    show mk R (ownGen L₀ m (actOwner f i) (actY (R := R) L₀ f y i z q)) = mk R (ownGen L₀ m
      (actOwner f i) fun a => (if ltB L₀ (f i) a then σ R (q && c a) else 1)
        • actY (R := R) L f y i z false a)
    rw [actY_false_indep L L₀]
    congr 2
    funext a
    exact actY_hom L₀ f y i z q c hy a
  rw [hL L, hL L', mk_reorder (ownGen L m (actOwner f i) (actY (R := R) L f y i z false)) L' _
    (actY_false_par L f y i z q hz c hy), smul_smul, smul_smul]
  congr 1
  exact rsg_update_mul_after L L' c (f i) q

end Reorder

/-! ## The action -/

section Act

omit [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V] in
lemma ownY_update (g : GrCompGen V C S) (a : g.A) (w : C (g.B a)) :
    ownY (R := R) { g with y := update g.y a w }
      = update (ownY (R := R) g) a (GrOperad.map (R := R) (fibEquiv g a) w) :=
  funext fun a' => apply_update (fun a' => ⇑(GrOperad.map (R := R) (P := C) (fibEquiv g a'))) g.y
    a w a'

omit [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrOperad R C]
  [Fintype S] [DecidableEq S] in
lemma owner_outer (g : GrCompGen V C S) {A : Type} [Fintype A] [DecidableEq A] (σ : A ≃ g.A)
    (m : V A) :
    owner (⟨A, fun a => g.B (σ a), LinOrd.map σ.symm g.L, m, fun a => g.y (σ a),
      (Equiv.sigmaCongrLeft σ).trans g.e⟩ : GrCompGen V C S) = σ.symm ∘ owner g := by
  funext s
  show ((Equiv.sigmaCongrLeft σ).symm (g.e.symm s)).1 = σ.symm (g.e.symm s).1
  generalize g.e.symm s = p
  obtain ⟨⟨a', b⟩, rfl⟩ := (Equiv.sigmaCongrLeft σ).surjective p
  rw [Equiv.symm_apply_apply]
  show a' = σ.symm (σ a')
  rw [Equiv.symm_apply_apply]

lemma actFun_respects (i : S) (z : C Y) :
    GrCompGen.Respects R (actFun (V := V) R i z) where
  add_m g m' := actOwn_add_m g.L g.m m' (owner g) (ownY (R := R) g) i z
  smul_m g c := actOwn_smul_m g.L c g.m (owner g) (ownY (R := R) g) i z
  add_y g a w w' := by
    show actOwn R g.L g.m (owner g) (ownY (R := R) { g with y := update g.y a (w + w') }) i z
      = actOwn R g.L g.m (owner g) (ownY (R := R) { g with y := update g.y a w }) i z
        + actOwn R g.L g.m (owner g) (ownY (R := R) { g with y := update g.y a w' }) i z
    rw [ownY_update, ownY_update, ownY_update, map_add, actOwn_update_add]
  smul_y g a c w := by
    show actOwn R g.L g.m (owner g) (ownY (R := R) { g with y := update g.y a (c • w) }) i z
      = c • actOwn R g.L g.m (owner g) (ownY (R := R) { g with y := update g.y a w }) i z
    rw [ownY_update, ownY_update, map_smul, actOwn_update_smul]
  outer := @fun g A _ _ σ m => by
    show actOwn R g.L (SymSpecies.map (R := R) σ m) (owner g) (ownY (R := R) g) i z = _
    rw [actOwn_outer, actFun, actOwn_congr _ m (owner_outer g σ m).symm]
    congr 1
    funext a'
    simp only [ownY, ← GrOperad.map_trans]
    apply gmap_congr
    intro b
    rfl
  inner := @fun g B _ _ τ => by
    show actOwn R g.L g.m _ (ownY (R := R) (⟨g.A, B, g.L, g.m,
      fun a => SymSpecies.map (R := R) (τ a) (g.y a),
      (Equiv.sigmaCongrRight τ).symm.trans g.e⟩ : GrCompGen V C S)) i z = actFun R i z g
    unfold actFun
    congr 1
    funext a
    apply gmap_comp_congr
    intro b
    exact Subtype.ext (show g.e ⟨a, (τ a).symm (τ a b)⟩ = g.e ⟨a, b⟩ by
      rw [Equiv.symm_apply_apply])
  reorder g L' c hy := by
    unfold actFun actOwn
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    exact mk_actGen_reorder g.L L' g.m (owner g) (ownY (R := R) g) i (GrOperad.par (R := R) q z) q
      (by rw [GrOperad.par_par, if_pos rfl]) c fun a => by
        show GrOperad.par (R := R) (c a) (GrOperad.map (R := R) _ (g.y a)) = _
        rw [← GrOperad.map_par]
        exact congrArg _ (hy a)

variable (R V) in
/-- **The right action of `C` on `V ∘ C`**: composing `z` at the input `i`. -/
noncomputable def act (i : S) (z : C Y) :
    GrComposite R V C S →ₗ[R] GrComposite R V C (Without S i ⊕ Y) :=
  lift (actFun R i z) (actFun_respects i z)

@[simp] lemma act_mk (i : S) (z : C Y) (g : GrCompGen V C S) :
    act R V i z (mk R g) = actFun R i z g :=
  lift_mk _ _ g

end Act

/-! ## Equivariance -/

section Equivariance

variable {S' Y' : Type} [Fintype S'] [DecidableEq S'] [Fintype Y'] [DecidableEq Y']
  {A : Type} [Fintype A] [DecidableEq A]

omit [Fintype S] [Fintype Y] [DecidableEq Y] [Fintype S'] [Fintype Y'] [DecidableEq Y']
  [Fintype A] [DecidableEq A] in
lemma actOwner_compEquiv (σ : S ≃ S') (τ : Y ≃ Y') (f : S → A) (i : S) :
    actOwner f i ∘ (compEquiv σ τ i).symm = actOwner (f ∘ σ.symm) (σ i) := by
  funext x
  rcases x with s | y
  · rfl
  · show f i = f (σ.symm (σ i))
    rw [Equiv.symm_apply_apply]

/-- **The action commutes with relabelling**, on generators given by owners. -/
lemma map_actOwn (σ : S ≃ S') (τ : Y ≃ Y') (L : LinOrd A) (m : V A) (f : S → A)
    (y : ∀ a, C (Fib f a)) (i : S) (z : C Y) :
    map (compEquiv σ τ i) (actOwn R L m f y i z)
      = actOwn R L m (f ∘ σ.symm) (fun a => GrOperad.map (R := R) (fibMap σ f a) (y a)) (σ i)
          (GrOperad.map (R := R) τ z) := by
  unfold actOwn
  rw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mk_ownGen, mk_ownGen_congr _ m (actOwner_compEquiv σ τ f i)]
  congr 2
  funext a
  show GrOperad.map (R := R) _ (GrOperad.map (R := R) _
      (actLin (R := R) L f i (GrOperad.par (R := R) q z) q a (y a)))
    = actLin (R := R) L (f ∘ σ.symm) (σ i) (GrOperad.par (R := R) q (GrOperad.map (R := R) τ z))
        q a (GrOperad.map (R := R) (fibMap σ f a) (y a))
  rw [← GrOperad.map_par]
  by_cases h : f i = a
  · have h' : (f ∘ σ.symm) (σ i) = a := by simp [h]
    rw [actLin_eq _ _ _ _ _ _ h, actLin_eq _ _ _ _ _ _ h']
    have hc := GrOperad.map_comp (R := R) (fibMap σ f a) τ (⟨i, h⟩ : Fib f a) (y a)
      (GrOperad.par (R := R) q z)
    show _ = GrOperad.map (R := R) (actEq (f ∘ σ.symm) (σ i) a h')
      (GrOperad.comp (R := R) ((fibMap σ f a) ⟨i, h⟩)
        (GrOperad.map (R := R) (fibMap σ f a) (y a))
        (GrOperad.map (R := R) τ (GrOperad.par (R := R) q z)))
    rw [← hc]
    simp only [← GrOperad.map_trans]
    refine (gmap_comp_congr _ _ _ ?_ _).symm
    rintro (⟨⟨t, ht⟩, hne⟩ | x) <;> rfl
  · have h' : (f ∘ σ.symm) (σ i) ≠ a := by simpa using h
    rw [actLin_ne _ _ _ _ _ _ h, actLin_ne _ _ _ _ _ _ h',
      show (f ∘ σ.symm) (σ i) = f i by simp, GrOperad.map_tw, GrOperad.map_tw]
    congr 1
    simp only [← GrOperad.map_trans]
    apply gmap_congr
    intro b
    exact Subtype.ext rfl

/-- **The action commutes with relabelling.** -/
lemma map_act (σ : S ≃ S') (τ : Y ≃ Y') (i : S) (z : C Y) (x : GrComposite R V C S) :
    map (compEquiv σ τ i) (act R V i z x)
      = act R V (σ i) (GrOperad.map (R := R) τ z) (map σ x) := by
  have h : (map (R := R) (M := V) (N := C) (compEquiv σ τ i)).comp (act R V i z)
      = (act R V (σ i) (GrOperad.map (R := R) τ z)).comp (map σ) := hom_ext fun g => by
    simp only [LinearMap.comp_apply, act_mk, map_mk, actFun]
    rw [map_actOwn]
    congr 1
    funext a
    show _ = GrOperad.map (R := R) (fibEquiv (g.relabel σ) a) (g.y a)
    simp only [ownY]
    apply gmap_comp_congr
    intro b
    rfl
  exact LinearMap.congr_fun h x

end Equivariance

/-! ## Homogeneous operations, the unit -/

section Unit

variable {A : Type} [Fintype A] [DecidableEq A]

lemma mk_actGen_zero (L : LinOrd A) (m : V A) (f : S → A) (y : ∀ a, C (Fib f a)) (i : S)
    (q : Bool) : mk R (actGen (R := R) L m f y i (0 : C Y) q) = 0 := by
  refine mk_of_y_eq_zero _ (a := f i) ?_
  show actLin (R := R) L f i 0 q (f i) (y (f i)) = 0
  rw [actLin_eq _ _ _ _ _ _ rfl, map_zero, map_zero]

/-- **The action of a homogeneous operation** has a single term. -/
lemma actOwn_hom (L : LinOrd A) (m : V A) (f : S → A) (y : ∀ a, C (Fib f a)) (i : S) (z : C Y)
    {q : Bool} (hz : GrOperad.par (R := R) q z = z) :
    actOwn R L m f y i z = mk R (actGen (R := R) L m f y i z q) := by
  unfold actOwn
  rw [Finset.sum_eq_single q]
  · rw [hz]
  · intro q' _ hq'
    rw [← hz, GrOperad.par_par, if_neg hq']
    exact mk_actGen_zero L m f y i q'
  · intro h
    exact absurd (Finset.mem_univ q) h

omit [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrOperad R C] in
lemma owner_ownGen (L : LinOrd A) (m : V A) (f : S → A) (y : ∀ a, C (Fib f a)) :
    owner (ownGen L m f y) = f := rfl

/-- **The action on a generator given by owners.** -/
lemma actFun_ownGen (L : LinOrd A) (m : V A) (f : S → A) (y : ∀ a, C (Fib f a)) (i : S)
    (z : C Y) : actFun R i z (ownGen L m f y) = actOwn R L m f y i z := by
  unfold actFun
  congr 1
  funext a
  show GrOperad.map (R := R) (fibEquiv (ownGen L m f y) a) (y a) = y a
  rw [show fibEquiv (ownGen L m f y) a = Equiv.refl _ from Equiv.ext fun b => Subtype.ext rfl]
  exact GrOperad.map_refl (R := R) _

lemma act_mk_ownGen (L : LinOrd A) (m : V A) (f : S → A) (y : ∀ a, C (Fib f a)) (i : S)
    (z : C Y) : act R V i z (mk R (ownGen L m f y)) = actOwn R L m f y i z := by
  rw [act_mk, actFun_ownGen]

omit [Fintype S] [Fintype A] [DecidableEq A] in
lemma actOwner_rightUnit (f : S → A) (i : S) :
    actOwner (Y := Unit) f i ∘ (rightUnitEquiv i).symm = f := by
  funext s
  by_cases h : s = i
  · subst h
    simp [rightUnitEquiv, actOwner]
  · simp [rightUnitEquiv, actOwner, h]

/-- **The unit acts trivially**, on generators given by owners. -/
lemma map_actOwn_one (L : LinOrd A) (m : V A) (f : S → A) (y : ∀ a, C (Fib f a)) (i : S) :
    map (rightUnitEquiv i) (actOwn R L m f y i (GrOperad.one (R := R) (P := C)))
      = mk R (ownGen L m f y) := by
  rw [actOwn_hom L m f y i _ (GrOperad.par_one (R := R) (P := C)), map_mk_ownGen,
    mk_ownGen_congr _ m (actOwner_rightUnit f i)]
  congr 2
  funext a
  show GrOperad.map (R := R) _ (GrOperad.map (R := R) _
      (actLin (R := R) L f i (GrOperad.one (R := R)) false a (y a))) = y a
  by_cases h : f i = a
  · rw [actLin_eq _ _ _ _ _ _ h]
    have hc := GrOperad.comp_one (R := R) (⟨i, h⟩ : Fib f a) (y a)
    conv_rhs => rw [← hc]
    simp only [← GrOperad.map_trans]
    apply gmap_congr
    rintro (⟨⟨t, ht⟩, hne⟩ | ⟨⟩)
    · apply Subtype.ext
      show t = t
      rfl
    · apply Subtype.ext
      show (rightUnitEquiv i) (Sum.inr ()) = i
      rfl
  · rw [actLin_ne _ _ _ _ _ _ h, Bool.false_and, GrOperad.tw_false]
    simp only [← GrOperad.map_trans]
    conv_rhs => rw [← GrOperad.map_refl (R := R) (y a)]
    apply gmap_congr
    intro b
    exact Subtype.ext rfl

/-- **The unit acts trivially.** -/
lemma map_act_one (i : S) (x : GrComposite R V C S) :
    map (rightUnitEquiv i) (act R V i (GrOperad.one (R := R) (P := C)) x) = x := by
  have h : (map (R := R) (M := V) (N := C) (rightUnitEquiv i)).comp
      (act R V i (GrOperad.one (R := R) (P := C))) = LinearMap.id := hom_ext fun g => by
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    rw [mk_eq_ownGen (R := R) g, act_mk_ownGen, map_actOwn_one]
  exact LinearMap.congr_fun h x

end Unit

end GrComposite

end Operad
