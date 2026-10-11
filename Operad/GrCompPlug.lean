/-
# Plugging a composite into an input of the outer operation

For a graded operad `P` and a graded operad `C`, an element `Z` of `P ∘ C` can be plugged into an
input `a₀` of the outer operation of a generator `m ⊗ y₁ ⊗ ⋯ ⊗ yₖ` of `P ∘ C`, in place of the
inner operation `y_{a₀}`, as long as its inputs are those owned by `a₀`: for `Z = m' ⊗ y'`,

  `m ⊗ (y₁, …, m' ⊗ y', …, yₖ) ↦ ± (m ∘_{a₀} m') ⊗ (y₁, …, y', …, yₖ)`,

the sign moving `m'` across the inner operations read before `a₀` (`GrComposite.plug`). The inputs
of the result are owned by the inputs of `m'` when they were owned by `a₀`, and as before
otherwise (`GrComposite.plugOwner`).

Reordering a generator is allowed when the inner operations changing places are homogeneous
(`GrComposite.mk_reorder_of`): the others need not be.
-/
import Operad.GrCompAct

universe u v w

namespace Operad

open Function Sym GerBV

/-! ## Reordering with some inner operations kept in place -/

namespace GrComposite

section ReorderOf

variable {R : Type u} [CommRing R]
  {M : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M A)] [GrSpecies R M]
  {N : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N A)] [GrSpecies R N]
  {S : Type} [Fintype S] [DecidableEq S]

omit [Fintype S] [DecidableEq S] in
lemma rsg_of_agree {A : Type} [Fintype A] (L L' : LinOrd A) (c r : A → Bool) (U : A → Prop)
    (hU : ∀ a b, U a → ((L.lt a b ↔ L'.lt a b) ∧ (L.lt b a ↔ L'.lt b a)))
    (hr : ∀ a, ¬ U a → r a = c a) :
    GrEnd.rsg R L L' r = GrEnd.rsg R L L' c := by
  classical
  unfold GrEnd.rsg
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
  by_cases ha : U a
  · have h := hU a b ha
    rw [if_neg, if_neg] <;> exact fun h' => GrEnd.lt_asymm L h'.1 (h.2.2 h'.2)
  by_cases hb : U b
  · have h := hU b a hb
    rw [if_neg, if_neg] <;> exact fun h' => GrEnd.lt_asymm L h'.1 (h.1.2 h'.2)
  rw [hr a ha, hr b hb]

/-- **Reordering a generator** whose inner operations at the positions `U` keep their places
relative to all the others: only the other inner operations need to be homogeneous. -/
lemma mk_reorder_of (g : GrCompGen M N S) (L' : LinOrd g.A) (c : g.A → Bool) (U : g.A → Prop)
    [DecidablePred U]
    (hU : ∀ a b, U a → ((g.L.lt a b ↔ L'.lt a b) ∧ (g.L.lt b a ↔ L'.lt b a)))
    (hy : ∀ a, ¬ U a → GrSpecies.par (R := R) (c a) (g.y a) = g.y a) :
    mk R g = GrEnd.rsg R g.L L' c • mk R { g with L := L' } := by
  let v : ∀ a, Bool → N (g.B a) := fun a j =>
    if U a then (GrSpecies.par (R := R) j : N (g.B a) →ₗ[R] N (g.B a)) (g.y a)
    else if j = c a then g.y a else 0
  have hv : g.y = fun a => ∑ j, v a j := by
    funext a
    simp only [v, Fintype.sum_bool]
    by_cases ha : U a
    · rw [if_pos ha, if_pos ha, add_comm, GrSpecies.par_add]
    · rw [if_neg ha, if_neg ha]
      cases c a <;> simp
  have e1 : mk R g = mkY (R := R) g (fun a => ∑ j, v a j) := by
    rw [← hv]
    rfl
  have e2 : mk R { g with L := L' } = mkY (R := R) { g with L := L' } (fun a => ∑ j, v a j) := by
    rw [← hv]
    rfl
  rw [e1, e2, MultilinearMap.map_sum, MultilinearMap.map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : ∀ a, ¬ U a → r a = c a
  · have hh : ∀ a, GrSpecies.par (R := R) (r a) (v a (r a)) = v a (r a) := by
      intro a
      simp only [v]
      by_cases ha : U a
      · rw [if_pos ha, GrSpecies.par_par, if_pos rfl]
      · rw [if_neg ha, if_pos (hr a ha), hr a ha, hy a ha]
    have := mk_reorder (R := R) { g with y := fun a => v a (r a) } L' r hh
    rw [rsg_of_agree g.L L' c r U hU hr] at this
    exact this
  · push Not at hr
    obtain ⟨a, ha, hra⟩ := hr
    have h0 : v a (r a) = 0 := by
      simp only [v]
      rw [if_neg ha, if_neg hra]
    rw [(mkY (R := R) g).map_coord_zero a h0,
      (mkY (R := R) { g with L := L' }).map_coord_zero a h0, smul_zero]

end ReorderOf

end GrComposite

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrOperad R C]

namespace GrComposite

/-! ## Owners after plugging -/

section Owners

variable {S : Type} {A : Type} [DecidableEq A] {A' : Type}

/-- **The owners after plugging at `a₀`**: the inputs owned by `a₀` are now owned by the inputs of
the plugged outer operation. -/
def plugOwner (f : S → A) (a₀ : A) (f' : Fib f a₀ → A') : S → Without A a₀ ⊕ A' :=
  fun s => if h : f s = a₀ then Sum.inr (f' ⟨s, h⟩) else Sum.inl ⟨f s, h⟩

lemma plugOwner_eq_inl {f : S → A} {a₀ : A} {f' : Fib f a₀ → A'} {s : S} {b : Without A a₀} :
    plugOwner f a₀ f' s = Sum.inl b ↔ f s = b.1 := by
  unfold plugOwner
  by_cases h : f s = a₀
  · rw [dif_pos h]
    exact ⟨fun h' => absurd h' Sum.inr_ne_inl, fun h' => absurd (h'.symm.trans h) b.2⟩
  · rw [dif_neg h]
    exact ⟨fun h' => congrArg Subtype.val (Sum.inl_injective h'),
      fun h' => congrArg Sum.inl (Subtype.ext h')⟩

lemma plugOwner_eq_inr {f : S → A} {a₀ : A} {f' : Fib f a₀ → A'} {s : S} {a' : A'} :
    plugOwner f a₀ f' s = Sum.inr a' ↔ ∃ h : f s = a₀, f' ⟨s, h⟩ = a' := by
  unfold plugOwner
  by_cases h : f s = a₀
  · rw [dif_pos h]
    exact ⟨fun h' => ⟨h, Sum.inr_injective h'⟩, fun ⟨_, h'⟩ => congrArg Sum.inr h'⟩
  · rw [dif_neg h]
    exact ⟨fun h' => absurd h' Sum.inl_ne_inr, fun ⟨h', _⟩ => absurd h' h⟩

/-- The inputs owned by another input of the outer operation. -/
def plugNe (f : S → A) (a₀ : A) (f' : Fib f a₀ → A') (b : Without A a₀) :
    Fib f b.1 ≃ Fib (plugOwner f a₀ f') (Sum.inl b) where
  toFun s := ⟨s.1, plugOwner_eq_inl.2 s.2⟩
  invFun s := ⟨s.1, plugOwner_eq_inl.1 s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The inputs owned by an input of the plugged outer operation. -/
def plugEq (f : S → A) (a₀ : A) (f' : Fib f a₀ → A') (a' : A') :
    Fib f' a' ≃ Fib (plugOwner f a₀ f') (Sum.inr a') where
  toFun t := ⟨t.1.1, plugOwner_eq_inr.2 ⟨t.1.2, t.2⟩⟩
  invFun s := ⟨⟨s.1, (plugOwner_eq_inr.1 s.2).1⟩, (plugOwner_eq_inr.1 s.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma plugNe_apply (f : S → A) (a₀ : A) (f' : Fib f a₀ → A') (b : Without A a₀)
    (s : Fib f b.1) : (plugNe f a₀ f' b s).1 = s.1 := rfl

@[simp] lemma plugEq_apply (f : S → A) (a₀ : A) (f' : Fib f a₀ → A') (a' : A')
    (t : Fib f' a') : (plugEq f a₀ f' a' t).1 = t.1.1 := rfl

end Owners

/-! ## Plugging a generator -/

section PlugGen

variable {S : Type} [Fintype S] [DecidableEq S] {A : Type} [Fintype A] [DecidableEq A]
  {A' : Type} [Fintype A'] [DecidableEq A']

/-- **The inner operations after plugging** an operation of parity `q` at `a₀`: those owned by
another input, twisted by `q` when read before `a₀`, and the plugged ones. -/
noncomputable def plugY (L : LinOrd A) (f : S → A) (yy : ∀ a, C (Fib f a)) (a₀ : A)
    (f' : Fib f a₀ → A') (yy' : ∀ a', C (Fib f' a')) (q : Bool) :
    ∀ x, C (Fib (plugOwner f a₀ f') x)
  | Sum.inl b => GrOperad.map (R := R) (plugNe f a₀ f' b)
      (GrOperad.tw (R := R) (P := C) (q && ltB L b.1 a₀) (yy b.1))
  | Sum.inr a' => GrOperad.map (R := R) (plugEq f a₀ f' a') (yy' a')

/-- **The generator obtained by plugging** `m' ⊗ y'` at `a₀`, `m'` of parity `q`. -/
noncomputable abbrev plugGen (L : LinOrd A) (m : P A) (f : S → A) (yy : ∀ a, C (Fib f a))
    (a₀ : A) (L' : LinOrd A') (m' : P A') (f' : Fib f a₀ → A') (yy' : ∀ a', C (Fib f' a'))
    (q : Bool) : GrCompGen P C S :=
  ownGen (LinOrd.comp a₀ L L') (GrOperad.comp (R := R) a₀ m m') (plugOwner f a₀ f')
    (plugY (R := R) L f yy a₀ f' yy' q)

variable (R) in
/-- **Plugging** `m' ⊗ y'` at `a₀`, on the data of generators given by owners. -/
noncomputable def plugOwn (L : LinOrd A) (m : P A) (f : S → A) (yy : ∀ a, C (Fib f a)) (a₀ : A)
    (L' : LinOrd A') (m' : P A') (f' : Fib f a₀ → A') (yy' : ∀ a', C (Fib f' a')) :
    GrComposite R P C S :=
  ∑ q : Bool, mk R (plugGen (R := R) L m f yy a₀ L' (GrOperad.par (R := R) q m') f' yy' q)

omit [Fintype A] [Fintype A'] in
lemma plugY_update (L : LinOrd A) (f : S → A) (yy : ∀ a, C (Fib f a)) (a₀ : A)
    (f' : Fib f a₀ → A') (yy' : ∀ a', C (Fib f' a')) (q : Bool) (a' : A') (w : C (Fib f' a')) :
    plugY (R := R) L f yy a₀ f' (update yy' a' w) q
      = update (plugY (R := R) L f yy a₀ f' yy' q) (Sum.inr a')
          (GrOperad.map (R := R) (plugEq f a₀ f' a') w) := by
  funext x
  rcases x with b | a''
  · rw [update_of_ne (Sum.inl_ne_inr)]
    rfl
  · by_cases h : a'' = a'
    · subst h
      rw [update_self]
      show GrOperad.map (R := R) _ (update yy' a'' w a'') = _
      rw [update_self]
    · rw [update_of_ne (fun e => h (Sum.inr_injective e))]
      show GrOperad.map (R := R) _ (update yy' a' w a'') = _
      rw [update_of_ne h]
      rfl

end PlugGen

/-! ## Linearity -/

section Lin

variable {S : Type} [Fintype S] [DecidableEq S] {A : Type} [Fintype A] [DecidableEq A]
  {A' : Type} [Fintype A'] [DecidableEq A'] (L : LinOrd A) (m : P A) (f : S → A)
  (yy : ∀ a, C (Fib f a)) (a₀ : A) (L' : LinOrd A') (f' : Fib f a₀ → A')

lemma plugOwn_add_m (m' m'' : P A') (yy' : ∀ a', C (Fib f' a')) :
    plugOwn R L m f yy a₀ L' (m' + m'') f' yy'
      = plugOwn R L m f yy a₀ L' m' f' yy' + plugOwn R L m f yy a₀ L' m'' f' yy' := by
  unfold plugOwn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  dsimp only [plugGen]
  rw [map_add, map_add]
  exact mk_add_m (plugGen (R := R) L m f yy a₀ L' (GrOperad.par (R := R) q m') f' yy' q) _

lemma plugOwn_smul_m (c : R) (m' : P A') (yy' : ∀ a', C (Fib f' a')) :
    plugOwn R L m f yy a₀ L' (c • m') f' yy' = c • plugOwn R L m f yy a₀ L' m' f' yy' := by
  unfold plugOwn
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  dsimp only [plugGen]
  rw [map_smul, map_smul]
  exact mk_smul_m (plugGen (R := R) L m f yy a₀ L' (GrOperad.par (R := R) q m') f' yy' q) c

lemma plugOwn_update_add (m' : P A') (yy' : ∀ a', C (Fib f' a')) (a' : A') (w w' : C (Fib f' a')) :
    plugOwn R L m f yy a₀ L' m' f' (update yy' a' (w + w'))
      = plugOwn R L m f yy a₀ L' m' f' (update yy' a' w)
        + plugOwn R L m f yy a₀ L' m' f' (update yy' a' w') := by
  unfold plugOwn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  show mkY (plugGen (R := R) L m f yy a₀ L' (GrOperad.par (R := R) q m') f' yy' q)
      (plugY (R := R) L f yy a₀ f' (update yy' a' (w + w')) q)
    = mkY (plugGen (R := R) L m f yy a₀ L' (GrOperad.par (R := R) q m') f' yy' q)
        (plugY (R := R) L f yy a₀ f' (update yy' a' w) q)
      + mkY (plugGen (R := R) L m f yy a₀ L' (GrOperad.par (R := R) q m') f' yy' q)
        (plugY (R := R) L f yy a₀ f' (update yy' a' w') q)
  rw [plugY_update, plugY_update, plugY_update, map_add, MultilinearMap.map_update_add]

lemma plugOwn_update_smul (m' : P A') (yy' : ∀ a', C (Fib f' a')) (a' : A') (c : R)
    (w : C (Fib f' a')) :
    plugOwn R L m f yy a₀ L' m' f' (update yy' a' (c • w))
      = c • plugOwn R L m f yy a₀ L' m' f' (update yy' a' w) := by
  unfold plugOwn
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  show mkY (plugGen (R := R) L m f yy a₀ L' (GrOperad.par (R := R) q m') f' yy' q)
      (plugY (R := R) L f yy a₀ f' (update yy' a' (c • w)) q)
    = c • mkY (plugGen (R := R) L m f yy a₀ L' (GrOperad.par (R := R) q m') f' yy' q)
        (plugY (R := R) L f yy a₀ f' (update yy' a' w) q)
  rw [plugY_update, plugY_update, map_smul, MultilinearMap.map_update_smul]

end Lin

/-! ## Relabelling the plugged outer operation -/

section Outer

variable {S : Type} [Fintype S] [DecidableEq S] {A : Type} [Fintype A] [DecidableEq A]
  {A' : Type} [Fintype A'] [DecidableEq A'] {A'' : Type} [Fintype A''] [DecidableEq A'']

omit [Fintype S] [DecidableEq S] [Fintype A] [Fintype A'] [DecidableEq A'] [Fintype A'']
  [DecidableEq A''] in
lemma plugOwner_comp (σ : A'' ≃ A') (f : S → A) (a₀ : A) (f' : Fib f a₀ → A') :
    (Equiv.sumCongr (Equiv.refl (Without A a₀)) σ).symm ∘ plugOwner f a₀ f'
      = plugOwner f a₀ (σ.symm ∘ f') := by
  funext s
  simp only [comp_apply, plugOwner]
  split_ifs <;> rfl

lemma comp_map_sumCongr (σ : A'' ≃ A') (a₀ : A) (m : P A) (x : P A'') :
    GrOperad.comp (R := R) a₀ m (GrOperad.map (R := R) σ x)
      = GrOperad.map (R := R) (Equiv.sumCongr (Equiv.refl (Without A a₀)) σ)
          (GrOperad.comp (R := R) a₀ m x) := by
  rw [GrOperad.comp_map_right]
  exact gmap_congr (fun z => by rcases z with z | z <;> rfl) _

omit [Fintype A] [Fintype A'] [DecidableEq A'] [Fintype A''] [DecidableEq A''] in
lemma map_comp_linOrd (σ : A'' ≃ A') (L : LinOrd A) (a₀ : A) (L' : LinOrd A') :
    LinOrd.map (Equiv.sumCongr (Equiv.refl (Without A a₀)) σ).symm (LinOrd.comp a₀ L L')
      = LinOrd.comp a₀ L (LinOrd.map σ.symm L') := by
  ext x z
  rcases x with x | x <;> rcases z with z | z <;> exact Iff.rfl

/-- **Plugging commutes with relabelling the plugged outer operation.** -/
lemma plugOwn_outer (σ : A'' ≃ A') (L : LinOrd A) (m : P A) (f : S → A) (yy : ∀ a, C (Fib f a))
    (a₀ : A) (L' : LinOrd A') (m'' : P A'') (f' : Fib f a₀ → A') (yy' : ∀ a', C (Fib f' a')) :
    plugOwn R L m f yy a₀ L' (GrOperad.map (R := R) σ m'') f' yy'
      = plugOwn R L m f yy a₀ (LinOrd.map σ.symm L') m'' (σ.symm ∘ f')
          (fun a'' => GrOperad.map (R := R) (fibOuter σ f' a'') (yy' (σ a''))) := by
  unfold plugOwn
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← GrOperad.map_par]
  dsimp only [plugGen]
  rw [comp_map_sumCongr]
  refine (mk_ownGen_outer (Equiv.sumCongr (Equiv.refl (Without A a₀)) σ) (LinOrd.comp a₀ L L')
      (GrOperad.comp (R := R) a₀ m (GrOperad.par (R := R) q m'')) (plugOwner f a₀ f') _).trans ?_
  rw [map_comp_linOrd, mk_ownGen_congr _ _ (plugOwner_comp σ f a₀ f')]
  congr 2
  funext z
  rcases z with b | a''
  · show GrOperad.map (R := R) _ (GrOperad.map (R := R) _ (GrOperad.map (R := R)
        (plugNe f a₀ f' b) (GrOperad.tw (R := R) (P := C) (q && ltB L b.1 a₀) (yy b.1))))
      = GrOperad.map (R := R) (plugNe f a₀ (σ.symm ∘ f') b)
          (GrOperad.tw (R := R) (P := C) (q && ltB L b.1 a₀) (yy b.1))
    simp only [← GrOperad.map_trans]
    exact gmap_congr (fun _ => rfl) _
  · show GrOperad.map (R := R) _ (GrOperad.map (R := R) _ (GrOperad.map (R := R)
        (plugEq f a₀ f' (σ a'')) (yy' (σ a''))))
      = GrOperad.map (R := R) (plugEq f a₀ (σ.symm ∘ f') a'')
          (GrOperad.map (R := R) (fibOuter σ f' a'') (yy' (σ a'')))
    simp only [← GrOperad.map_trans]
    exact gmap_congr (fun _ => rfl) _

lemma plugOwn_congr (L : LinOrd A) (m : P A) (f : S → A) (yy : ∀ a, C (Fib f a)) (a₀ : A)
    (L' : LinOrd A') (m' : P A') {f' f'' : Fib f a₀ → A'} (hf : f' = f'')
    (yy' : ∀ a', C (Fib f' a')) :
    plugOwn R L m f yy a₀ L' m' f' yy' = plugOwn R L m f yy a₀ L' m' f'' (fun a' =>
      GrOperad.map (R := R) (Equiv.subtypeEquivRight fun s => by rw [hf]) (yy' a')) := by
  subst hf
  congr 1
  funext a'
  rw [show (Equiv.subtypeEquivRight _ : Fib f' a' ≃ Fib f' a') = Equiv.refl _ from
    Equiv.ext fun _ => rfl, GrOperad.map_refl]

end Outer

/-! ## Reordering the plugged inner operations -/

section Reorder

variable {S : Type} [Fintype S] [DecidableEq S] {A : Type} [Fintype A] [DecidableEq A]
  {A' : Type} [Fintype A'] [DecidableEq A']

/-- **Reordering the plugged inner operations**, the others being arbitrary. -/
lemma mk_plugGen_reorder (L : LinOrd A) (m : P A) (f : S → A) (yy : ∀ a, C (Fib f a)) (a₀ : A)
    (L₁ L₂ : LinOrd A') (m' : P A') (f' : Fib f a₀ → A') (yy' : ∀ a', C (Fib f' a')) (q : Bool)
    (c : A' → Bool) (hy : ∀ a', GrOperad.par (R := R) (c a') (yy' a') = yy' a') :
    mk R (plugGen (R := R) L m f yy a₀ L₁ m' f' yy' q)
      = GrEnd.rsg R L₁ L₂ c • mk R (plugGen (R := R) L m f yy a₀ L₂ m' f' yy' q) := by
  have h := mk_reorder_of (R := R) (plugGen (R := R) L m f yy a₀ L₁ m' f' yy' q)
    (LinOrd.comp a₀ L L₂) (Sum.elim (fun _ => false) c) (fun x => x.isLeft = true)
    (by
      rintro (b | b) z hb
      · rcases z with z | z <;> exact ⟨Iff.rfl, Iff.rfl⟩
      · exact absurd hb (by simp))
    (by
      rintro (b | a') hb
      · exact absurd rfl hb
      · show GrOperad.par (R := R) (c a') (GrOperad.map (R := R) _ (yy' a')) = _
        rw [← GrOperad.map_par, hy]
        rfl)
  rw [h, GrEnd.rsg_comp_right]
  rfl

end Reorder

/-! ## Reordering the outer operation of a plug -/

section OuterReorder

variable {S : Type} [Fintype S] [DecidableEq S] {A : Type} [Fintype A] [DecidableEq A]
  {A' : Type} [Fintype A'] [DecidableEq A']

omit [Fintype A] [Fintype A'] in
lemma plugY_false_indep (L L₂ : LinOrd A) (f : S → A) (yy : ∀ a, C (Fib f a)) (a₀ : A)
    (f' : Fib f a₀ → A') (yy' : ∀ a', C (Fib f' a')) :
    plugY (R := R) L f yy a₀ f' yy' false = plugY (R := R) L₂ f yy a₀ f' yy' false := by
  funext x
  rcases x with b | a' <;> rfl

omit [Fintype A] [Fintype A'] in
/-- The twists of the inner operations read before `a₀`, on homogeneous ones, are signs. -/
lemma plugY_hom (L : LinOrd A) (f : S → A) (yy : ∀ a, C (Fib f a)) (a₀ : A)
    (f' : Fib f a₀ → A') (yy' : ∀ a', C (Fib f' a')) (q : Bool) (c : A → Bool)
    (hy : ∀ a, a ≠ a₀ → GrOperad.par (R := R) (c a) (yy a) = yy a) :
    plugY (R := R) L f yy a₀ f' yy' q = fun x =>
      (Sum.elim (fun b => if ltB L b.1 a₀ then σ R (q && c b.1) else 1) (fun _ => 1) x : R)
        • plugY (R := R) L f yy a₀ f' yy' false x := by
  funext x
  rcases x with b | a'
  · show GrOperad.map (R := R) _ (GrOperad.tw (R := R) (P := C) (q && ltB L b.1 a₀) (yy b.1))
      = _ • GrOperad.map (R := R) _ (GrOperad.tw (R := R) (P := C) (false && ltB L b.1 a₀) _)
    rw [Bool.false_and, GrOperad.tw_false, GrOperad.tw_hom _ (hy b.1 b.2), map_smul]
    by_cases hl : ltB L b.1 a₀
    · simp [hl]
    · simp [hl]
  · exact (one_smul R _).symm

omit [Fintype S] [DecidableEq S] [DecidableEq A'] in
lemma prod_elim_ltB (L : LinOrd A) (a₀ : A) (q : Bool) (c : A → Bool) :
    ∏ x : Without A a₀ ⊕ A',
      (Sum.elim (fun b => if ltB L b.1 a₀ then σ R (q && c b.1) else 1) (fun _ => 1) x : R)
      = ∏ a, if ltB L a a₀ then σ R (q && c a) else 1 := by
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Finset.prod_const_one, mul_one]
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ a₀, ltB_self, if_neg Bool.false_ne_true, one_mul]

lemma mk_plugGen_twist (L : LinOrd A) (m : P A) (f : S → A) (yy : ∀ a, C (Fib f a)) (a₀ : A)
    (L' : LinOrd A') (m' : P A') (f' : Fib f a₀ → A') (yy' : ∀ a', C (Fib f' a')) (q : Bool)
    (c : A → Bool) (hy : ∀ a, a ≠ a₀ → GrOperad.par (R := R) (c a) (yy a) = yy a) :
    mk R (plugGen (R := R) L m f yy a₀ L' m' f' yy' q)
      = (∏ a, if ltB L a a₀ then σ R (q && c a) else 1)
        • mk R (ownGen (LinOrd.comp a₀ L L') (GrOperad.comp (R := R) a₀ m m') (plugOwner f a₀ f')
            (plugY (R := R) L f yy a₀ f' yy' false)) := by
  rw [← prod_elim_ltB (A' := A')]
  have := (mkY (R := R) (ownGen (LinOrd.comp a₀ L L') (GrOperad.comp (R := R) a₀ m m')
    (plugOwner f a₀ f') (plugY (R := R) L f yy a₀ f' yy' false))).map_smul_univ
    (fun x => (Sum.elim (fun b => if ltB L b.1 a₀ then σ R (q && c b.1) else 1) (fun _ => 1) x : R))
    (plugY (R := R) L f yy a₀ f' yy' false)
  refine Eq.trans ?_ this
  show mk R (ownGen _ _ _ (plugY (R := R) L f yy a₀ f' yy' q)) = mk R (ownGen _ _ _ _)
  rw [plugY_hom L f yy a₀ f' yy' q c hy]

omit [DecidableEq A] in
lemma sq_prod_ltB (L : LinOrd A) (a₀ : A) (q : Bool) (c : A → Bool) :
    (∏ a, if ltB L a a₀ then σ R (q && c a) else 1)
      * (∏ a, if ltB L a a₀ then σ R (q && c a) else 1) = 1 := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun a _ => by split_ifs <;> simp [σ_mul_self]

/-- **Reordering the outer operation of a plug**, its inner operations other than the plugged one
homogeneous: the sign of the reordering, the plugged part counting as one operation. -/
lemma mk_plugGen_outer_reorder (L L₂ : LinOrd A) (m : P A) (f : S → A) (yy : ∀ a, C (Fib f a))
    (a₀ : A) (L' : LinOrd A') (m' : P A') (f' : Fib f a₀ → A') (yy' : ∀ a', C (Fib f' a'))
    (q : Bool) (c : A → Bool) (hy : ∀ a, a ≠ a₀ → GrOperad.par (R := R) (c a) (yy a) = yy a)
    (c' : A' → Bool) (hy' : ∀ a', GrOperad.par (R := R) (c' a') (yy' a') = yy' a') :
    mk R (plugGen (R := R) L m f yy a₀ L' m' f' yy' q)
      = GrEnd.rsg R L L₂ (update c a₀ (xor (GrEnd.tot c') q))
        • mk R (plugGen (R := R) L₂ m f yy a₀ L' m' f' yy' q) := by
  set c₀ : A → Bool := update c a₀ (GrEnd.tot c') with hc₀
  have hY : ∀ x, GrOperad.par (R := R) (Sum.elim (fun b => c b.1) c' x)
      (plugY (R := R) L f yy a₀ f' yy' false x) = plugY (R := R) L f yy a₀ f' yy' false x := by
    rintro (b | a')
    · show GrOperad.par (R := R) (c b.1) (GrOperad.map (R := R) (plugNe f a₀ f' b)
        (GrOperad.tw (R := R) (P := C) (false && ltB L b.1 a₀) (yy b.1)))
        = GrOperad.map (R := R) (plugNe f a₀ f' b)
          (GrOperad.tw (R := R) (P := C) (false && ltB L b.1 a₀) (yy b.1))
      rw [← GrOperad.map_par, Bool.false_and, GrOperad.tw_false, hy b.1 b.2]
    · show GrOperad.par (R := R) (c' a') (GrOperad.map (R := R) _ (yy' a')) = _
      rw [← GrOperad.map_par, hy']
      rfl
  have hre : mk R (ownGen (LinOrd.comp a₀ L L') (GrOperad.comp (R := R) a₀ m m')
      (plugOwner f a₀ f') (plugY (R := R) L f yy a₀ f' yy' false))
      = GrEnd.rsg R (LinOrd.comp a₀ L L') (LinOrd.comp a₀ L₂ L') (Sum.elim (fun b => c b.1) c')
        • mk R (ownGen (LinOrd.comp a₀ L₂ L') (GrOperad.comp (R := R) a₀ m m')
          (plugOwner f a₀ f') (plugY (R := R) L f yy a₀ f' yy' false)) :=
    mk_reorder (R := R) (ownGen (LinOrd.comp a₀ L L') (GrOperad.comp (R := R) a₀ m m')
      (plugOwner f a₀ f') (plugY (R := R) L f yy a₀ f' yy' false)) (LinOrd.comp a₀ L₂ L')
      (Sum.elim (fun b => c b.1) c') hY
  have hslot : GrEnd.slot a₀ false (Sum.elim (fun b => c b.1) c') = c₀ := by
    funext a
    by_cases ha : a = a₀
    · subst ha
      rw [hc₀, update_self]
      unfold GrEnd.slot
      rw [feed_self, Bool.false_xor]
      rfl
    · rw [hc₀, update_of_ne ha]
      unfold GrEnd.slot
      exact feed_of_ne ha _ _
  have hrsg := GrEnd.rsg_comp_left (R := R) a₀ L L₂ L' false (Sum.elim (fun b => c b.1) c')
  rw [GrEnd.bsg_false, GrEnd.bsg_false, one_mul, mul_one, hslot] at hrsg
  have hupd : update c₀ a₀ (xor (c₀ a₀) q) = update c a₀ (xor (GrEnd.tot c') q) := by
    rw [hc₀, update_self, update_idem]
  have hmul := rsg_update_mul (R := R) L L₂ c₀ a₀ q
  rw [hupd] at hmul
  have hT : ∀ L₀ : LinOrd A, (∏ a, if ltB L₀ a a₀ then σ R (q && c₀ a) else 1)
      = ∏ a, if ltB L₀ a a₀ then σ R (q && c a) else 1 := fun L₀ =>
    Finset.prod_congr rfl fun a _ => by
      by_cases ha : a = a₀
      · subst ha
        rw [ltB_self, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
      · rw [hc₀, update_of_ne ha]
  rw [hT, hT] at hmul
  rw [mk_plugGen_twist L m f yy a₀ L' m' f' yy' q c hy, hre, ← hrsg,
    mk_plugGen_twist L₂ m f yy a₀ L' m' f' yy' q c hy, plugY_false_indep L₂ L, smul_smul,
    smul_smul]
  congr 1
  set T₁ := ∏ a, if ltB L a a₀ then σ R (q && c a) else 1
  set T₂ := ∏ a, if ltB L₂ a a₀ then σ R (q && c a) else 1
  have h1 := sq_prod_ltB (R := R) L a₀ q c
  have h2 := sq_prod_ltB (R := R) L₂ a₀ q c
  calc T₁ * GrEnd.rsg R L L₂ c₀
      = T₁ * (GrEnd.rsg R L L₂ c₀ * (T₂ * T₂)) := by rw [h2, mul_one]
    _ = T₁ * (T₁ * GrEnd.rsg R L L₂ (update c a₀ (xor (GrEnd.tot c') q)) * T₂) := by
        rw [← mul_assoc (GrEnd.rsg R L L₂ c₀), ← hmul]
    _ = GrEnd.rsg R L L₂ (update c a₀ (xor (GrEnd.tot c') q)) * T₂ := by
        rw [← mul_assoc, ← mul_assoc, h1, one_mul]

end OuterReorder

/-! ## Plugging -/

section Plug

variable {S : Type} [Fintype S] [DecidableEq S] {A : Type} [Fintype A] [DecidableEq A]

variable (R) in
/-- Plugging a generator at `a₀`. -/
noncomputable def plugFun (L : LinOrd A) (m : P A) (f : S → A) (yy : ∀ a, C (Fib f a)) (a₀ : A)
    (g : GrCompGen P C (Fib f a₀)) : GrComposite R P C S :=
  plugOwn R L m f yy a₀ g.L g.m (owner g) (ownY (R := R) g)

lemma plugFun_respects (L : LinOrd A) (m : P A) (f : S → A) (yy : ∀ a, C (Fib f a)) (a₀ : A) :
    GrCompGen.Respects R (plugFun R L m f yy a₀) where
  add_m g m' := plugOwn_add_m L m f yy a₀ g.L (owner g) g.m m' (ownY (R := R) g)
  smul_m g c := plugOwn_smul_m L m f yy a₀ g.L (owner g) c g.m (ownY (R := R) g)
  add_y g a w w' := by
    show plugOwn R L m f yy a₀ g.L g.m (owner g)
        (ownY (R := R) { g with y := update g.y a (w + w') })
      = plugOwn R L m f yy a₀ g.L g.m (owner g) (ownY (R := R) { g with y := update g.y a w })
        + plugOwn R L m f yy a₀ g.L g.m (owner g) (ownY (R := R) { g with y := update g.y a w' })
    rw [ownY_update, ownY_update, ownY_update, map_add, plugOwn_update_add]
  smul_y g a c w := by
    show plugOwn R L m f yy a₀ g.L g.m (owner g)
        (ownY (R := R) { g with y := update g.y a (c • w) })
      = c • plugOwn R L m f yy a₀ g.L g.m (owner g)
          (ownY (R := R) { g with y := update g.y a w })
    rw [ownY_update, ownY_update, map_smul, plugOwn_update_smul]
  outer := @fun g A'' _ _ σ m'' => by
    show plugOwn R L m f yy a₀ g.L (GrOperad.map (R := R) σ m'') (owner g) (ownY (R := R) g) = _
    rw [plugOwn_outer, plugFun, plugOwn_congr _ _ _ _ _ _ m'' (owner_outer g σ m'').symm]
    congr 1
    funext a'
    simp only [ownY, ← GrOperad.map_trans]
    apply gmap_congr
    intro b
    rfl
  inner := @fun g B _ _ τ => by
    show plugOwn R L m f yy a₀ g.L g.m _ (ownY (R := R) (⟨g.A, B, g.L, g.m,
      fun a => SymSpecies.map (R := R) (τ a) (g.y a),
      (Equiv.sigmaCongrRight τ).symm.trans g.e⟩ : GrCompGen P C (Fib f a₀)))
      = plugFun R L m f yy a₀ g
    unfold plugFun
    congr 1
    funext a
    apply gmap_comp_congr
    intro b
    exact Subtype.ext (show g.e ⟨a, (τ a).symm (τ a b)⟩ = g.e ⟨a, b⟩ by
      rw [Equiv.symm_apply_apply])
  reorder g L'' c hy := by
    unfold plugFun plugOwn
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    exact mk_plugGen_reorder L m f yy a₀ g.L L'' _ (owner g) (ownY (R := R) g) q c fun a => by
      show GrOperad.par (R := R) (c a) (GrOperad.map (R := R) _ (g.y a)) = _
      rw [← GrOperad.map_par]
      exact congrArg _ (hy a)

variable (R) in
/-- **Plugging an element of `P ∘ C` at the input `a₀` of the outer operation** of a generator
given by owners, in place of the inner operation `y_{a₀}`. -/
noncomputable def plug (L : LinOrd A) (m : P A) (f : S → A) (yy : ∀ a, C (Fib f a)) (a₀ : A) :
    GrComposite R P C (Fib f a₀) →ₗ[R] GrComposite R P C S :=
  lift (plugFun R L m f yy a₀) (plugFun_respects L m f yy a₀)

@[simp] lemma plug_mk (L : LinOrd A) (m : P A) (f : S → A) (yy : ∀ a, C (Fib f a)) (a₀ : A)
    (g : GrCompGen P C (Fib f a₀)) :
    plug R L m f yy a₀ (mk R g) = plugFun R L m f yy a₀ g :=
  lift_mk _ _ g

end Plug

/-! ## Plugging generators given by owners; parts of a given parity -/

section PlugLemmas

variable {S : Type} [Fintype S] [DecidableEq S] {A : Type} [Fintype A] [DecidableEq A]
  {A' : Type} [Fintype A'] [DecidableEq A']

omit [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P] in
lemma ownY_ownGen {B : Type} [Fintype B] [DecidableEq B] (L' : LinOrd A') (m' : P A')
    (f' : B → A') (yy' : ∀ a', C (Fib f' a')) :
    ownY (R := R) (ownGen L' m' f' yy') = yy' := by
  funext a'
  show GrOperad.map (R := R) _ (yy' a') = yy' a'
  rw [show fibEquiv (ownGen (M := P) L' m' f' yy') a' = Equiv.refl _ from
    Equiv.ext fun _ => rfl, GrOperad.map_refl]

lemma plug_mk_ownGen (L : LinOrd A) (m : P A) (f : S → A) (yy : ∀ a, C (Fib f a))
    (a₀ : A) (L' : LinOrd A') (m' : P A') (f' : Fib f a₀ → A') (yy' : ∀ a', C (Fib f' a')) :
    plug R L m f yy a₀ (mk R (ownGen L' m' f' yy')) = plugOwn R L m f yy a₀ L' m' f' yy' := by
  rw [plug_mk, plugFun, ownY_ownGen]
  rfl

end PlugLemmas

section ParExt

variable {M : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M A)] [GrSpecies R M]
  {N : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N A)] [GrSpecies R N]
  {S : Type} [Fintype S] [DecidableEq S] {W : Type*} [AddCommGroup W] [Module R W]

/-- **Two linear maps agree on the parts of parity `z`** as soon as they agree on the homogeneous
generators of total parity `z`. -/
lemma par_ext (F G : GrComposite R M N S →ₗ[R] W) (z : Bool)
    (h : ∀ g p c, xor p (GrEnd.tot c) = z →
      F (mk R (parGen (R := R) g p c)) = G (mk R (parGen (R := R) g p c)))
    (x : GrComposite R M N S) : F (par R M N z x) = G (par R M N z x) := by
  induction x using induction_on with
  | h0 => simp
  | hadd x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | hsmul c x hx => rw [map_smul, map_smul, map_smul, hx]
  | hmk g =>
    rw [mk_eq_sum (R := R) g]
    simp only [map_sum, par_parGen, apply_ite F, apply_ite G, map_zero]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun c _ => ?_
    split_ifs with hpc
    · exact h g p c hpc
    · rfl

end ParExt

section PlugReorder

variable {S : Type} [Fintype S] [DecidableEq S] {A : Type} [Fintype A] [DecidableEq A]

lemma mk_plugGen_m_zero {A' : Type} [Fintype A'] [DecidableEq A'] (L : LinOrd A) (m : P A)
    (f : S → A)
    (yy : ∀ a, C (Fib f a)) (a₀ : A) (L' : LinOrd A') (f' : Fib f a₀ → A')
    (yy' : ∀ a', C (Fib f' a')) (q : Bool) :
    mk R (plugGen (R := R) L m f yy a₀ L' 0 f' yy' q) = 0 := by
  show mkM (plugGen (R := R) L m f yy a₀ L' 0 f' yy' q) (GrOperad.comp (R := R) a₀ m 0) = 0
  rw [map_zero, map_zero]

/-- **Reordering the outer operation of a plug** of an element of parity `z`, the inner operations
other than the plugged one homogeneous. -/
lemma plug_reorder (L L₂ : LinOrd A) (m : P A) (f : S → A) (yy : ∀ a, C (Fib f a)) (a₀ : A)
    (c : A → Bool) (hy : ∀ a, a ≠ a₀ → GrOperad.par (R := R) (c a) (yy a) = yy a) (z : Bool)
    (Z : GrComposite R P C (Fib f a₀)) (hZ : GrSpecies.par (R := R) z Z = Z) :
    plug R L m f yy a₀ Z = GrEnd.rsg R L L₂ (update c a₀ z) • plug R L₂ m f yy a₀ Z := by
  rw [← hZ]
  have := par_ext (plug R L m f yy a₀) (GrEnd.rsg R L L₂ (update c a₀ z) • plug R L₂ m f yy a₀) z
    (fun g p c' hpc => by
      rw [LinearMap.smul_apply, plug_mk, plug_mk]
      unfold plugFun plugOwn
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hq : q = p
      · subst hq
        have hy' : ∀ a', GrOperad.par (R := R) (c' a')
            (ownY (R := R) (parGen (R := R) g q c') a') = ownY (R := R) (parGen (R := R) g q c') a'
            := fun a' => by
          show GrOperad.par (R := R) (c' a') (GrOperad.map (R := R) _
            (GrOperad.par (R := R) (c' a') (g.y a'))) = _
          rw [← GrOperad.map_par, GrOperad.par_par, if_pos rfl]
          rfl
        rw [mk_plugGen_outer_reorder L L₂ m f yy a₀ _ _ _ _ q c hy c' hy', Bool.xor_comm, hpc]
      · have h0 : GrOperad.par (R := R) q (parGen (R := R) g p c').m = 0 := by
          show GrOperad.par (R := R) q (GrOperad.par (R := R) p g.m) = 0
          rw [GrOperad.par_par, if_neg hq]
        rw [h0, mk_plugGen_m_zero, mk_plugGen_m_zero, smul_zero])
  exact this Z

/-- **Scalars on the other inner operations** come out of a plug. -/
lemma plug_smul_family (L : LinOrd A) (m : P A) (f : S → A) (yy : ∀ a, C (Fib f a)) (a₀ : A)
    (s : A → R) (hs : s a₀ = 1) (Z : GrComposite R P C (Fib f a₀)) :
    plug R L m f (fun a => s a • yy a) a₀ Z = (∏ a, s a) • plug R L m f yy a₀ Z := by
  have h : plug R L m f (fun a => s a • yy a) a₀ = (∏ a, s a) • plug R L m f yy a₀ :=
    hom_ext fun g => by
      rw [LinearMap.smul_apply, plug_mk, plug_mk]
      unfold plugFun plugOwn
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hY : plugY (R := R) L f (fun a => s a • yy a) a₀ (owner g) (ownY (R := R) g) q
          = fun x => (Sum.elim (fun b => s b.1) (fun _ => 1) x : R)
            • plugY (R := R) L f yy a₀ (owner g) (ownY (R := R) g) q x := by
        funext x
        rcases x with b | a'
        · show GrOperad.map (R := R) _ (GrOperad.tw (R := R) (P := C) _ (s b.1 • yy b.1)) = _
          rw [map_smul, map_smul]
          rfl
        · exact (one_smul R _).symm
      have hp : ∏ x : Without A a₀ ⊕ g.A, (Sum.elim (fun b => s b.1) (fun _ => 1) x : R)
          = ∏ a, s a := by
        rw [Fintype.prod_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, Finset.prod_const_one, mul_one]
        rw [Fintype.prod_eq_mul_prod_subtype_ne _ a₀, hs, one_mul]
      have := (mkY (R := R) (plugGen (R := R) L m f yy a₀ g.L (GrOperad.par (R := R) q g.m)
        (owner g) (ownY (R := R) g) q)).map_smul_univ
        (fun x => (Sum.elim (fun b => s b.1) (fun _ => 1) x : R))
        (plugY (R := R) L f yy a₀ (owner g) (ownY (R := R) g) q)
      rw [hp] at this
      refine Eq.trans ?_ this
      show mk R (ownGen _ _ _ _) = mk R (ownGen _ _ _ _)
      rw [hY]
  exact LinearMap.congr_fun h Z

omit [Fintype A] in
lemma plugY_update_left {A' : Type} [Fintype A'] [DecidableEq A'] (L : LinOrd A) (f : S → A)
    (yy : ∀ a, C (Fib f a)) (a₀ : A)
    (f' : Fib f a₀ → A') (yy' : ∀ a', C (Fib f' a')) (q : Bool) (a : A) (ha : a ≠ a₀)
    (w : C (Fib f a)) :
    plugY (R := R) L f (update yy a w) a₀ f' yy' q
      = update (plugY (R := R) L f yy a₀ f' yy' q) (Sum.inl ⟨a, ha⟩)
          (GrOperad.map (R := R) (plugNe f a₀ f' ⟨a, ha⟩)
            (GrOperad.tw (R := R) (P := C) (q && ltB L a a₀) w)) := by
  funext x
  rcases x with b | a'
  · by_cases h : b = ⟨a, ha⟩
    · subst h
      rw [update_self]
      show GrOperad.map (R := R) _ (GrOperad.tw (R := R) (P := C) _ (update yy a w a)) = _
      rw [update_self]
    · rw [update_of_ne (fun e => h (Sum.inl_injective e))]
      have h' : b.1 ≠ a := fun e => h (Subtype.ext e)
      show GrOperad.map (R := R) _ (GrOperad.tw (R := R) (P := C) _ (update yy a w b.1)) = _
      rw [update_of_ne h']
      rfl
  · rw [update_of_ne Sum.inr_ne_inl]
    rfl

omit [Fintype A] in
lemma plugY_update_self {A' : Type} [Fintype A'] [DecidableEq A'] (L : LinOrd A) (f : S → A)
    (yy : ∀ a, C (Fib f a)) (a₀ : A)
    (f' : Fib f a₀ → A') (yy' : ∀ a', C (Fib f' a')) (q : Bool) (w : C (Fib f a₀)) :
    plugY (R := R) L f (update yy a₀ w) a₀ f' yy' q = plugY (R := R) L f yy a₀ f' yy' q := by
  funext x
  rcases x with b | a'
  · show GrOperad.map (R := R) _ (GrOperad.tw (R := R) (P := C) _ (update yy a₀ w b.1)) = _
    rw [update_of_ne b.2]
    rfl
  · rfl

lemma plug_update_self (L : LinOrd A) (m : P A) (f : S → A) (yy : ∀ a, C (Fib f a)) (a₀ : A)
    (w : C (Fib f a₀)) : plug R L m f (update yy a₀ w) a₀ = plug R L m f yy a₀ :=
  hom_ext fun g => by
    rw [plug_mk, plug_mk]
    unfold plugFun plugOwn
    refine Finset.sum_congr rfl fun q _ => ?_
    show mk R (ownGen _ _ _ (plugY (R := R) L f (update yy a₀ w) a₀ _ _ q))
      = mk R (ownGen _ _ _ _)
    rw [plugY_update_self]

lemma plug_update_add (L : LinOrd A) (m : P A) (f : S → A) (yy : ∀ a, C (Fib f a)) (a₀ a : A)
    (ha : a ≠ a₀) (w w' : C (Fib f a)) (Z : GrComposite R P C (Fib f a₀)) :
    plug R L m f (update yy a (w + w')) a₀ Z
      = plug R L m f (update yy a w) a₀ Z + plug R L m f (update yy a w') a₀ Z := by
  rw [← LinearMap.add_apply]
  congr 1
  refine hom_ext fun g => ?_
  rw [LinearMap.add_apply, plug_mk, plug_mk, plug_mk]
  unfold plugFun plugOwn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  show mkY (plugGen (R := R) L m f yy a₀ g.L (GrOperad.par (R := R) q g.m) (owner g)
      (ownY (R := R) g) q) (plugY (R := R) L f (update yy a (w + w')) a₀ (owner g) _ q)
    = mkY (plugGen (R := R) L m f yy a₀ g.L (GrOperad.par (R := R) q g.m) (owner g)
      (ownY (R := R) g) q) (plugY (R := R) L f (update yy a w) a₀ (owner g) _ q)
      + mkY (plugGen (R := R) L m f yy a₀ g.L (GrOperad.par (R := R) q g.m) (owner g)
      (ownY (R := R) g) q) (plugY (R := R) L f (update yy a w') a₀ (owner g) _ q)
  rw [plugY_update_left _ _ _ _ _ _ _ a ha, plugY_update_left _ _ _ _ _ _ _ a ha,
    plugY_update_left _ _ _ _ _ _ _ a ha, map_add, map_add, MultilinearMap.map_update_add]

lemma plug_update_smul (L : LinOrd A) (m : P A) (f : S → A) (yy : ∀ a, C (Fib f a)) (a₀ a : A)
    (ha : a ≠ a₀) (c : R) (w : C (Fib f a)) (Z : GrComposite R P C (Fib f a₀)) :
    plug R L m f (update yy a (c • w)) a₀ Z = c • plug R L m f (update yy a w) a₀ Z := by
  rw [← LinearMap.smul_apply]
  congr 1
  refine hom_ext fun g => ?_
  rw [LinearMap.smul_apply, plug_mk, plug_mk]
  unfold plugFun plugOwn
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  show mkY (plugGen (R := R) L m f yy a₀ g.L (GrOperad.par (R := R) q g.m) (owner g)
      (ownY (R := R) g) q) (plugY (R := R) L f (update yy a (c • w)) a₀ (owner g) _ q)
    = c • mkY (plugGen (R := R) L m f yy a₀ g.L (GrOperad.par (R := R) q g.m) (owner g)
      (ownY (R := R) g) q) (plugY (R := R) L f (update yy a w) a₀ (owner g) _ q)
  rw [plugY_update_left _ _ _ _ _ _ _ a ha, plugY_update_left _ _ _ _ _ _ _ a ha, map_smul,
    map_smul, MultilinearMap.map_update_smul]

lemma plug_add_m (L : LinOrd A) (m m' : P A) (f : S → A) (yy : ∀ a, C (Fib f a)) (a₀ : A) :
    plug R L (m + m') f yy a₀ = plug R L m f yy a₀ + plug R L m' f yy a₀ :=
  hom_ext fun g => by
    rw [LinearMap.add_apply, plug_mk, plug_mk, plug_mk]
    unfold plugFun plugOwn
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    dsimp only [plugGen]
    rw [map_add, LinearMap.add_apply]
    exact mk_add_m (plugGen (R := R) L m f yy a₀ g.L (GrOperad.par (R := R) q g.m) (owner g)
      (ownY (R := R) g) q) _

lemma plug_smul_m (L : LinOrd A) (c : R) (m : P A) (f : S → A) (yy : ∀ a, C (Fib f a))
    (a₀ : A) : plug R L (c • m) f yy a₀ = c • plug R L m f yy a₀ :=
  hom_ext fun g => by
    rw [LinearMap.smul_apply, plug_mk, plug_mk]
    unfold plugFun plugOwn
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    dsimp only [plugGen]
    rw [map_smul, LinearMap.smul_apply]
    exact mk_smul_m (plugGen (R := R) L m f yy a₀ g.L (GrOperad.par (R := R) q g.m) (owner g)
      (ownY (R := R) g) q) c

end PlugReorder

/-! ## Relabelling the outer operation of a plug -/

section RelabelOuter

variable {S : Type} [Fintype S] [DecidableEq S] {A : Type} [Fintype A] [DecidableEq A]
  {A₂ : Type} [Fintype A₂] [DecidableEq A₂]

omit [Fintype S] [DecidableEq S] [Fintype A] [Fintype A₂] in
lemma plugOwner_compEquiv {A' : Type} (σ : A₂ ≃ A) (f : S → A) (a₂ : A₂)
    (f' : Fib f (σ a₂) → A') :
    (compEquiv σ (Equiv.refl A') a₂).symm ∘ plugOwner f (σ a₂) f'
      = plugOwner (σ.symm ∘ f) a₂ (f' ∘ (fibOuter σ f a₂).symm) := by
  funext s
  simp only [comp_apply, plugOwner]
  by_cases h : f s = σ a₂
  · have h' : σ.symm (f s) = a₂ := by rw [h, σ.symm_apply_apply]
    rw [dif_pos h, dif_pos h']
    rfl
  · have h' : σ.symm (f s) ≠ a₂ := fun e => h (by rw [← e, σ.apply_symm_apply])
    rw [dif_neg h, dif_neg h']
    rfl

omit [Fintype A] [Fintype A₂] in
lemma map_compEquiv_linOrd {A' : Type} [DecidableEq A'] (σ : A₂ ≃ A) (L : LinOrd A) (a₂ : A₂)
    (L' : LinOrd A') :
    LinOrd.map (compEquiv σ (Equiv.refl A') a₂).symm (LinOrd.comp (σ a₂) L L')
      = LinOrd.comp a₂ (LinOrd.map σ.symm L) L' := by
  ext x z
  rcases x with x | x <;> rcases z with z | z <;> exact Iff.rfl

/-- **Plugging commutes with relabelling the outer operation.** -/
lemma plugOwn_relabelOuter {A' : Type} [Fintype A'] [DecidableEq A'] (σ : A₂ ≃ A) (L : LinOrd A)
    (m₂ : P A₂) (f : S → A) (yy : ∀ a, C (Fib f a)) (a₂ : A₂) (L' : LinOrd A') (m' : P A')
    (f' : Fib f (σ a₂) → A') (yy' : ∀ a', C (Fib f' a')) :
    plugOwn R L (GrOperad.map (R := R) σ m₂) f yy (σ a₂) L' m' f' yy'
      = plugOwn R (LinOrd.map σ.symm L) m₂ (σ.symm ∘ f)
          (fun a => GrOperad.map (R := R) (fibOuter σ f a) (yy (σ a))) a₂ L' m'
          (f' ∘ (fibOuter σ f a₂).symm)
          (fun a' => GrOperad.map (R := R) (fibMap (fibOuter σ f a₂) f' a') (yy' a')) := by
  unfold plugOwn
  refine Finset.sum_congr rfl fun q _ => ?_
  dsimp only [plugGen]
  have hc : GrOperad.comp (R := R) (σ a₂) (GrOperad.map (R := R) σ m₂) (GrOperad.par (R := R) q m')
      = GrOperad.map (R := R) (compEquiv σ (Equiv.refl A') a₂)
          (GrOperad.comp (R := R) a₂ m₂ (GrOperad.par (R := R) q m')) := by
    rw [GrOperad.map_comp, GrOperad.map_refl]
  rw [hc]
  refine (mk_ownGen_outer (compEquiv σ (Equiv.refl A') a₂) (LinOrd.comp (σ a₂) L L')
      (GrOperad.comp (R := R) a₂ m₂ (GrOperad.par (R := R) q m')) (plugOwner f (σ a₂) f')
      _).trans ?_
  rw [map_compEquiv_linOrd, mk_ownGen_congr _ _ (plugOwner_compEquiv σ f a₂ f')]
  congr 2
  funext x
  rcases x with b | a'
  · show GrOperad.map (R := R) _ (GrOperad.map (R := R) _ (GrOperad.map (R := R)
        (plugNe f (σ a₂) f' ⟨σ b.1, _⟩)
        (GrOperad.tw (R := R) (P := C) (q && ltB L (σ b.1) (σ a₂)) (yy (σ b.1)))))
      = GrOperad.map (R := R) (plugNe (σ.symm ∘ f) a₂ (f' ∘ (fibOuter σ f a₂).symm) b)
          (GrOperad.tw (R := R) (P := C) (q && ltB L (σ b.1) (σ a₂))
            (GrOperad.map (R := R) (fibOuter σ f b.1) (yy (σ b.1))))
    rw [← GrOperad.map_tw]
    simp only [← GrOperad.map_trans]
    exact gmap_congr (fun _ => rfl) _
  · show GrOperad.map (R := R) _ (GrOperad.map (R := R) _ (GrOperad.map (R := R)
        (plugEq f (σ a₂) f' a') (yy' a')))
      = GrOperad.map (R := R) (plugEq (σ.symm ∘ f) a₂ (f' ∘ (fibOuter σ f a₂).symm) a')
          (GrOperad.map (R := R) (fibMap (fibOuter σ f a₂) f' a') (yy' a'))
    simp only [← GrOperad.map_trans]
    exact gmap_congr (fun _ => rfl) _

/-- **Plugging commutes with relabelling the outer operation**, on elements. -/
lemma plug_relabelOuter (σ : A₂ ≃ A) (L : LinOrd A) (m₂ : P A₂) (f : S → A)
    (yy : ∀ a, C (Fib f a)) (a₂ : A₂) (Z : GrComposite R P C (Fib f (σ a₂))) :
    plug R L (GrOperad.map (R := R) σ m₂) f yy (σ a₂) Z
      = plug R (LinOrd.map σ.symm L) m₂ (σ.symm ∘ f)
          (fun a => GrOperad.map (R := R) (fibOuter σ f a) (yy (σ a))) a₂
          (map (fibOuter σ f a₂) Z) := by
  have h : plug R L (GrOperad.map (R := R) σ m₂) f yy (σ a₂)
      = (plug R (LinOrd.map σ.symm L) m₂ (σ.symm ∘ f)
          (fun a => GrOperad.map (R := R) (fibOuter σ f a) (yy (σ a))) a₂).comp
        (map (fibOuter σ f a₂)) := hom_ext fun g => by
    rw [LinearMap.comp_apply, mk_eq_ownGen (R := R) g, map_mk_ownGen, plug_mk_ownGen,
      plug_mk_ownGen]
    exact plugOwn_relabelOuter σ L m₂ f yy a₂ g.L g.m (owner g) _
  exact LinearMap.congr_fun h Z

end RelabelOuter

end GrComposite

end Operad
