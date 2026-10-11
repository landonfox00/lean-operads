/-
# The associativity of the composition product

The associator `(M ∘ N) ∘ L → M ∘ (N ∘ L)` of `Operad.Composite` is an isomorphism. Its inverse
sends `⟨m; w; e⟩`, with `w a` the class of `⟨n a; l a; f a⟩` in `(N ∘ L)(B a)`, to the class of
`⟨⟨m; n⟩; l; e'⟩`. It is multilinear in the classes `w a`: on representatives it is defined on
tuples of generators (`Operad.ML.finsuppLift'`), and it respects the relations of each `N ∘ L`
(`Operad.ML.finsuppLift'_eq_zero`). To check a relation in one slot, the slots are renumbered
by `Option` so that the slot is `none` (`Operad.Composite.phi_reindex`); relabellings in that
slot are then isomorphisms of families of generators (`Operad.Composite.phi_iso`).

* `Operad.Composite.assocInvApp`: the inverse associator.
* `Operad.Composite.assocEquiv`: **the associator `(M ∘ N) ∘ L ≅ M ∘ (N ∘ L)`**.
-/
import Operad.Composite

universe u v w x

namespace Operad

open Function

namespace Composite

variable {R : Type u} [CommRing R]
  {M : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M A)] [SymSpecies R M]
  {N : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N A)] [SymSpecies R N]
  {L : (A : Type) → [Fintype A] → [DecidableEq A] → Type x}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (L A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (L A)] [SymSpecies R L]
  {S : Type} [Fintype S] [DecidableEq S]

/-! ## The inverse associator on tuples of generators -/

section PhiGen

variable {A : Type} [Fintype A] [DecidableEq A] {B : A → Type}

/-- The naming of the inputs in the inverse associator. -/
def phiE (e : (Σ a, B a) ≃ S) (t : ∀ a, CompGen N L (B a)) :
    (Σ p : Σ a, (t a).A, (t p.1).B p.2) ≃ S :=
  (Equiv.sigmaAssoc fun a c => (t a).B c).trans ((Equiv.sigmaCongrRight fun a => (t a).e).trans e)

variable (R) in
/-- The generator of `(M ∘ N) ∘ L` of the inverse associator, on a tuple of generators. -/
noncomputable abbrev phiGen (m : M A) (e : (Σ a, B a) ≃ S) (t : ∀ a, CompGen N L (B a)) :
    CompGen (Composite R M N) L S :=
  ⟨Σ a, (t a).A, fun p => (t p.1).B p.2,
    mk R ⟨A, fun a => (t a).A, m, fun a => (t a).m, Equiv.refl _⟩, fun p => (t p.1).y p.2,
    phiE e t⟩

/-- **Renumbering the inputs of the outer operation.** -/
theorem phi_reindex {A' : Type} [Fintype A'] [DecidableEq A'] (σ : A' ≃ A) (m' : M A')
    (e : (Σ a, B a) ≃ S) (t : ∀ a, CompGen N L (B a)) :
    mk R (phiGen R (SymSpecies.map (R := R) σ m') e t)
      = mk R (phiGen R (B := fun a' => B (σ a')) m' ((Equiv.sigmaCongrLeft σ).trans e)
          fun a' => t (σ a')) := by
  have hx : (mk R ⟨A, fun a => (t a).A, SymSpecies.map (R := R) σ m', fun a => (t a).m,
      Equiv.refl _⟩ : Composite R M N _)
      = SymSpecies.map (R := R) (V := Composite R M N)
          (Equiv.sigmaCongrLeft (β := fun a => (t a).A) σ)
          (mk R ⟨A', fun a' => (t (σ a')).A, m', fun a' => (t (σ a')).m, Equiv.refl _⟩) := by
    rw [symSpecies_map_mk]
    exact mk_outer (R := R) ⟨A, fun a => (t a).A, SymSpecies.map (R := R) σ m',
      fun a => (t a).m, Equiv.refl _⟩ σ m'
  show mk R ⟨_, _, mk R ⟨A, _, SymSpecies.map (R := R) σ m', _, _⟩, _, _⟩ = _
  rw [hx]
  refine (mk_outer (phiGen R (SymSpecies.map (R := R) σ m') e t)
    (Equiv.sigmaCongrLeft (β := fun a => (t a).A) σ) _).trans ?_
  exact mk_congr_e _ _ fun ⟨⟨_, _⟩, _⟩ => rfl

/-- **Isomorphic tuples of generators give the same value.** -/
theorem phi_iso (m : M A) (e : (Σ a, B a) ≃ S) (t₁ t₂ : ∀ a, CompGen N L (B a))
    (σ : ∀ a, (t₂ a).A ≃ (t₁ a).A) (ρ : ∀ a c, (t₂ a).B c ≃ (t₁ a).B (σ a c))
    (hm : ∀ a, (t₁ a).m = SymSpecies.map (R := R) (σ a) (t₂ a).m)
    (hy : ∀ a c, (t₁ a).y (σ a c) = SymSpecies.map (R := R) (ρ a c) ((t₂ a).y c))
    (he : ∀ a c d, (t₂ a).e ⟨c, d⟩ = (t₁ a).e ⟨σ a c, ρ a c d⟩) :
    mk R (phiGen R m e t₁) = mk R (phiGen R m e t₂) := by
  let τ : (Σ a, (t₂ a).A) ≃ Σ a, (t₁ a).A := Equiv.sigmaCongrRight σ
  have hx : (mk R ⟨A, fun a => (t₁ a).A, m, fun a => (t₁ a).m, Equiv.refl _⟩ :
      Composite R M N _) = SymSpecies.map (R := R) (V := Composite R M N) τ
        (mk R ⟨A, fun a => (t₂ a).A, m, fun a => (t₂ a).m, Equiv.refl _⟩) := by
    rw [symSpecies_map_mk]
    have h1 := mk_inner (R := R) (M := M) (N := N) ⟨A, fun a => (t₂ a).A, m, fun a => (t₂ a).m,
      τ⟩ (B := fun a => (t₁ a).A) σ
    rw [Equiv.symm_trans_self, ← funext hm] at h1
    exact h1
  show mk R ⟨_, _, mk R ⟨A, fun a => (t₁ a).A, m, fun a => (t₁ a).m, Equiv.refl _⟩, _, _⟩ = _
  rw [hx]
  refine (mk_outer (phiGen R m e t₁) τ _).trans ?_
  let ρ' : ∀ p : Σ a, (t₂ a).A, (t₂ p.1).B p.2 ≃ (t₁ (τ p).1).B (τ p).2 := fun p => ρ p.1 p.2
  have hl : (fun p : Σ a, (t₂ a).A => (t₁ (τ p).1).y (τ p).2)
      = fun p => SymSpecies.map (R := R) (ρ' p) ((t₂ p.1).y p.2) :=
    funext fun p => hy p.1 p.2
  have h2 := mk_inner (R := R) (M := Composite R M N) (N := L) (phiGen R m e t₂)
    (B := fun p => (t₁ (τ p).1).B (τ p).2) ρ'
  rw [Equiv.symm_trans_eq_of (Equiv.sigmaCongrRight ρ') (phiE e t₂)
    ((Equiv.sigmaCongrLeft τ).trans (phiE e t₁)) (fun ⟨⟨a, c⟩, d⟩ => by
      show e ⟨a, (t₂ a).e ⟨c, d⟩⟩ = e ⟨a, (t₁ a).e ⟨σ a c, ρ a c d⟩⟩
      rw [he])] at h2
  rw [← h2]
  exact congrArg (fun y => mk R (⟨Σ a, (t₂ a).A, fun p => (t₁ (τ p).1).B (τ p).2,
    mk R ⟨A, fun a => (t₂ a).A, m, fun a => (t₂ a).m, Equiv.refl _⟩, y,
    (Equiv.sigmaCongrLeft τ).trans (phiE e t₁)⟩ : CompGen (Composite R M N) L S)) hl

/-! ### Linearity in the operations of one generator -/

theorem phi_add_m (m : M A) (e : (Σ a, B a) ≃ S) (T₀ : ∀ a, CompGen N L (B a))
    (F : ∀ a, N ((T₀ a).A)) (a : A) (v v' : N ((T₀ a).A)) :
    mk R (phiGen R m e fun a' => { T₀ a' with m := update F a (v + v') a' })
      = mk R (phiGen R m e fun a' => { T₀ a' with m := update F a v a' })
        + mk R (phiGen R m e fun a' => { T₀ a' with m := update F a v' a' }) := by
  have hx : (mk R ⟨A, fun a' => (T₀ a').A, m, update F a (v + v'), Equiv.refl _⟩ :
      Composite R M N _) = mk R ⟨A, fun a' => (T₀ a').A, m, update F a v, Equiv.refl _⟩
        + mk R ⟨A, fun a' => (T₀ a').A, m, update F a v', Equiv.refl _⟩ :=
    (mkY (R := R) (⟨A, fun a' => (T₀ a').A, m, F, Equiv.refl _⟩ :
      CompGen M N _)).map_update_add F a v v'
  show mk R ⟨_, _, mk R ⟨A, fun a' => (T₀ a').A, m, update F a (v + v'), Equiv.refl _⟩, _, _⟩
    = _
  rw [hx]
  exact mk_add_m (phiGen R m e fun a' => { T₀ a' with m := update F a v a' }) _

theorem phi_smul_m (m : M A) (e : (Σ a, B a) ≃ S) (T₀ : ∀ a, CompGen N L (B a))
    (F : ∀ a, N ((T₀ a).A)) (a : A) (c : R) (v : N ((T₀ a).A)) :
    mk R (phiGen R m e fun a' => { T₀ a' with m := update F a (c • v) a' })
      = c • mk R (phiGen R m e fun a' => { T₀ a' with m := update F a v a' }) := by
  have hx : (mk R ⟨A, fun a' => (T₀ a').A, m, update F a (c • v), Equiv.refl _⟩ :
      Composite R M N _) = c • mk R ⟨A, fun a' => (T₀ a').A, m, update F a v, Equiv.refl _⟩ :=
    (mkY (R := R) (⟨A, fun a' => (T₀ a').A, m, F, Equiv.refl _⟩ :
      CompGen M N _)).map_update_smul F a c v
  show mk R ⟨_, _, mk R ⟨A, fun a' => (T₀ a').A, m, update F a (c • v), Equiv.refl _⟩, _, _⟩
    = _
  rw [hx]
  exact mk_smul_m (phiGen R m e fun a' => { T₀ a' with m := update F a v a' }) c

omit [Fintype A] in
lemma sigma_curry_update {β : A → Type} [∀ a, DecidableEq (β a)] {γ : ∀ a, β a → Type*}
    (G : ∀ a b, γ a b) (a : A) (b : β a) (w : γ a b) :
    (fun p : Σ a, β a => update G a (update (G a) b w) p.1 p.2)
      = update (fun p : Σ a, β a => G p.1 p.2) ⟨a, b⟩ w := by
  funext ⟨a', b'⟩
  by_cases ha : a' = a
  · subst ha
    by_cases hb : b' = b
    · subst hb
      simp
    · simp only [update_self]
      rw [update_of_ne hb, update_of_ne (fun h => hb (eq_of_heq (Sigma.mk.inj_iff.1 h).2))]
  · simp only [update_of_ne ha]
    rw [update_of_ne (fun h => ha (Sigma.mk.inj_iff.1 h).1)]

theorem phi_add_y (m : M A) (e : (Σ a, B a) ≃ S) (T₀ : ∀ a, CompGen N L (B a))
    (G : ∀ a c, L ((T₀ a).B c)) (a : A) (c : (T₀ a).A) (z z' : L ((T₀ a).B c)) :
    mk R (phiGen R m e fun a' => { T₀ a' with y := update G a (update (G a) c (z + z')) a' })
      = mk R (phiGen R m e fun a' => { T₀ a' with y := update G a (update (G a) c z) a' })
        + mk R (phiGen R m e fun a' => { T₀ a' with y := update G a (update (G a) c z') a' }) := by
  have h := (mkY (R := R) (phiGen R m e fun a' => { T₀ a' with y := G a' })).map_update_add
    (fun p => G p.1 p.2) ⟨a, c⟩ z z'
  simp only [← sigma_curry_update] at h
  exact h

theorem phi_smul_y (m : M A) (e : (Σ a, B a) ≃ S) (T₀ : ∀ a, CompGen N L (B a))
    (G : ∀ a c, L ((T₀ a).B c)) (a : A) (c : (T₀ a).A) (r : R) (z : L ((T₀ a).B c)) :
    mk R (phiGen R m e fun a' => { T₀ a' with y := update G a (update (G a) c (r • z)) a' })
      = r • mk R (phiGen R m e fun a' => { T₀ a' with y := update G a (update (G a) c z) a' }) := by
  have h := (mkY (R := R) (phiGen R m e fun a' => { T₀ a' with y := G a' })).map_update_smul
    (fun p => G p.1 p.2) ⟨a, c⟩ r z
  simp only [← sigma_curry_update] at h
  exact h

/-! ### Renumbering a slot as `none` -/

/-- The tuple of generators, renumbered so that the slot `a`, filled with `y`, is `none`. -/
def slotFam (t : ∀ a, CompGen N L (B a)) (a : A) (y : CompGen N L (B a)) :
    ∀ j : Option {a' // a' ≠ a}, CompGen N L (B (Equiv.optionSubtypeNe a j)) :=
  fun j => Option.rec (motive := fun j => CompGen N L (B (Equiv.optionSubtypeNe a j))) y
    (fun j' => t j'.1) j

omit [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (L A)] [Fintype A] in
lemma update_comp_optionSubtypeNe (t : ∀ a, CompGen N L (B a)) (a : A) (y : CompGen N L (B a)) :
    (fun j => update t a y (Equiv.optionSubtypeNe a j)) = slotFam t a y := by
  funext j
  cases j with
  | none => exact update_self a y t
  | some j' => exact update_of_ne j'.2 y t

/-- **The value on a tuple with one slot replaced**, renumbered. -/
theorem phi_update (m : M A) (e : (Σ a, B a) ≃ S) (t : ∀ a, CompGen N L (B a)) (a : A)
    (y : CompGen N L (B a)) :
    mk R (phiGen R m e (update t a y))
      = mk R (phiGen R (B := fun j => B (Equiv.optionSubtypeNe a j))
          (SymSpecies.map (R := R) (Equiv.optionSubtypeNe a).symm m)
          ((Equiv.sigmaCongrLeft (Equiv.optionSubtypeNe a)).trans e) (slotFam t a y)) := by
  conv_lhs => rw [show m = SymSpecies.map (R := R) (Equiv.optionSubtypeNe a)
    (SymSpecies.map (R := R) (Equiv.optionSubtypeNe a).symm m) by
      rw [← SymSpecies.map_trans, Equiv.symm_trans_self, SymSpecies.map_refl]]
  rw [phi_reindex, update_comp_optionSubtypeNe]

/-! ### The relations of each slot -/

/-- **The value respects the relations of `N ∘ L` in each slot.** -/
theorem phi_rel (m : M A) (e : (Σ a, B a) ≃ S) (t : ∀ a, CompGen N L (B a)) (a : A)
    {x : CompGen N L (B a) →₀ R} (hx : CompRel R N L (B a) x) :
    Finsupp.lift (Composite R (Composite R M N) L S) R (CompGen N L (B a))
      (fun y => mk R (phiGen R m e (update t a y))) x = 0 := by
  have hfamM : ∀ (h : CompGen N L (B a)) (v : N h.A), slotFam t a { h with m := v } = fun j =>
      { slotFam t a h j with m := update (fun j => (slotFam t a h j).m) none v j } := by
    intro h v
    funext j
    cases j with
    | none =>
      show { h with m := v } = { h with m := update (fun j => (slotFam t a h j).m) none v none }
      rw [update_self]
    | some j' =>
      show t j'.1 = { t j'.1 with m := update (fun j => (slotFam t a h j).m) none v (some j') }
      rw [update_of_ne (Option.some_ne_none j')]
      rfl
  have hfamY : ∀ (h : CompGen N L (B a)) (Y : ∀ c, L (h.B c)), slotFam t a { h with y := Y } =
      fun j => { slotFam t a h j with y := update (fun j => (slotFam t a h j).y) none Y j } := by
    intro h Y
    funext j
    cases j with
    | none =>
      show { h with y := Y } = { h with y := update (fun j => (slotFam t a h j).y) none Y none }
      rw [update_self]
    | some j' =>
      show t j'.1 = { t j'.1 with y := update (fun j => (slotFam t a h j).y) none Y (some j') }
      rw [update_of_ne (Option.some_ne_none j')]
      rfl
  cases hx with
  | add_m h n' =>
    rw [map_sub, map_sub, Finsupp.lift_single', Finsupp.lift_single', Finsupp.lift_single',
      one_smul, one_smul, one_smul, phi_update, phi_update, phi_update]
    rw [sub_sub, sub_eq_zero, show slotFam t a h = _ from hfamM h h.m, hfamM h (h.m + n'),
      hfamM h n']
    exact phi_add_m _ _ (slotFam t a h) _ none h.m n'
  | smul_m h c =>
    rw [map_sub, map_smul, Finsupp.lift_single', Finsupp.lift_single', one_smul, one_smul,
      phi_update, phi_update]
    rw [sub_eq_zero, show slotFam t a h = _ from hfamM h h.m, hfamM h (c • h.m)]
    exact phi_smul_m _ _ (slotFam t a h) _ none c h.m
  | add_y h c z z' =>
    rw [map_sub, map_sub, Finsupp.lift_single', Finsupp.lift_single', Finsupp.lift_single',
      one_smul, one_smul, one_smul, phi_update, phi_update, phi_update]
    rw [sub_sub, sub_eq_zero, hfamY h (update h.y c (z + z')), hfamY h (update h.y c z),
      hfamY h (update h.y c z')]
    exact phi_add_y _ _ (slotFam t a h) _ none c z z'
  | smul_y h c r z =>
    rw [map_sub, map_smul, Finsupp.lift_single', Finsupp.lift_single', one_smul, one_smul,
      phi_update, phi_update]
    rw [sub_eq_zero, hfamY h (update h.y c (r • z)), hfamY h (update h.y c z)]
    exact phi_smul_y _ _ (slotFam t a h) _ none c r z
  | outer h σ' m'' =>
    rw [map_sub, Finsupp.lift_single', Finsupp.lift_single', one_smul, one_smul, phi_update,
      phi_update, sub_eq_zero]
    refine phi_iso _ _ _ _
      (fun j => Option.rec (motive := fun j => (slotFam t a ⟨_, fun c => h.B (σ' c), m'',
        fun c => h.y (σ' c), (Equiv.sigmaCongrLeft σ').trans h.e⟩ j).A
          ≃ (slotFam t a { h with m := SymSpecies.map (R := R) σ' m'' } j).A) σ'
        (fun _ => Equiv.refl _) j)
      (fun j => Option.rec (motive := fun j => ∀ c, (slotFam t a ⟨_, fun c => h.B (σ' c), m'',
        fun c => h.y (σ' c), (Equiv.sigmaCongrLeft σ').trans h.e⟩ j).B c
          ≃ (slotFam t a { h with m := SymSpecies.map (R := R) σ' m'' } j).B
            (Option.rec (motive := fun j => (slotFam t a ⟨_, fun c => h.B (σ' c), m'',
              fun c => h.y (σ' c), (Equiv.sigmaCongrLeft σ').trans h.e⟩ j).A
                ≃ (slotFam t a { h with m := SymSpecies.map (R := R) σ' m'' } j).A) σ'
              (fun _ => Equiv.refl _) j c)) (fun _ => Equiv.refl _) (fun _ _ => Equiv.refl _) j)
      (fun j => ?_) (fun j c => ?_) (fun j c d => ?_)
    · cases j with
      | none => rfl
      | some j' => exact (SymSpecies.map_refl _).symm
    · cases j with
      | none => exact (SymSpecies.map_refl _).symm
      | some j' => exact (SymSpecies.map_refl _).symm
    · cases j <;> rfl
  | @inner h B' _ _ τ =>
    rw [map_sub, Finsupp.lift_single', Finsupp.lift_single', one_smul, one_smul, phi_update,
      phi_update, sub_eq_zero]
    let y₁ : CompGen N L (B a) := ⟨h.A, B', h.m, fun c => SymSpecies.map (R := R) (τ c) (h.y c),
      (Equiv.sigmaCongrRight τ).symm.trans h.e⟩
    let σ : ∀ j, (slotFam t a h j).A ≃ (slotFam t a y₁ j).A := fun j =>
      Option.rec (motive := fun j => (slotFam t a h j).A ≃ (slotFam t a y₁ j).A) (Equiv.refl _)
        (fun _ => Equiv.refl _) j
    refine phi_iso _ _ _ _ σ
      (fun j => Option.rec (motive := fun j => ∀ c, (slotFam t a h j).B c
          ≃ (slotFam t a y₁ j).B (σ j c)) (fun c => τ c) (fun _ _ => Equiv.refl _) j)
      (fun j => ?_) (fun j c => ?_) (fun j c d => ?_)
    · cases j with
      | none => exact (SymSpecies.map_refl _).symm
      | some j' => exact (SymSpecies.map_refl _).symm
    · cases j with
      | none => rfl
      | some j' => exact (SymSpecies.map_refl _).symm
    · cases j with
      | none =>
        show h.e ⟨c, d⟩ = h.e ⟨c, (τ c).symm (τ c d)⟩
        rw [Equiv.symm_apply_apply]
      | some j' => rfl

/-! ### The multilinear map on the composites of the slots -/

variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]

variable (R) in
/-- **The inverse associator, multilinear in the classes in the slots.** -/
noncomputable def phiML (m : M A) (e : (Σ a, B a) ≃ S) :
    MultilinearMap R (fun a => Composite R N L (B a)) (Composite R (Composite R M N) L S) :=
  ML.liftQ' (fun a => Submodule.span R {x | CompRel R N L (B a) x})
    (ML.finsuppLift' (R := R) fun t => mk R (phiGen R m e t))
    fun x a hx => ML.finsuppLift'_eq_zero _ (fun a => {x | CompRel R N L (B a) x})
      (fun t a x hx => by
        rw [SetLike.mem_coe, LinearMap.mem_ker]
        exact phi_rel m e t a hx) x a hx

lemma phiML_mk (m : M A) (e : (Σ a, B a) ≃ S) (t : ∀ a, CompGen N L (B a)) :
    phiML R m e (fun a => mk R (t a)) = mk R (phiGen R m e t) := by
  show ML.liftQ' _ _ _ (fun a => Submodule.Quotient.mk (Finsupp.single (t a) 1)) = _
  rw [ML.liftQ'_mk, ML.finsuppLift'_single]

/-- **Multilinear maps on the composites of the slots agree when they agree on tuples of
generators.** -/
theorem slots_ext {W : Type*} [AddCommGroup W] [Module R W]
    {f g : MultilinearMap R (fun a => Composite R N L (B a)) W}
    (h : ∀ t : ∀ a, CompGen N L (B a), f (fun a => mk R (t a)) = g (fun a => mk R (t a))) :
    f = g := by
  have h1 : f.compLinearMap (fun a => (Submodule.span R {x | CompRel R N L (B a) x}).mkQ)
      = g.compLinearMap (fun a => (Submodule.span R {x | CompRel R N L (B a) x}).mkQ) :=
    ML.finsupp_ext' fun t => h t
  exact ML.quot_ext' (fun a => Submodule.span R {x | CompRel R N L (B a) x}) fun x =>
    congrArg (fun F : MultilinearMap R (fun a => CompGen N L (B a) →₀ R) W => F x) h1

end PhiGen

/-- **A multilinear map reindexed** along a bijection of its arguments. -/
def ML.reindex {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι'] {X : ι → Type*}
    [∀ i, AddCommGroup (X i)] [∀ i, Module R (X i)] {W : Type*} [AddCommGroup W] [Module R W]
    (σ : ι' ≃ ι) (f : MultilinearMap R (fun i' => X (σ i')) W) : MultilinearMap R X W :=
  MultilinearMap.mk' (fun w => f fun i' => w (σ i'))
    (fun w i v v' => by
      obtain ⟨i', rfl⟩ := σ.surjective i
      simp only [update_comp_eq_of_injective' w σ.injective]
      exact f.map_update_add _ i' v v')
    (fun w i c v => by
      obtain ⟨i', rfl⟩ := σ.surjective i
      simp only [update_comp_eq_of_injective' w σ.injective]
      exact f.map_update_smul _ i' c v)

omit [Fintype S] [DecidableEq S] in
lemma ML.reindex_apply {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι'] {X : ι → Type*}
    [∀ i, AddCommGroup (X i)] [∀ i, Module R (X i)] {W : Type*} [AddCommGroup W] [Module R W]
    (σ : ι' ≃ ι) (f : MultilinearMap R (fun i' => X (σ i')) W) (w : ∀ i, X i) :
    ML.reindex σ f w = f fun i' => w (σ i') :=
  rfl

variable (R M N L) in
/-- The inverse associator on generators. -/
noncomputable def assocInvFun (g : CompGen M (Composite R N L) S) :
    Composite R (Composite R M N) L S :=
  phiML R g.m g.e g.y

lemma assocInvFun_respects : CompGen.Respects R (assocInvFun R M N L (S := S)) where
  add_m g m' := by
    have h : phiML R (N := N) (L := L) (g.m + m') g.e = phiML R g.m g.e + phiML R m' g.e :=
      slots_ext fun t => by
      rw [MultilinearMap.add_apply, phiML_mk, phiML_mk, phiML_mk]
      have hx : (mk R ⟨g.A, fun a => (t a).A, g.m + m', fun a => (t a).m, Equiv.refl _⟩ :
          Composite R M N _) = mk R ⟨g.A, fun a => (t a).A, g.m, fun a => (t a).m, Equiv.refl _⟩
            + mk R ⟨g.A, fun a => (t a).A, m', fun a => (t a).m, Equiv.refl _⟩ :=
        mk_add_m (R := R) (⟨g.A, fun a => (t a).A, g.m, fun a => (t a).m, Equiv.refl _⟩ :
          CompGen M N _) m'
      show mk R ⟨_, _, mk R ⟨g.A, fun a => (t a).A, g.m + m', fun a => (t a).m,
        Equiv.refl _⟩, _, _⟩ = _
      rw [hx]
      exact mk_add_m (phiGen R g.m g.e t) _
    exact congrArg (fun F : MultilinearMap R _ _ => F g.y) h
  smul_m g c := by
    have h : phiML R (N := N) (L := L) (c • g.m) g.e = c • phiML R g.m g.e :=
      slots_ext fun t => by
      rw [MultilinearMap.smul_apply, phiML_mk, phiML_mk]
      have hx : (mk R ⟨g.A, fun a => (t a).A, c • g.m, fun a => (t a).m, Equiv.refl _⟩ :
          Composite R M N _)
            = c • mk R ⟨g.A, fun a => (t a).A, g.m, fun a => (t a).m, Equiv.refl _⟩ :=
        mk_smul_m (R := R) (⟨g.A, fun a => (t a).A, g.m, fun a => (t a).m, Equiv.refl _⟩ :
          CompGen M N _) c
      show mk R ⟨_, _, mk R ⟨g.A, fun a => (t a).A, c • g.m, fun a => (t a).m,
        Equiv.refl _⟩, _, _⟩ = _
      rw [hx]
      exact mk_smul_m (phiGen R g.m g.e t) c
    exact congrArg (fun F : MultilinearMap R _ _ => F g.y) h
  add_y g a z z' := (phiML R g.m g.e).map_update_add g.y a z z'
  smul_y g a c z := (phiML R g.m g.e).map_update_smul g.y a c z
  outer := @fun g A' _ _ σ m' => by
    have h : phiML R (N := N) (L := L) (SymSpecies.map (R := R) σ m') g.e
        = ML.reindex σ (phiML R (B := fun a' => g.B (σ a')) m'
          ((Equiv.sigmaCongrLeft σ).trans g.e)) := slots_ext fun t => by
      rw [ML.reindex_apply, phiML_mk, phiML_mk (B := fun a' => g.B (σ a'))]
      exact phi_reindex σ m' g.e t
    exact congrArg (fun F : MultilinearMap R _ _ => F g.y) h
  inner := @fun g B' _ _ τ => by
    have h : (phiML R (N := N) (L := L) (B := B') g.m
        ((Equiv.sigmaCongrRight τ).symm.trans g.e)).compLinearMap
        (fun a => SymSpecies.map (R := R) (V := Composite R N L) (τ a)) = phiML R g.m g.e :=
      slots_ext fun t => by
        rw [MultilinearMap.compLinearMap_apply]
        simp only [symSpecies_map_mk]
        rw [phiML_mk (B := B'), phiML_mk]
        exact (mk_congr_e _ _ fun ⟨⟨a, c⟩, d⟩ => by
          show g.e ((Equiv.sigmaCongrRight τ).symm ⟨a, τ a ((t a).e ⟨c, d⟩)⟩)
            = g.e ⟨a, (t a).e ⟨c, d⟩⟩
          rw [Equiv.sigmaCongrRight_symm, Equiv.sigmaCongrRight_apply, Equiv.symm_apply_apply])
    exact congrArg (fun F : MultilinearMap R _ _ => F g.y) h

/-- The components of the inverse associator. -/
noncomputable def assocInvApp (S : Type) [Fintype S] [DecidableEq S] :
    Composite R M (Composite R N L) S →ₗ[R] Composite R (Composite R M N) L S :=
  lift (assocInvFun R M N L) assocInvFun_respects

lemma assocInvApp_mk (g : CompGen M (Composite R N L) S) :
    assocInvApp S (mk R g) = phiML R g.m g.e g.y :=
  lift_mk _ _ g

theorem assocInvApp_assocApp (z : Composite R (Composite R M N) L S) :
    assocInvApp S (assocApp S z) = z := by
  have h : (assocInvApp (R := R) (M := M) (N := N) (L := L) S).comp (assocApp S)
      = LinearMap.id :=
    hom_ext fun h => by
      rw [LinearMap.comp_apply, assocApp_mk, LinearMap.id_apply]
      show assocInvApp S (assocLin h.B h.e h.m h.y) = mkM h h.m
      induction h.m using induction_on with
      | h0 => simp only [map_zero, MultilinearMap.zero_apply]
      | hadd x y hx hy => simp only [map_add, MultilinearMap.add_apply, hx, hy]
      | hsmul c x hx => simp only [map_smul, MultilinearMap.smul_apply, hx]
      | hmk k =>
        rw [assocLin_mk, assocInvApp_mk, phiML_mk, mkM_apply]
        have hk : (mk R k : Composite R M N h.A)
            = SymSpecies.map (R := R) (V := Composite R M N) k.e
              (mk R ⟨k.A, k.B, k.m, k.y, Equiv.refl _⟩) := by
          rw [symSpecies_map_mk]
          rfl
        rw [hk]
        refine Eq.trans ?_ (mk_outer h k.e _).symm
        exact mk_congr_e _ _ fun ⟨⟨_, _⟩, _⟩ => rfl
  exact LinearMap.congr_fun h z

theorem assocApp_assocInvApp (z : Composite R M (Composite R N L) S) :
    assocApp S (assocInvApp S z) = z := by
  have h : (assocApp (R := R) (M := M) (N := N) (L := L) S).comp (assocInvApp S)
      = LinearMap.id :=
    hom_ext fun g => by
      rw [LinearMap.comp_apply, assocInvApp_mk, LinearMap.id_apply]
      show (assocApp S).compMultilinearMap (phiML R g.m g.e) g.y = mkY g g.y
      congr 1
      refine slots_ext fun t => ?_
      rw [LinearMap.compMultilinearMap_apply, phiML_mk, assocApp_mk, assocLin_mk, mkY_apply]
      let k₀ : CompGen M N (Σ a, (t a).A) :=
        ⟨g.A, fun a => (t a).A, g.m, fun a => (t a).m, Equiv.refl _⟩
      have ht : (fun a => mk R (t a)) = fun a => SymSpecies.map (R := R) (V := Composite R N L)
          (t a).e (mk R (assocInner k₀ (fun p => (t p.1).B p.2) (fun p => (t p.1).y p.2) a)) :=
        funext fun a => by
          rw [symSpecies_map_mk]
          rfl
      rw [ht]
      have h3 := mk_inner (R := R) (assocGen R k₀ (fun p => (t p.1).B p.2)
        (fun p => (t p.1).y p.2) (phiE g.e t)) (B := g.B) fun a => (t a).e
      rw [Equiv.symm_trans_eq_of _ _ g.e (fun ⟨_, _, _⟩ => rfl)] at h3
      exact h3.symm
  exact LinearMap.congr_fun h z

/-- **The associator `(M ∘ N) ∘ L ≅ M ∘ (N ∘ L)`**, as a linear equivalence in each arity. -/
noncomputable def assocEquiv (S : Type) [Fintype S] [DecidableEq S] :
    Composite R (Composite R M N) L S ≃ₗ[R] Composite R M (Composite R N L) S :=
  LinearEquiv.ofLinear (assocApp S) (assocInvApp S) (LinearMap.ext assocApp_assocInvApp)
    (LinearMap.ext assocInvApp_assocApp)

@[simp] lemma assocEquiv_apply (z : Composite R (Composite R M N) L S) :
    assocEquiv S z = assoc.app S z :=
  rfl

end Composite

end Operad
