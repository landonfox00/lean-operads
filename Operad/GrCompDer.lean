/-
# Derivations of `P ∘ C` along the inner operations

For graded operads `P` and `C`, a family `Φ : C → P ∘ C` of parity `e`, commuting with the
relabellings (`GrComposite.InnerOp`), extends to an operator `D_Φ` of parity `e` on `P ∘ C`
(`GrComposite.plugDer`): apply `Φ` to one inner operation and plug the result in its place, with
the Koszul sign of `Φ` passing the outer operation and the inner operations read before,

  `D_Φ (m ⊗ y₁ ⊗ ⋯ ⊗ yₖ) = ∑ₐ ± m ∘ₐ Φ(yₐ)`.

For instance, for the free graded operad `C = T(W)` and `α : W → P`, `Φ = (α ∘ 1) ∘ ρ` gives
the left twisted differential, cutting the root vertex of an inner tree and composing its image
under `α` into the outer operation.
-/
import Operad.GrCompPlug

universe u v w

namespace Operad

open Function Sym GerBV

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrOperad R C]

namespace GrComposite

variable (R P C) in
/-- **An operation of parity `e` from `C` to `P ∘ C`**, commuting with the relabellings. -/
structure InnerOp (e : Bool) where
  /-- The components. -/
  app (B : Type) [Fintype B] [DecidableEq B] : C B →ₗ[R] GrComposite R P C B
  app_map {B B' : Type} [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] (τ : B ≃ B')
    (x : C B) : app B' (GrOperad.map (R := R) τ x) = map τ (app B x)
  app_par {B : Type} [Fintype B] [DecidableEq B] (b : Bool) (x : C B) :
    GrSpecies.par (R := R) b (app B x) = app B (GrOperad.par (R := R) (xor b e) x)

variable {e : Bool} (Φ : InnerOp R P C e)

lemma InnerOp.par_app_hom {B : Type} [Fintype B] [DecidableEq B] {c : Bool} {x : C B}
    (hx : GrOperad.par (R := R) c x = x) :
    GrSpecies.par (R := R) (xor c e) (Φ.app B x) = Φ.app B x := by
  rw [Φ.app_par, Bool.xor_assoc, Bool.xor_self, Bool.xor_false, hx]

/-! ## The operator on generators -/

section Own

variable {S : Type} [Fintype S] [DecidableEq S] {A : Type} [Fintype A] [DecidableEq A]

/-- The inner operations twisted by `e` when read before `a₀`. -/
noncomputable def twBefore (L : LinOrd A) (e : Bool) (a₀ : A) {B : A → Type}
    [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (yy : ∀ a, C (B a)) : ∀ a, C (B a) :=
  fun a => GrOperad.tw (R := R) (P := C) (e && ltB L a a₀) (yy a)

omit [Fintype A] in
lemma twBefore_update (L : LinOrd A) (e : Bool) (a₀ : A) {B : A → Type}
    [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (yy : ∀ a, C (B a)) (a : A) (w : C (B a)) :
    twBefore (R := R) L e a₀ (update yy a w)
      = update (twBefore (R := R) L e a₀ yy) a (GrOperad.tw (R := R) (P := C) (e && ltB L a a₀) w)
    := funext fun a' =>
  apply_update (fun a' => ⇑(GrOperad.tw (R := R) (P := C) (A := B a') (e && ltB L a' a₀))) yy a w a'

variable (R) in
/-- **The operator on generators given by owners**: `Φ` applied at every inner operation, plugged
in its place. -/
noncomputable def derOwn (L : LinOrd A) (m : P A) (f : S → A) (yy : ∀ a, C (Fib f a)) :
    GrComposite R P C S :=
  ∑ a₀, plug R L (GrOperad.tw (R := R) e m) f (twBefore (R := R) L e a₀ yy) a₀
    (Φ.app _ (yy a₀))

lemma derOwn_add_m (L : LinOrd A) (m m' : P A) (f : S → A) (yy : ∀ a, C (Fib f a)) :
    derOwn R Φ L (m + m') f yy = derOwn R Φ L m f yy + derOwn R Φ L m' f yy := by
  unfold derOwn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a₀ _ => ?_
  rw [map_add, plug_add_m, LinearMap.add_apply]

lemma derOwn_smul_m (L : LinOrd A) (c : R) (m : P A) (f : S → A) (yy : ∀ a, C (Fib f a)) :
    derOwn R Φ L (c • m) f yy = c • derOwn R Φ L m f yy := by
  unfold derOwn
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun a₀ _ => ?_
  rw [map_smul, plug_smul_m, LinearMap.smul_apply]

lemma derOwn_update_add (L : LinOrd A) (m : P A) (f : S → A) (yy : ∀ a, C (Fib f a)) (a : A)
    (w w' : C (Fib f a)) :
    derOwn R Φ L m f (update yy a (w + w'))
      = derOwn R Φ L m f (update yy a w) + derOwn R Φ L m f (update yy a w') := by
  unfold derOwn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a₀ _ => ?_
  simp only [twBefore_update]
  by_cases h : a₀ = a
  · subst h
    simp only [plug_update_self, update_self, map_add]
  · rw [update_of_ne h, update_of_ne h, update_of_ne h, map_add,
      plug_update_add _ _ _ _ _ _ (Ne.symm h)]

lemma derOwn_update_smul (L : LinOrd A) (m : P A) (f : S → A) (yy : ∀ a, C (Fib f a)) (a : A)
    (c : R) (w : C (Fib f a)) :
    derOwn R Φ L m f (update yy a (c • w)) = c • derOwn R Φ L m f (update yy a w) := by
  unfold derOwn
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun a₀ _ => ?_
  simp only [twBefore_update]
  by_cases h : a₀ = a
  · subst h
    simp only [plug_update_self, update_self, map_smul]
  · rw [update_of_ne h, update_of_ne h, map_smul, plug_update_smul _ _ _ _ _ _ (Ne.symm h)]

/-- **The operator commutes with relabelling the outer operation.** -/
lemma derOwn_outer {A₂ : Type} [Fintype A₂] [DecidableEq A₂] (σ : A₂ ≃ A) (L : LinOrd A)
    (m₂ : P A₂) (f : S → A) (yy : ∀ a, C (Fib f a)) :
    derOwn R Φ L (SymSpecies.map (R := R) σ m₂) f yy
      = derOwn R Φ (LinOrd.map σ.symm L) m₂ (σ.symm ∘ f)
          (fun a₂ => GrOperad.map (R := R) (fibOuter σ f a₂) (yy (σ a₂))) := by
  unfold derOwn
  rw [← σ.sum_comp]
  refine Finset.sum_congr rfl fun a₂ _ => ?_
  show plug R L (GrOperad.tw (R := R) e (GrOperad.map (R := R) σ m₂)) f _ (σ a₂) _ = _
  rw [← GrOperad.map_tw, plug_relabelOuter, ← Φ.app_map]
  congr 2
  funext a
  show GrOperad.map (R := R) _ (GrOperad.tw (R := R) (P := C) _ (yy (σ a))) = _
  rw [GrOperad.map_tw]
  rfl

lemma derOwn_congr (L : LinOrd A) (m : P A) {f f' : S → A} (hf : f = f') (yy : ∀ a, C (Fib f a)) :
    derOwn R Φ L m f yy = derOwn R Φ L m f' (fun a =>
      GrOperad.map (R := R) (Equiv.subtypeEquivRight fun s => by rw [hf]) (yy a)) := by
  subst hf
  congr 1
  funext a
  rw [show (Equiv.subtypeEquivRight _ : Fib f a ≃ Fib f a) = Equiv.refl _ from
    Equiv.ext fun _ => rfl, GrOperad.map_refl]

omit [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] in
lemma twBefore_hom (L : LinOrd A) (a₀ : A) {B : A → Type} [∀ a, Fintype (B a)]
    [∀ a, DecidableEq (B a)] (yy : ∀ a, C (B a)) (c : A → Bool)
    (hy : ∀ a, GrOperad.par (R := R) (c a) (yy a) = yy a) :
    twBefore (R := R) L e a₀ yy = fun a => (if ltB L a a₀ then σ R (e && c a) else 1) • yy a := by
  funext a
  unfold twBefore
  rw [GrOperad.tw_hom _ (hy a)]
  by_cases h : ltB L a a₀ <;> simp [h]

/-- **Reordering the inner operations**, homogeneous. -/
lemma derOwn_reorder (L L₂ : LinOrd A) (m : P A) (f : S → A) (yy : ∀ a, C (Fib f a))
    (c : A → Bool) (hy : ∀ a, GrOperad.par (R := R) (c a) (yy a) = yy a) :
    derOwn R Φ L m f yy = GrEnd.rsg R L L₂ c • derOwn R Φ L₂ m f yy := by
  unfold derOwn
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun a₀ _ => ?_
  have hZ := Φ.par_app_hom (hy a₀)
  rw [twBefore_hom L a₀ yy c hy, twBefore_hom L₂ a₀ yy c hy,
    plug_smul_family _ _ _ _ _ _ (by rw [ltB_self, if_neg Bool.false_ne_true]),
    plug_smul_family _ _ _ _ _ _ (by rw [ltB_self, if_neg Bool.false_ne_true]),
    plug_reorder L L₂ _ f yy a₀ c (fun a _ => hy a) _ _ hZ, smul_smul, smul_smul]
  rw [rsg_update_mul (R := R) L L₂ c a₀ e]

end Own

/-! ## The operator -/

section Der

variable {S : Type} [Fintype S] [DecidableEq S]

variable (R) in
/-- The operator on a generator. -/
noncomputable def derFun (g : GrCompGen P C S) : GrComposite R P C S :=
  derOwn R Φ g.L g.m (owner g) (ownY (R := R) g)

lemma derFun_respects : GrCompGen.Respects R (derFun R Φ (S := S)) where
  add_m g m' := derOwn_add_m Φ g.L g.m m' (owner g) (ownY (R := R) g)
  smul_m g c := derOwn_smul_m Φ g.L c g.m (owner g) (ownY (R := R) g)
  add_y g a w w' := by
    show derOwn R Φ g.L g.m (owner g) (ownY (R := R) { g with y := update g.y a (w + w') })
      = derOwn R Φ g.L g.m (owner g) (ownY (R := R) { g with y := update g.y a w })
        + derOwn R Φ g.L g.m (owner g) (ownY (R := R) { g with y := update g.y a w' })
    rw [ownY_update, ownY_update, ownY_update, map_add, derOwn_update_add]
  smul_y g a c w := by
    show derOwn R Φ g.L g.m (owner g) (ownY (R := R) { g with y := update g.y a (c • w) })
      = c • derOwn R Φ g.L g.m (owner g) (ownY (R := R) { g with y := update g.y a w })
    rw [ownY_update, ownY_update, map_smul, derOwn_update_smul]
  outer := @fun g A _ _ σ m => by
    show derOwn R Φ g.L (SymSpecies.map (R := R) σ m) (owner g) (ownY (R := R) g) = _
    rw [derOwn_outer, derFun, derOwn_congr _ _ m (owner_outer g σ m).symm]
    congr 1
    funext a'
    simp only [ownY, ← GrOperad.map_trans]
    apply gmap_congr
    intro b
    rfl
  inner := @fun g B _ _ τ => by
    show derOwn R Φ g.L g.m _ (ownY (R := R) (⟨g.A, B, g.L, g.m,
      fun a => SymSpecies.map (R := R) (τ a) (g.y a),
      (Equiv.sigmaCongrRight τ).symm.trans g.e⟩ : GrCompGen P C S)) = derFun R Φ g
    unfold derFun
    congr 1
    funext a
    apply gmap_comp_congr
    intro b
    exact Subtype.ext (show g.e ⟨a, (τ a).symm (τ a b)⟩ = g.e ⟨a, b⟩ by
      rw [Equiv.symm_apply_apply])
  reorder g L' c hy := derOwn_reorder Φ g.L L' g.m (owner g) (ownY (R := R) g) c fun a => by
    show GrOperad.par (R := R) (c a) (GrOperad.map (R := R) _ (g.y a)) = _
    rw [← GrOperad.map_par]
    exact congrArg _ (hy a)

variable (R) in
/-- **The operator `D_Φ`**: `Φ` applied at every inner operation and plugged in its place. -/
noncomputable def plugDer : GrComposite R P C S →ₗ[R] GrComposite R P C S :=
  lift (derFun R Φ) (derFun_respects Φ)

@[simp] lemma plugDer_mk (g : GrCompGen P C S) : plugDer R Φ (mk R g) = derFun R Φ g :=
  lift_mk _ _ g

lemma plugDer_mk_ownGen {A : Type} [Fintype A] [DecidableEq A] (L : LinOrd A) (m : P A)
    (f : S → A) (yy : ∀ a, C (Fib f a)) :
    plugDer R Φ (mk R (ownGen L m f yy)) = derOwn R Φ L m f yy := by
  rw [plugDer_mk, derFun, ownY_ownGen]
  rfl

end Der

end GrComposite

end Operad
