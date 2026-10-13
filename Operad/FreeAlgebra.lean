/-
# Free algebras over a symmetric operad

The free algebra over a symmetric operad `P` on a module `V` is the Schur functor
`S(P, V) = ⊕ₙ P(n) ⊗_{Σₙ} V^{⊗n}`, on which an operation acts by total composition: on classes of
generators, `p · (q_a ⊗ w_a)_a = total(p; q_a) ⊗ (w_a)_a` (`Schur.act_mkA`).

* **Algebras act through total composition** (`SymAlgebra.act_total`): in any algebra,
  `total(p; q_a)` acts as `p` on the actions of the `q_a`.
* `Schur.algebra`: the algebra structure of the Schur functor, a morphism of operads
  `P → End(S(P, V))`, and `Schur.ι : V →ₗ S(P, V)`, the classes of the unit.
* `SymAlgebraHom`: the morphisms of algebras, the linear maps commuting with the actions.
* **The universal property** (`Schur.liftEquiv`): the morphisms of algebras from the free algebra
  to an algebra `W` are the linear maps `V → W`, through `Schur.ι`.
-/
import Operad.Schur
import Operad.MayClass
import Operad.EndOperad

universe u v w x

namespace Operad

open DirectSum Function May

namespace Sym

section ActTotal

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]
  {V : Type v} [AddCommGroup V] [Module R V]
  {A : Type} [Fintype A] [DecidableEq A] {B : A → Type} [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]

/-- **Filling acts by substitution** at the filled inputs. -/
lemma SymAlgebra.act_fill (α : SymAlgebra R P V) (p : P A) (q : ∀ a, P (B a)) (l : List A)
    (hl : l.Nodup) (v : Stage B l → V) :
    α.act (SymOperad.fill R p q l hl) v = α.act p fun a =>
      if h : a ∈ l then α.act (q a) (fun b => v (Sum.inr ⟨⟨a, h⟩, b⟩))
      else v (Sum.inl ⟨a, h⟩) := by
  induction l with
  | nil =>
    rw [SymOperad.fill_nil, SymAlgebra.act_map]
    congr 1
  | cons a l ih =>
    have ha := (List.nodup_cons.1 hl).1
    rw [SymOperad.fill_cons, SymAlgebra.act_map, SymAlgebra.act_comp, ih]
    congr 1
    funext c
    by_cases hc : c ∈ l
    · rw [dif_pos hc, dif_pos (List.mem_cons_of_mem a hc)]
      congr 1
    · rw [dif_neg hc]
      by_cases hca : c = a
      · subst hca
        rw [dif_pos List.mem_cons_self, feed_self]
        rfl
      · rw [dif_neg (by simp [hca, hc]), feed_of_ne (show (Sum.inl ⟨c, hc⟩ : Stage B l)
          ≠ Sum.inl ⟨a, ha⟩ from fun h => hca (congrArg Subtype.val (Sum.inl_injective h)))]
        rfl

/-- **Algebras act through total composition**: `total(p; q_a)` acts as `p` on the actions of the
`q_a`. -/
theorem SymAlgebra.act_total (α : SymAlgebra R P V) (p : P A) (q : ∀ a, P (B a))
    (v : (Σ a, B a) → V) :
    α.act (SymOperad.total R p q) v = α.act p fun a => α.act (q a) fun b => v ⟨a, b⟩ := by
  have hc : ∀ a, a ∈ (Finset.univ : Finset A).toList :=
    fun a => Finset.mem_toList.2 (Finset.mem_univ a)
  rw [SymOperad.total_eq_fill p q _ (Finset.nodup_toList _) hc, SymAlgebra.act_map,
    SymAlgebra.act_fill]
  congr 1
  funext a
  rw [dif_pos (hc a)]
  rfl

end ActTotal

/-! ## Morphisms of algebras -/

section Hom

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]
  {V : Type v} [AddCommGroup V] [Module R V] {W : Type x} [AddCommGroup W] [Module R W]

/-- **A morphism of algebras** over a symmetric operad: a linear map commuting with the
actions. -/
structure SymAlgebraHom (α : SymAlgebra R P V) (β : SymAlgebra R P W) where
  /-- The underlying linear map. -/
  toLinearMap : V →ₗ[R] W
  /-- It commutes with the actions. -/
  map_act {A : Type} [Fintype A] [DecidableEq A] (p : P A) (v : A → V) :
    toLinearMap (α.act p v) = β.act p fun a => toLinearMap (v a)

namespace SymAlgebraHom

variable {α : SymAlgebra R P V} {β : SymAlgebra R P W}

@[ext] lemma ext {F G : SymAlgebraHom α β} (h : F.toLinearMap = G.toLinearMap) : F = G := by
  cases F
  cases G
  congr

/-- The identity morphism. -/
def id (α : SymAlgebra R P V) : SymAlgebraHom α α where
  toLinearMap := LinearMap.id
  map_act _ _ := rfl

/-- The composite of two morphisms. -/
def comp {U : Type*} [AddCommGroup U] [Module R U] {γ : SymAlgebra R P U}
    (G : SymAlgebraHom β γ) (F : SymAlgebraHom α β) : SymAlgebraHom α γ where
  toLinearMap := G.toLinearMap ∘ₗ F.toLinearMap
  map_act p v := by
    rw [LinearMap.comp_apply, F.map_act, G.map_act]
    rfl

@[simp] lemma id_toLinearMap : (id α).toLinearMap = LinearMap.id := rfl

@[simp] lemma comp_toLinearMap {U : Type*} [AddCommGroup U] [Module R U]
    {γ : SymAlgebra R P U} (G : SymAlgebraHom β γ) (F : SymAlgebraHom α β) :
    (G.comp F).toLinearMap = G.toLinearMap ∘ₗ F.toLinearMap :=
  rfl

end SymAlgebraHom

end Hom

end Sym

/-! ## Partial composition through total composition -/

namespace SymOperad

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable (R) in
/-- **The padded family**, in an operad in modules: `y` at `i` and the unit at every other
input. -/
noncomputable def pad (i : A) (y : P B) (a : A) : P (Pad i B a) :=
  if h : a = i then map (R := R) (padIn h) y else map (R := R) (padOut h) (one R)

/-- **Partial composition through total composition**: insert `y` at `i` and the unit at every
other input. -/
theorem comp_eq_total (i : A) (x : P A) (y : P B) :
    comp (R := R) i x y = map (R := R) (padEquiv i B) (total R x (pad R i y)) :=
  (MaySetOperad.comp_toMaySetOperad (S := Und R P) i x y).symm

lemma eq_map_symm_of_map_eq (e : A ≃ B) {x : P A} {y : P B} (h : map (R := R) e x = y) :
    x = map (R := R) e.symm y := by
  rw [← h, ← map_trans, Equiv.self_trans_symm, map_refl]

end SymOperad

/-! ## The free algebra -/

namespace Schur

open Sym

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]
  {V : Type v} [AddCommGroup V] [Module R V]
  {A : Type} [Fintype A] [DecidableEq A]

/-- **Multilinear maps on the Schur functor agree when they agree on generators.** -/
theorem ml_ext {W : Type x} [AddCommGroup W] [Module R W]
    {f g : MultilinearMap R (fun _ : A => Schur R P V) W}
    (h : ∀ (n : A → ℕ) (q : ∀ a, P (Fin (n a))) (w : ∀ a, Fin (n a) → V),
      f (fun a => mk R (n a) (q a) (w a)) = g (fun a => mk R (n a) (q a) (w a))) : f = g := by
  refine ML.quot_ext (schurRel R P V) fun x => ?_
  have := ML.ds_ext (f := f.compLinearMap fun _ => (schurRel R P V).mkQ)
    (g := g.compLinearMap fun _ => (schurRel R P V).mkQ) fun n t =>
      h n (fun a => (t a).1) (fun a => (t a).2)
  exact congrArg (fun F => F x) this

/-- The action of an operation on generators. -/
noncomputable def actGen (p : P A) (n : A → ℕ) (t : ∀ a, SchurGen P V (n a)) : Schur R P V :=
  mkA R (SymOperad.total R p fun a => (t a).1) fun x => (t x.1).2 x.2

lemma actGen_update (p : P A) (n : A → ℕ) (t : ∀ a, SchurGen P V (n a)) (i : A)
    (q : P (Fin (n i))) (w : Fin (n i) → V) :
    actGen p n (update t i (q, w))
      = mkA R (SymOperad.total R p (update (fun a => (t a).1) i q))
          (fun x => update (fun a => (t a).2) i w x.1 x.2) := by
  have h1 : (fun a => (update t i (q, w) a).1) = update (fun a => (t a).1) i q :=
    funext fun a => apply_update (fun a (y : SchurGen P V (n a)) => y.1) t i (q, w) a
  have h2 : (fun x : Σ a, Fin (n a) => (update t i (q, w) x.1).2 x.2)
      = fun x => update (fun a => (t a).2) i w x.1 x.2 :=
    funext fun x => congrFun
      (apply_update (fun a (y : SchurGen P V (n a)) => y.2) t i (q, w) x.1) x.2
  unfold actGen
  rw [h1, h2]

omit [Fintype A] [DecidableEq A] in
lemma sigmaCongr_mk {A' : Type} {B : A → Type} {B' : A' → Type} (f : A ≃ A')
    (F : ∀ a, B a ≃ B' (f a)) (a : A) (b : B a) : Equiv.sigmaCongr f F ⟨a, b⟩ = ⟨f a, F a b⟩ :=
  rfl

/-- `Schur.mkA_map` for an operad. -/
lemma mkA_map' {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    (p : P A) (v : B → V) : mkA R (SymOperad.map (R := R) e p) v = mkA R p (v ∘ e) :=
  mkA_map e p v

omit [Fintype A] [AddCommGroup V] in
lemma sigma_update {B : A → Type} [∀ a, DecidableEq (B a)] (W : ∀ a, B a → V) (i : A)
    (w : B i → V) (j : B i) (c : V) :
    (fun x : Σ a, B a => update W i (update w j c) x.1 x.2)
      = update (fun x : Σ a, B a => update W i w x.1 x.2) ⟨i, j⟩ c := by
  funext ⟨a, b⟩
  by_cases ha : a = i
  · subst ha
    by_cases hb : b = j
    · subst hb
      simp
    · rw [update_of_ne (fun h => hb (eq_of_heq (Sigma.mk.inj h).2))]
      simp [update_of_ne hb]
  · rw [update_of_ne (fun h => ha (congrArg Sigma.fst h))]
    simp [update_of_ne ha]

omit [SymOperad R P] in
lemma lift_single_one {X W : Type*} [AddCommGroup W] [Module R W] (f : X → W) (x : X) :
    Finsupp.lift W R X f (Finsupp.single x 1) = f x := by
  simp

/-- **The relations are respected** in each argument. -/
lemma actGen_rel (p : P A) (n : A → ℕ) (t : ∀ a, SchurGen P V (n a)) (i : A) :
    schurRelSet R P V (n i) ⊆ LinearMap.ker
      (Finsupp.lift (Schur R P V) R (SchurGen P V (n i)) fun y => actGen p n (update t i y)) := by
  rintro r ((((⟨q, q', w, rfl⟩ | ⟨c, q, w, rfl⟩) | ⟨q, w, j, y, y', rfl⟩) |
    ⟨q, w, j, c, y, rfl⟩) | ⟨σ, q, w, rfl⟩) <;>
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, lift_single_one,
      actGen_update]
  · rw [SymOperad.total_update_add, mkA_add]
    abel
  · rw [SymOperad.total_update_smul, mkA_smul, sub_self]
  · rw [sigma_update, sigma_update, sigma_update, mkA_update_add]
    abel
  · rw [sigma_update, sigma_update, mkA_update_smul, sub_self]
  · rw [sub_eq_zero]
    let τ : ∀ a, Fin (n a) ≃ Fin (n a) := update (fun a => Equiv.refl (Fin (n a))) i σ
    have hτ := SymOperad.total_map (R := R) (Equiv.refl A) τ p (update (fun a => (t a).1) i q)
      (update (fun a => (t a).1) i (SymOperad.map (R := R) σ q)) fun a => by
        by_cases ha : a = i
        · subst ha
          simp only [τ, Equiv.refl_apply, update_self]
          rfl
        · simp only [τ, Equiv.refl_apply, update_of_ne ha]
          exact (SymOperad.map_refl _).symm
    rw [SymOperad.map_refl] at hτ
    rw [show SymSpecies.map (R := R) σ q = SymOperad.map (R := R) σ q from rfl, ← hτ, mkA_map']
    congr 1
    funext ⟨a, b⟩
    simp only [comp_apply, sigmaCongr_mk, Equiv.refl_apply]
    by_cases ha : a = i
    · subst ha
      simp only [τ, update_self, comp_apply]
      rfl
    · simp only [τ, update_of_ne ha]
      rfl

/-- The action on the free module of generators. -/
noncomputable def actPre (p : P A) :
    MultilinearMap R (fun _ : A => SchurPre R P V) (Schur R P V) :=
  ML.dsLift fun n t => actGen p n t

/-- **The action of an operation on the Schur functor.** -/
noncomputable def act (p : P A) : MultilinearMap R (fun _ : A => Schur R P V) (Schur R P V) :=
  ML.liftQ (schurRel R P V) (actPre p) fun x i hx =>
    ML.dsLift_eq_zero _ (schurRelSet R P V) (fun n t i => actGen_rel p n t i) x i hx

/-- **The action on generators**: by total composition. -/
lemma act_mk (p : P A) (n : A → ℕ) (q : ∀ a, P (Fin (n a))) (w : ∀ a, Fin (n a) → V) :
    act p (fun a => mk R (n a) (q a) (w a))
      = mkA R (SymOperad.total R p q) fun x => w x.1 x.2 := by
  unfold act actPre
  exact (ML.liftQ_mkQ _ _ _ _).trans (ML.dsLift_lof_single (R := R) (X := SchurGen P V)
    (fun n t => actGen p n t) n fun a => (q a, w a))

/-- **The action on classes of operations with any finite types of inputs.** -/
lemma act_mkA {B : A → Type} [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (p : P A)
    (q : ∀ a, P (B a)) (w : ∀ a, B a → V) :
    act p (fun a => mkA R (q a) (w a)) = mkA R (SymOperad.total R p q) fun x => w x.1 x.2 := by
  let φ : ∀ a, B a ≃ Fin (Fintype.card (B a)) := fun a => Fintype.equivFin (B a)
  have h := SymOperad.total_map (R := R) (Equiv.refl A) φ p q
    (fun a => SymOperad.map (R := R) (φ a) (q a)) fun a => rfl
  rw [SymOperad.map_refl] at h
  show act p (fun a => mk R _ (SymOperad.map (R := R) (φ a) (q a)) (w a ∘ (φ a).symm)) = _
  rw [act_mk, ← h, mkA_map']
  congr 1
  funext ⟨a, b⟩
  show w a ((φ a).symm (φ a b)) = w a b
  rw [Equiv.symm_apply_apply]

lemma act_add (p p' : P A) : act (p + p') = (act p + act p' :
    MultilinearMap R (fun _ : A => Schur R P V) (Schur R P V)) :=
  ml_ext fun n q w => by
    rw [MultilinearMap.add_apply, act_mk, act_mk, act_mk, SymOperad.total_add, mkA_add]

lemma act_smul (c : R) (p : P A) : act (c • p) = (c • act p :
    MultilinearMap R (fun _ : A => Schur R P V) (Schur R P V)) :=
  ml_ext fun n q w => by
    rw [MultilinearMap.smul_apply, act_mk, act_mk, SymOperad.total_smul, mkA_smul]

/-- **Equivariance of the action.** -/
lemma act_map {A' : Type} [Fintype A'] [DecidableEq A'] (e : A ≃ A') (p : P A)
    (s : A' → Schur R P V) : act (SymOperad.map (R := R) e p) s = act p fun a => s (e a) := by
  have := ml_ext (f := act (R := R) (V := V) (SymOperad.map (R := R) e p))
    (g := (act (R := R) (V := V) p).domDomCongr e)
    fun n q w => by
      rw [MultilinearMap.domDomCongr_apply, act_mk, act_mk]
      rw [← SymOperad.total_map (R := R) e (fun a => Equiv.refl (Fin (n (e a)))) p
        (fun a => q (e a)) q fun a => (SymOperad.map_refl _).symm, mkA_map']
      rfl
  exact congrArg (fun F => F s) this

/-- **The unit acts as the identity.** -/
lemma act_one (s : Unit → Schur R P V) : act (SymOperad.one R : P Unit) s = s () := by
  have := ml_ext (f := act (R := R) (V := V) (SymOperad.one R : P Unit))
    (g := EndOp.one R (Schur R P V)) fun n q w => by
      rw [EndOp.one_apply, act_mk, SymOperad.eq_map_symm_of_map_eq _
        (SymOperad.total_one_left (R := R) q), mkA_map', ← mkA_fin]
      rfl
  exact congrArg (fun F => F s) this

/-- **Total composites act through the actions**, on generators. -/
lemma act_total_mk {B : A → Type} [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (p : P A)
    (q : ∀ a, P (B a)) (m : (Σ a, B a) → ℕ) (Q : ∀ z, P (Fin (m z)))
    (W : ∀ z, Fin (m z) → V) :
    act (SymOperad.total R p q) (fun z => mk R (m z) (Q z) (W z))
      = act p fun a => act (q a) fun b => mk R (m ⟨a, b⟩) (Q ⟨a, b⟩) (W ⟨a, b⟩) := by
  simp only [act_mk]
  rw [act_mkA, ← SymOperad.total_assoc (R := R) p q fun a b => Q ⟨a, b⟩, mkA_map']
  rfl

/-- **Partial composites act by substitution.** -/
lemma act_comp {B : Type} [Fintype B] [DecidableEq B] (i : A) (x : P A) (y : P B)
    (s : Without A i ⊕ B → Schur R P V) :
    act (SymOperad.comp (R := R) i x y) s = act x (feed i s (act y fun b => s (Sum.inr b))) := by
  have := ml_ext (f := act (R := R) (V := V) (SymOperad.comp (R := R) i x y))
    (g := EndOp.compML R (Schur R P V) i (act x) (act y)) fun n q w => by
      rw [EndOp.compML_apply, SymOperad.comp_eq_total, act_map, act_total_mk]
      congr 1
      funext a
      by_cases ha : a = i
      · subst ha
        rw [feed_self, SymOperad.pad, dif_pos rfl, act_map]
        rfl
      · rw [feed_of_ne ha, SymOperad.pad, dif_neg ha, act_map, act_one]
        rfl
  exact congrArg (fun F => F s) this

variable (R P V) in
/-- **The free algebra** over `P` on `V`: the Schur functor, on which operations act by total
composition. -/
noncomputable def algebra : SymAlgebra R P (Schur R P V) where
  app _ _ _ :=
    { toFun := act
      map_add' := act_add
      map_smul' := act_smul }
  app_map e p := MultilinearMap.ext fun s => act_map e p s
  app_one := MultilinearMap.ext fun s => act_one s
  app_comp i x y := MultilinearMap.ext fun s => act_comp i x y s

@[simp] lemma algebra_act (p : P A) (s : A → Schur R P V) :
    (algebra R P V).act p s = act p s :=
  rfl

/-! ### The universal property -/

omit [Fintype A] [DecidableEq A] in
lemma unit_fun (z : V) : (fun _ : Unit => z) = update (fun _ : Unit => (0 : V)) () z := by
  funext u
  cases u
  simp

variable (R P V) in
/-- **The generators of the free algebra**: the classes of the unit. -/
noncomputable def ι : V →ₗ[R] Schur R P V where
  toFun v := mkA R (SymOperad.one R : P Unit) fun _ => v
  map_add' v v' := by
    rw [unit_fun (v + v'), mkA_update_add, ← unit_fun, ← unit_fun]
  map_smul' c v := by
    simp only [RingHom.id_apply]
    rw [unit_fun (c • v), mkA_update_smul, ← unit_fun]

lemma ι_apply (v : V) : ι R P V v = mkA R (SymOperad.one R : P Unit) fun _ => v :=
  rfl

/-- **The generators of the Schur functor are the actions on generators of the free
algebra.** -/
lemma mk_eq_act (n : ℕ) (q : P (Fin n)) (w : Fin n → V) :
    mk R n q w = act q fun k => ι R P V (w k) := by
  simp only [ι_apply]
  rw [act_mkA, SymOperad.eq_map_symm_of_map_eq _ (SymOperad.total_one_right (R := R) q),
    mkA_map', ← mkA_fin]
  rfl

variable {W : Type x} [AddCommGroup W] [Module R W]

/-- The family of maps defining the morphism of algebras extending a linear map. -/
noncomputable def liftFam (β : SymAlgebra R P W) (φ : V →ₗ[R] W) (n : ℕ) :
    P (Fin n) →ₗ[R] MultilinearMap R (fun _ : Fin n => V) W where
  toFun q := (β.app (Fin n) q).compLinearMap fun _ => φ
  map_add' q q' := by
    ext v
    simp
  map_smul' c q := by
    ext v
    simp

lemma liftFam_apply (β : SymAlgebra R P W) (φ : V →ₗ[R] W) (n : ℕ) (q : P (Fin n))
    (v : Fin n → V) : liftFam β φ n q v = β.act q fun k => φ (v k) :=
  rfl

lemma liftFam_compatible (β : SymAlgebra R P W) (φ : V →ₗ[R] W) :
    Compatible (liftFam β φ) := fun n σ q v => by
  rw [liftFam_apply, liftFam_apply]
  exact SymAlgebra.act_map β σ q _

lemma lift_liftFam_mkA (β : SymAlgebra R P W) (φ : V →ₗ[R] W) (p : P A) (v : A → V) :
    lift (liftFam β φ) (liftFam_compatible β φ) (mkA R p v) = β.act p fun a => φ (v a) := by
  rw [mkA, lift_mk, liftFam_apply]
  exact (SymAlgebra.act_map β _ p _).trans (by simp)

/-- **The morphism of algebras extending a linear map.** -/
noncomputable def liftHom (β : SymAlgebra R P W) (φ : V →ₗ[R] W) :
    SymAlgebraHom (algebra R P V) β where
  toLinearMap := lift (liftFam β φ) (liftFam_compatible β φ)
  map_act {A} _ _ p s := by
    have := ml_ext (A := A) (f := (lift (liftFam β φ) (liftFam_compatible β φ)).compMultilinearMap
        (act (R := R) (V := V) p))
      (g := (β.app A p).compLinearMap fun _ => lift (liftFam β φ) (liftFam_compatible β φ))
      fun n q w => by
        rw [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply, act_mk,
          lift_liftFam_mkA, SymAlgebra.act_total]
        simp only [lift_mk, liftFam_apply]
        rfl
    exact congrArg (fun F => F s) this

@[simp] lemma liftHom_ι (β : SymAlgebra R P W) (φ : V →ₗ[R] W) (v : V) :
    (liftHom β φ).toLinearMap (ι R P V v) = φ v := by
  show lift (liftFam β φ) (liftFam_compatible β φ) (mkA R (SymOperad.one R : P Unit) fun _ => v)
    = φ v
  rw [lift_liftFam_mkA, SymAlgebra.act_one]

/-- **Morphisms out of the free algebra agree when they agree on generators.** -/
theorem algHom_ext {β : SymAlgebra R P W} {F G : SymAlgebraHom (algebra R P V) β}
    (h : ∀ v, F.toLinearMap (ι R P V v) = G.toLinearMap (ι R P V v)) : F = G := by
  refine SymAlgebraHom.ext (hom_ext fun n q w => ?_)
  rw [mk_eq_act, ← algebra_act, F.map_act, G.map_act]
  simp only [h]

/-- **The universal property of the free algebra**: morphisms of algebras out of it are the
linear maps out of `V`. -/
noncomputable def liftEquiv (β : SymAlgebra R P W) :
    SymAlgebraHom (algebra R P V) β ≃ (V →ₗ[R] W) where
  toFun F := F.toLinearMap ∘ₗ ι R P V
  invFun φ := liftHom β φ
  left_inv F := algHom_ext fun v => by
    rw [liftHom_ι]
    rfl
  right_inv φ := LinearMap.ext fun v => liftHom_ι β φ v

@[simp] lemma liftEquiv_apply (β : SymAlgebra R P W) (F : SymAlgebraHom (algebra R P V) β) :
    liftEquiv β F = F.toLinearMap ∘ₗ ι R P V :=
  rfl

@[simp] lemma liftEquiv_symm_apply (β : SymAlgebra R P W) (φ : V →ₗ[R] W) :
    (liftEquiv β).symm φ = liftHom β φ :=
  rfl

end Schur

end Operad
