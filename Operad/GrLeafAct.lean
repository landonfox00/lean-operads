/-
# Derivations at the inner operations and the right action

For a derivation `D` of parity `q` of a graded operad `C`, the operator `1 ∘' D` of `V ∘ C`
applying `D` at each inner operation in turn (`GrComposite.leafMap`) satisfies the Leibniz rule
with the right action of `C` (`GrComposite.leafMap_act`):

  `(1 ∘' D) (w ◁ᵢ z) = (1 ∘' D) w ◁ᵢ z + (-1)^{q |w|} w ◁ᵢ D z`.

It is checked on homogeneous generators given by owners, where both sides are signed generators
(`GrComposite.act_ownGen_hom`, `GrComposite.leafMap_ownGen_hom`).
-/
import Operad.GrCompAct

universe u v w

namespace Operad

open Function Sym GerBV

variable {R : Type u} [CommRing R]
  {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrOperad R C]

/-- **A derivation of a graded operad**, as an endomorphism of its graded linear species. -/
def GrDer.toSpEnd {q : Bool} (D : GrDer (GrOperadHom.id R C) q) : GrSpEnd R C q where
  app A _ _ := D.app A
  app_map σ' x := D.app_map σ' x
  app_par c x := D.app_par c x

namespace GrComposite

variable {S : Type} [Fintype S] [DecidableEq S] {Y : Type} [Fintype Y] [DecidableEq Y]
  {A : Type} [Fintype A] [DecidableEq A]

/-! ## Signed generators -/

omit [Fintype S] [DecidableEq S] in
lemma mk_ownGen_smul_y [Fintype S] [DecidableEq S] (L : LinOrd A) (m : V A) (f : S → A)
    (y : ∀ a, C (Fib f a)) (s : A → R) :
    mk R (ownGen L m f fun a => s a • y a) = (∏ a, s a) • mk R (ownGen L m f y) :=
  (mkY (R := R) (ownGen L m f y)).map_smul_univ s y

/-- **The action of a homogeneous operation on a homogeneous generator**, as a signed
generator. -/
lemma act_ownGen_hom (L : LinOrd A) (m : V A) (f : S → A) (y : ∀ a, C (Fib f a))
    (c : A → Bool) (hy : ∀ a, GrOperad.par (R := R) (c a) (y a) = y a) (i : S) (z : C Y)
    {r : Bool} (hz : GrOperad.par (R := R) r z = z) :
    act R V i z (mk R (ownGen L m f y))
      = (∏ a, if ltB L (f i) a then σ R (r && c a) else 1)
        • mk R (ownGen L m (actOwner f i) (actY (R := R) L f y i z false)) := by
  rw [act_mk_ownGen, actOwn_hom _ _ _ _ _ _ hz, ← mk_ownGen_smul_y]
  show mk R (ownGen L m (actOwner f i) (actY (R := R) L f y i z r)) = _
  rw [show actY (R := R) L f y i z r = fun a => _ from funext (actY_hom L f y i z r c hy)]

/-- **An endomorphism at the inner operations of a homogeneous generator**, as a sum of signed
generators. -/
lemma leafMap_ownGen_hom {q : Bool} (gm : GrSpEnd R C q) (L : LinOrd A) (m : V A) (f : S → A)
    (y : ∀ a, C (Fib f a)) {p : Bool} (hm : GrSpecies.par (R := R) p m = m) (c : A → Bool)
    (hy : ∀ a, GrOperad.par (R := R) (c a) (y a) = y a) :
    leafMap R V gm (mk R (ownGen L m f y))
      = ∑ j, (σ R (q && p) * ∏ a, if ltB L a j then σ R (q && c a) else 1)
          • mk R (ownGen L m f (update y j (gm.app _ (y j)))) := by
  rw [leafMap_mk]
  unfold leafFun
  refine Finset.sum_congr rfl fun j _ => ?_
  have hy' : (fun a => leafLin gm L j a (y a)) = fun a =>
      (if a = j then 1 else if ltB L a j then σ R (q && c a) else 1)
        • update y j (gm.app _ (y j)) a := by
    funext a
    unfold leafLin
    by_cases h : a = j
    · subst h
      simp
    · simp only [if_neg h, update_of_ne h]
      split_ifs
      · exact GrSpecies.tw_hom (R := R) (V := C) q (hy a)
      · simp
  have hp : ∏ a : A, (if a = j then (1 : R) else if ltB L a j then σ R (q && c a) else 1)
      = ∏ a, if ltB L a j then σ R (q && c a) else 1 :=
    Finset.prod_congr rfl fun a _ => by
      by_cases h : a = j
      · subst h
        simp
      · rw [if_neg h]
  show mk R ⟨A, Fib f, L, GrSpecies.tw (R := R) q m, fun a => leafLin gm L j a (y a),
    Equiv.sigmaFiberEquiv f⟩ = _
  rw [GrSpecies.tw_hom (R := R) q hm, hy', mul_smul, ← hp, ← mk_ownGen_smul_y]
  exact mk_smul_m (ownGen L m f fun a =>
    (if a = j then 1 else if ltB L a j then σ R (q && c a) else 1)
      • update y j (gm.app _ (y j)) a) _

omit [Fintype S] [DecidableEq S] in
/-- **The sign twist of a homogeneous generator.** -/
lemma tw_mk_hom [Fintype S] [DecidableEq S] (e : Bool) (g : GrCompGen V C S) {p : Bool}
    {c : g.A → Bool} (hm : GrSpecies.par (R := R) p g.m = g.m)
    (hy : ∀ a, GrSpecies.par (R := R) (c a) (g.y a) = g.y a) :
    GrSpecies.tw (R := R) e (mk R g) = σ R (e && xor p (GrEnd.tot c)) • mk R g := by
  rw [GrSpecies.tw_apply, grSpecies_par_mk, grSpecies_par_mk, parFun_hom _ _ hm hy,
    parFun_hom _ _ hm hy]
  cases xor p (GrEnd.tot c) <;> simp

/-! ## The sign identities -/

omit [DecidableEq A] in
lemma prod_update_σ (L : LinOrd A) (j k : A) [DecidableEq A] (q r : Bool) (c : A → Bool) :
    (∏ a, if ltB L a j then σ R (q && update c k (xor (c k) r) a) else 1)
      = (∏ a, if ltB L a j then σ R (q && c a) else 1) * (if ltB L k j then σ R (q && r) else 1)
    := by
  have h : ∀ a, (if ltB L a j then σ R (q && update c k (xor (c k) r) a) else 1)
      = (if ltB L a j then σ R (q && c a) else 1)
        * (if a = k then (if ltB L k j then σ R (q && r) else 1) else 1) := fun a => by
    by_cases ha : a = k
    · subst ha
      rw [update_self, if_pos rfl, GrEnd.σ_and_xor]
      split_ifs <;> simp
    · rw [update_of_ne ha, if_neg ha, mul_one]
  rw [Finset.prod_congr rfl fun a _ => h a, Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

omit [DecidableEq A] in
lemma prod_update_σ' (L : LinOrd A) (j k : A) [DecidableEq A] (q r : Bool) (c : A → Bool) :
    (∏ a, if ltB L k a then σ R (r && update c j (xor (c j) q) a) else 1)
      = (∏ a, if ltB L k a then σ R (r && c a) else 1) * (if ltB L k j then σ R (r && q) else 1)
    := by
  have h : ∀ a, (if ltB L k a then σ R (r && update c j (xor (c j) q) a) else 1)
      = (if ltB L k a then σ R (r && c a) else 1)
        * (if a = j then (if ltB L k j then σ R (r && q) else 1) else 1) := fun a => by
    by_cases ha : a = j
    · subst ha
      rw [update_self, if_pos rfl, GrEnd.σ_and_xor]
      split_ifs <;> simp
    · rw [update_of_ne ha, if_neg ha, mul_one]
  rw [Finset.prod_congr rfl fun a _ => h a, Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

/-- The signs at an inner operation other than the one receiving the inserted operation. -/
lemma sign_leaf_act (L : LinOrd A) (j k : A) (q r p : Bool) (c : A → Bool) :
    (∏ a, if ltB L k a then σ R (r && c a) else 1)
        * (σ R (q && p) * ∏ a, if ltB L a j then σ R (q && update c k (xor (c k) r) a) else 1)
      = (σ R (q && p) * ∏ a, if ltB L a j then σ R (q && c a) else 1)
        * ∏ a, if ltB L k a then σ R (r && update c j (xor (c j) q) a) else 1 := by
  rw [prod_update_σ, prod_update_σ']
  have : σ R (q && r) = σ R (r && q) := by rw [Bool.and_comm]
  rw [this]
  ring

/-- The signs of the inserted operation receiving the derivation. -/
lemma sign_leaf_act_self (L : LinOrd A) (k : A) (q r p : Bool) (c : A → Bool) :
    (∏ a, if ltB L k a then σ R (r && c a) else 1)
        * ((σ R (q && p) * ∏ a, if ltB L a k then σ R (q && update c k (xor (c k) r) a) else 1)
          * σ R (q && c k))
      = σ R (q && xor p (GrEnd.tot c)) * ∏ a, if ltB L k a then σ R (xor r q && c a) else 1 := by
  have h1 : (∏ a, if ltB L a k then σ R (q && update c k (xor (c k) r) a) else 1)
      = ∏ a, if ltB L a k then σ R (q && c a) else 1 :=
    Finset.prod_congr rfl fun a _ => by
      by_cases ha : a = k
      · subst ha
        simp
      · rw [update_of_ne ha]
  have h2 : (∏ a, if ltB L k a then σ R (xor r q && c a) else 1)
      = (∏ a, if ltB L k a then σ R (r && c a) else 1)
        * ∏ a, if ltB L k a then σ R (q && c a) else 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    split_ifs <;> simp [GrEnd.σ_xor_and]
  have h3 : σ R (q && GrEnd.tot c) = ∏ a, σ R (q && c a) := (GrEnd.prod_σ_tot q c).symm
  have h4 : (∏ a, if ltB L a k then σ R (q && c a) else 1) * σ R (q && c k)
      = (∏ a, σ R (q && c a)) * ∏ a, if ltB L k a then σ R (q && c a) else 1 := by
    have h5 : σ R (q && c k) = ∏ a, if a = k then σ R (q && c a) else 1 := by
      rw [Finset.prod_ite_eq']
      simp
    rw [h5, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    by_cases hak : a = k
    · subst hak
      simp
    · rw [if_neg hak, mul_one]
      by_cases h : ltB L a k
      · have h' : ltB L k a = false := by
          rw [ltB_swap L hak, h, Bool.not_true]
        rw [if_pos h, h', if_neg Bool.false_ne_true, mul_one]
      · have h' : ltB L k a = true := by
          rw [ltB_swap L hak, Bool.eq_false_iff.2 h, Bool.not_false]
        rw [if_neg h, h', if_pos rfl, σ_mul_self]
  rw [h1, h2, GrEnd.σ_and_xor, h3]
  rw [show (∏ a, if ltB L k a then σ R (r && c a) else 1)
      * ((σ R (q && p) * ∏ a, if ltB L a k then σ R (q && c a) else 1) * σ R (q && c k))
      = σ R (q && p) * (∏ a, if ltB L k a then σ R (r && c a) else 1)
        * ((∏ a, if ltB L a k then σ R (q && c a) else 1) * σ R (q && c k)) by ring, h4]
  ring

/-! ## The Leibniz rule -/

section Leibniz

variable {q : Bool} (D : GrDer (GrOperadHom.id R C) q)

omit [Fintype A] in
lemma update_actY_der (L : LinOrd A) (f : S → A) (y : ∀ a, C (Fib f a)) (i : S) (z : C Y) (j : A)
    (hj : f i ≠ j) :
    update (actY (R := R) L f y i z false) j (D.toSpEnd.app _ (actY (R := R) L f y i z false j))
      = actY (R := R) L f (update y j (D.toSpEnd.app _ (y j))) i z false := by
  rw [actY_update]
  congr 1
  show D.app _ (actLin (R := R) L f i z false j (y j)) = actLin (R := R) L f i z false j _
  rw [actLin_ne _ _ _ _ _ _ hj, actLin_ne _ _ _ _ _ _ hj, Bool.false_and, GrOperad.tw_false,
    GrOperad.tw_false, D.app_map]
  rfl

omit [Fintype A] in
lemma der_actY_self (L : LinOrd A) (f : S → A) (y : ∀ a, C (Fib f a)) (i : S) (z : C Y)
    {c : Bool} (hy : GrOperad.par (R := R) c (y (f i)) = y (f i)) :
    D.app _ (actY (R := R) L f y i z false (f i))
      = actLin (R := R) L f i z false (f i) (D.app _ (y (f i)))
        + σ R (q && c) • actLin (R := R) L f i (D.app Y z) false (f i) (y (f i)) := by
  show D.app _ (actLin (R := R) L f i z false (f i) (y (f i))) = _
  rw [actLin_eq _ _ _ _ _ _ rfl, actLin_eq _ _ _ _ _ _ rfl, actLin_eq _ _ _ _ _ _ rfl, D.app_map,
    D.app_comp, GrOperadHom.id_app, GrOperadHom.id_app, GrOperad.tw_hom _ hy, map_smul,
    LinearMap.smul_apply, map_add, map_smul]

/-- **The Leibniz rule on a homogeneous generator**, for a homogeneous operation. -/
theorem leafMap_act_ownGen_hom (L : LinOrd A) (m : V A) (f : S → A) (y : ∀ a, C (Fib f a))
    {p : Bool} (hm : GrSpecies.par (R := R) p m = m) (c : A → Bool)
    (hy : ∀ a, GrOperad.par (R := R) (c a) (y a) = y a) (i : S) (z : C Y) {r : Bool}
    (hz : GrOperad.par (R := R) r z = z) :
    leafMap R V D.toSpEnd (act R V i z (mk R (ownGen L m f y)))
      = act R V i z (leafMap R V D.toSpEnd (mk R (ownGen L m f y)))
        + act R V i (D.app Y z) (GrSpecies.tw (R := R) q (mk R (ownGen L m f y))) := by
  have hz' : GrOperad.par (R := R) (xor r q) (D.app Y z) = D.app Y z := by
    rw [← D.app_par, hz]
  have hyj : ∀ j a, GrOperad.par (R := R) (update c j (xor (c j) q) a)
      (update y j (D.toSpEnd.app _ (y j)) a) = update y j (D.toSpEnd.app _ (y j)) a := by
    intro j a
    by_cases h : a = j
    · subst h
      rw [update_self, update_self]
      show GrOperad.par (R := R) _ (D.app _ (y a)) = D.app _ (y a)
      rw [← D.app_par, hy]
    · rw [update_of_ne h, update_of_ne h, hy]
  rw [act_ownGen_hom L m f y c hy i z hz, map_smul,
    leafMap_ownGen_hom D.toSpEnd L m (actOwner f i) (actY (R := R) L f y i z false) hm
      (update c (f i) (xor (c (f i)) r)) (actY_false_par L f y i z r hz c hy),
    leafMap_ownGen_hom D.toSpEnd L m f y hm c hy, map_sum,
    tw_mk_hom (V := V) q (ownGen L m f y) hm (c := c) hy, map_smul,
    act_ownGen_hom L m f y c hy i (D.app Y z) hz', Finset.smul_sum]
  have hR : ∀ j, act R V i z (mk R (ownGen L m f (update y j (D.toSpEnd.app _ (y j)))))
      = (∏ a, if ltB L (f i) a then σ R (r && update c j (xor (c j) q) a) else 1)
        • mk R (ownGen L m (actOwner f i)
          (actY (R := R) L f (update y j (D.toSpEnd.app _ (y j))) i z false)) :=
    fun j => act_ownGen_hom L m f _ _ (hyj j) i z hz
  simp only [map_smul, hR]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (f i)),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ (f i)), add_right_comm]
  congr 1
  · -- the inner operation receiving the inserted operation
    have key : mk R (ownGen L m (actOwner f i) (update (actY (R := R) L f y i z false) (f i)
        (actLin (R := R) L f i z false (f i) (D.app _ (y (f i)))
          + σ R (q && c (f i)) • actLin (R := R) L f i (D.app Y z) false (f i) (y (f i)))))
        = mk R (ownGen L m (actOwner f i) (actY (R := R) L f (update y (f i)
            (D.toSpEnd.app _ (y (f i)))) i z false))
          + σ R (q && c (f i)) • mk R (ownGen L m (actOwner f i)
            (actY (R := R) L f y i (D.app Y z) false)) := by
      rw [actY_update, actY_eq_update L f y i (D.app Y z) z false]
      exact (MultilinearMap.map_update_add (mkY (R := R) (ownGen L m (actOwner f i)
        (actY (R := R) L f y i z false))) _ _ _ _).trans (congrArg (fun t => _ + t)
          (MultilinearMap.map_update_smul (mkY (R := R) (ownGen L m (actOwner f i)
            (actY (R := R) L f y i z false))) _ _ _ _))
    rw [show D.toSpEnd.app _ (actY (R := R) L f y i z false (f i))
        = actLin (R := R) L f i z false (f i) (D.app _ (y (f i)))
          + σ R (q && c (f i)) • actLin (R := R) L f i (D.app Y z) false (f i) (y (f i)) from
        der_actY_self D L f y i z (hy (f i)), key]
    simp only [smul_add, smul_smul]
    rw [sign_leaf_act, sign_leaf_act_self]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : f i ≠ j := Ne.symm (Finset.ne_of_mem_erase hj)
    rw [update_actY_der D L f y i z j hj', smul_smul, smul_smul, sign_leaf_act]

/-- **The Leibniz rule**: `(1 ∘' D) (w ◁ᵢ z) = (1 ∘' D) w ◁ᵢ z + (-1)^{q |w|} w ◁ᵢ D z`. -/
theorem leafMap_act (i : S) (z : C Y) (w : GrComposite R V C S) :
    leafMap R V D.toSpEnd (act R V i z w)
      = act R V i z (leafMap R V D.toSpEnd w)
        + act R V i (D.app Y z) (GrSpecies.tw (R := R) q w) := by
  have key : ∀ r : Bool, ∀ z : C Y, GrOperad.par (R := R) r z = z →
      leafMap R V D.toSpEnd (act R V i z w)
        = act R V i z (leafMap R V D.toSpEnd w)
          + act R V i (D.app Y z) (GrSpecies.tw (R := R) q w) := by
    intro r z hz
    induction w using induction_on with
    | h0 => simp
    | hadd x y hx hy => simp only [map_add, hx, hy]; abel
    | hsmul c x hx => simp only [map_smul, hx, smul_add]
    | hmk g =>
      rw [mk_eq_sum (R := R) g]
      simp only [map_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun c _ => ?_
      rw [mk_eq_ownGen (R := R) (parGen (R := R) g p c)]
      refine leafMap_act_ownGen_hom D _ _ _ _ (p := p) ?_ c (fun a => ?_) i z hz
      · show GrSpecies.par (R := R) p (GrSpecies.par (R := R) p g.m) = _
        rw [GrSpecies.par_par, if_pos rfl]
      · show GrOperad.par (R := R) (c a) (GrOperad.map (R := R) _ (GrSpecies.par (R := R) (c a)
          (g.y a))) = _
        rw [← GrOperad.map_par]
        exact congrArg _ (GrOperad.par_par_self (R := R) (c a) (g.y a))
  have hadd : ∀ z z' : C Y, act R V i (z + z') = act R V i z + act R V i z' := fun z z' =>
    (actL R V i).map_add z z'
  rw [← GrOperad.par_add (R := R) z, map_add (D.app Y), hadd, hadd]
  simp only [LinearMap.add_apply, map_add]
  rw [key false _ (GrOperad.par_par_self (R := R) false z),
    key true _ (GrOperad.par_par_self (R := R) true z)]
  abel

end Leibniz

end GrComposite

end Operad
