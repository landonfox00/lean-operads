/-
# The corner of a graded endomorphism operad and the homotopy transfer theorem

Let `V` and `H` be dg super modules with even chain maps `i : H → V` and `p : V → H`, `p ∘ i = 1`
(`DGRetract`), and `e = i ∘ p` (`EndGr.eE`). **Conjugation** `F ↦ p ∘ F ∘ (i, …, i)` sends the
graded endomorphism operad of `V` to that of `H` (`EndGr.conjE`). It commutes with the parity
projections, the relabellings and the differentials (`EndGr.conjE_d`), and with the compositions
`F ∘ⱼ G` when `e ∘ G = G` (`EndGr.conjE_comp_of_lcomp`). On the operations `F` with `e ∘ F = F` and
`F ∘ₐ e = F` at every input it is inverse to `G ↦ i ∘ G ∘ (p, …, p)` (`EndGr.conjE_cconjE`,
`EndGr.cconjE_conjE`).

* **A twisting morphism `C → End_V` with values the operations `F` with `e ∘ F = F` conjugates to
  a twisting morphism `C → End_H`** (`EndGr.conjTw`): conjugation commutes with the convolution
  product when the second factor has such values (`EndGr.conjInv_star`).
* A contraction `(i, p, h)` with `d h + h d = i p - 1` is a retract datum `(e, h)` in `End_V`
  (`EndGr.retractE`).
* The operations with at least one input form a dg suboperad `End_V⁺` (`EndGr.posE`), an ideal
  of itself without operations without inputs (`EndGr.topI`), to which `Bar.exists_transfer`
  applies. (In `End_V` itself an ideal without operations without inputs is zero, the constants
  composing into every operation.)
* **The homotopy transfer theorem** (`EndGr.exists_transfer_End`): a twisting morphism
  `C → End_V` vanishing on the cooperations without inputs gives a twisting morphism
  `C → End_H`, `p ∘ v (f x) ∘ (i, …, i)` for the van der Laan map `v` of `End_V⁺`.
-/
import Operad.VanDerLaanTransfer
import Operad.GrSuboperad

universe u v w

namespace Operad

open Sym GerBV GrEnd

/-! ## Conjugating multilinear maps -/

section ConjML

variable {R : Type u} [CommRing R] {V H : Type v} [AddCommGroup V] [Module R V] [SuperMod R V]
  [AddCommGroup H] [Module R H] [SuperMod R H]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **An even linear map** between super modules: it commutes with the parity projections. -/
def IsEvenLin (f : V →ₗ[R] H) : Prop :=
  ∀ (b : Bool) (x : V), f (SuperMod.pr (R := R) b x) = SuperMod.pr (R := R) b (f x)

variable (i : H →ₗ[R] V) (p : V →ₗ[R] H)

namespace GrEnd

/-- **Conjugating a multilinear map**: `f ↦ p ∘ f ∘ (i, …, i)`. -/
def conjML (A : Type) [Fintype A] [DecidableEq A] : EndOp R V A →ₗ[R] EndOp R H A where
  toFun f := p.compMultilinearMap (f.compLinearMap fun _ => i)
  map_add' _ _ := MultilinearMap.ext fun _ => p.map_add _ _
  map_smul' _ _ := MultilinearMap.ext fun _ => p.map_smul _ _

omit [SuperMod R V] [SuperMod R H] in
lemma conjML_apply (f : EndOp R V A) (x : A → H) :
    conjML i p A f x = p (f fun a => i (x a)) := rfl

variable {i p}

lemma conjML_inp (hi : IsEvenLin i) (c : A → Bool) (f : EndOp R V A) :
    conjML i p A (inp R V c f) = inp R H c (conjML i p A f) :=
  MultilinearMap.ext fun x => by
    rw [conjML_apply, inp_apply, inp_apply, conjML_apply]
    exact congrArg p (congrArg f (funext fun a => (hi (c a) (x a)).symm))

lemma conjML_out (hp : IsEvenLin p) (b : Bool) (f : EndOp R V A) :
    conjML i p A (out R V b f) = out R H b (conjML i p A f) :=
  MultilinearMap.ext fun x => by
    rw [conjML_apply, out_apply, out_apply, conjML_apply]
    exact hp b _

lemma conjML_twist (hi : IsEvenLin i) (φ : (A → Bool) → R) (f : EndOp R V A) :
    conjML i p A (twist R V φ f) = twist R H φ (conjML i p A f) := by
  simp only [twist, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, map_sum,
    map_smul, conjML_inp hi]

lemma conjML_parML (hi : IsEvenLin i) (hp : IsEvenLin p) (b : Bool) (f : EndOp R V A) :
    conjML i p A (parML R V b f) = parML R H b (conjML i p A f) := by
  simp only [parML, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, map_sum,
    conjML_inp hi, conjML_out hp]

omit [SuperMod R V] [SuperMod R H] in
lemma conjML_mapL {A' : Type} [Fintype A'] [DecidableEq A'] (e : A ≃ A') (f : EndOp R V A) :
    conjML i p A' (EndOp.mapL R V e f) = EndOp.mapL R H e (conjML i p A f) :=
  MultilinearMap.ext fun _ => rfl

omit [SuperMod R V] [SuperMod R H] [Fintype A] [Fintype B] [DecidableEq B] in
lemma i_feed (j : A) (x : Without A j ⊕ B → H) (w : H) :
    (fun a => i (feed j x w a)) = feed j (fun z => i (x z)) (i w) := by
  funext a
  by_cases h : a = j
  · subst h
    simp
  · rw [feed_of_ne h, feed_of_ne h]

omit [SuperMod R V] [SuperMod R H] in
/-- **Conjugation commutes with composition when `i ∘ p ∘ g = g`.** -/
lemma compL_conjML (j : A) (f : EndOp R V A) {g : EndOp R V B}
    (hg : ∀ y, i (p (g y)) = g y) :
    EndOp.compL R H j (conjML i p A f) (conjML i p B g)
      = conjML i p _ (EndOp.compL R V j f g) :=
  MultilinearMap.ext fun x => by
    simp only [EndOp.compL, LinearMap.mk₂_apply, EndOp.compML_apply, conjML_apply, i_feed, hg]

/-- **`i ∘ p` fixes the homogeneous components** of a multilinear map that it fixes. -/
lemma ip_parML (hi : IsEvenLin i) (hp : IsEvenLin p) {g : EndOp R V B}
    (hg : ∀ y, i (p (g y)) = g y) (q : Bool) (y : B → V) :
    i (p (parML R V q g y)) = parML R V q g y := by
  simp only [parML, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
    MultilinearMap.sum_apply, out_apply, inp_apply, map_sum, hp _, hi _, hg]

/-- **Conjugation commutes with the Koszul composite** when it does with the composites of the
homogeneous components. -/
lemma conjML_kcomp_of (hi : IsEvenLin i) (hp : IsEvenLin p) (L : LinOrd A) (j : A)
    (f : EndOp R V A) (g : EndOp R V B)
    (h : ∀ (q : Bool) (f' : EndOp R V A), EndOp.compL R H j (conjML i p A f')
      (conjML i p B (parML R V q g)) = conjML i p _ (EndOp.compL R V j f' (parML R V q g))) :
    conjML i p _ (kcomp R V L j f g) = kcomp R H L j (conjML i p A f) (conjML i p B g) := by
  rw [kcomp_apply, kcomp_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← h, conjML_twist hi, conjML_parML hi hp]

end GrEnd

end ConjML

/-! ## Retracts of dg super modules -/

section Retract

variable (R : Type u) [CommRing R] (V H : Type v) [AddCommGroup V] [Module R V] [SuperMod R V]
  [AddCommGroup H] [Module R H] [SuperMod R H] [DGSuperMod R V] [DGSuperMod R H]

/-- **A retract of dg super modules**: even chain maps `i : H → V` and `p : V → H` with
`p ∘ i = 1`. -/
structure DGRetract where
  /-- The inclusion. -/
  i : H →ₗ[R] V
  /-- The projection. -/
  p : V →ₗ[R] H
  i_even : IsEvenLin i
  p_even : IsEvenLin p
  d_i : ∀ x, DGSuperMod.d (R := R) (i x) = i (DGSuperMod.d (R := R) x)
  d_p : ∀ x, DGSuperMod.d (R := R) (p x) = p (DGSuperMod.d (R := R) x)
  p_i : ∀ x, p (i x) = x

end Retract

namespace EndGr

variable {R : Type u} [CommRing R] {V H : Type v} [AddCommGroup V] [Module R V] [SuperMod R V]
  [AddCommGroup H] [Module R H] [SuperMod R H] [DGSuperMod R V] [DGSuperMod R H]
  (r : DGRetract R V H)
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-! ## Conjugation -/

/-- **Conjugation** `F ↦ p ∘ F ∘ (i, …, i)`, order by order. -/
noncomputable def conjE (A : Type) [Fintype A] [DecidableEq A] :
    EndGr R V A →ₗ[R] EndGr R H A where
  toFun F := mk (fun L => conjML r.i r.p A (F.fam L)) fun L L' => by
    dsimp only
    rw [fam_compat F L L', conjML_twist r.i_even]
  map_add' F G := ext (dord A) (map_add (conjML r.i r.p A) (F.fam _) (G.fam _))
  map_smul' c F := ext (dord A) (map_smul (conjML r.i r.p A) c (F.fam _))

@[simp] lemma conjE_fam (F : EndGr R V A) (L : LinOrd A) :
    (conjE r A F).fam L = conjML r.i r.p A (F.fam L) := rfl

lemma conjE_par (b : Bool) (F : EndGr R V A) :
    conjE r A (GrOperad.par (R := R) b F) = GrOperad.par (R := R) b (conjE r A F) :=
  ext (dord A) (conjML_parML r.i_even r.p_even b _)

lemma conjE_map (e : A ≃ B) (F : EndGr R V A) :
    conjE r B (GrOperad.map (R := R) e F) = GrOperad.map (R := R) e (conjE r A F) :=
  ext (dord B) (conjML_mapL e _)

lemma conjE_tw (b : Bool) (F : EndGr R V A) :
    conjE r A (GrOperad.tw (R := R) b F) = GrOperad.tw (R := R) b (conjE r A F) := by
  rw [GrOperad.tw_apply, GrOperad.tw_apply, map_add, map_smul]
  exact congrArg₂ (· + σ R b • ·) (conjE_par r false F) (conjE_par r true F)

lemma dE_fam (L : LinOrd Unit) : (dE R V).fam L = dML R V := by
  rw [LinOrd.eq_of_subsingleton L LinOrd.one]
  exact ofFam_fam _ _

lemma bsg_unit (L : LinOrd Unit) (q : Bool) (c : Unit → Bool) : bsg R L () q c = 1 := by
  rw [LinOrd.eq_of_subsingleton L LinOrd.one]
  exact bsg_one q c

/-- **Conjugation commutes with composites `F ∘ⱼ G` with `i ∘ p ∘ G = G`.** -/
lemma conjE_comp (j : A) (F : EndGr R V A) {G : EndGr R V B}
    (hG : ∀ (M : LinOrd B) y, r.i (r.p (G.fam M y)) = G.fam M y) :
    conjE r _ (GrOperad.comp (R := R) j F G)
      = GrOperad.comp (R := R) j (conjE r A F) (conjE r B G) :=
  ext (LinOrd.comp j (dord A) (dord B)) (by
    show conjML r.i r.p _ ((compE j F G).fam _) = (compE j (conjE r A F) (conjE r B G)).fam _
    rw [compE_fam, compE_fam, compFam_comp, compFam_comp, conjE_fam, conjE_fam]
    exact conjML_kcomp_of r.i_even r.p_even _ j _ _ fun q f' =>
      compL_conjML j f' (ip_parML r.i_even r.p_even (hG (dord B)) q))

lemma compL_dML_left (g : EndOp R V B) :
    EndOp.compL R H () (dML R H) (conjML r.i r.p B g)
      = conjML r.i r.p _ (EndOp.compL R V () (dML R V) g) :=
  MultilinearMap.ext fun x => by
    simp only [EndOp.compL, LinearMap.mk₂_apply, EndOp.compML_apply, conjML_apply, dML_apply,
      feed_self]
    exact r.d_p _

lemma compL_dML_right (a : A) (f : EndOp R V A) :
    EndOp.compL R H a (conjML r.i r.p A f) (dML R H)
      = conjML r.i r.p _ (EndOp.compL R V a f (dML R V)) :=
  MultilinearMap.ext fun x => by
    simp only [EndOp.compL, LinearMap.mk₂_apply, EndOp.compML_apply, conjML_apply, dML_apply,
      i_feed, r.d_i]

lemma parML_false_dML : parML R V false (dML R V) = 0 := by
  rw [← parML_dML, parML_parML, if_neg (by decide)]

lemma conjE_comp_dE_left (G : EndGr R V B) :
    conjE r _ (GrOperad.comp (R := R) () (dE R V) G)
      = GrOperad.comp (R := R) () (dE R H) (conjE r B G) :=
  ext (LinOrd.comp () LinOrd.one (dord B)) (by
    show conjML r.i r.p _ ((compE () (dE R V) G).fam _)
      = (compE () (dE R H) (conjE r B G)).fam _
    rw [compE_fam, compE_fam, compFam_comp, compFam_comp, conjE_fam, dE_fam, dE_fam,
      kcomp_apply, kcomp_apply, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [twist_congr (fun c => bsg_unit _ q c), twist_one, twist_congr (fun c => bsg_unit _ q c),
      twist_one, ← conjML_parML r.i_even r.p_even, compL_dML_left])

lemma conjE_comp_dE_right (a : A) (F : EndGr R V A) :
    conjE r _ (GrOperad.comp (R := R) a F (dE R V))
      = GrOperad.comp (R := R) a (conjE r A F) (dE R H) :=
  ext (LinOrd.comp a (dord A) LinOrd.one) (by
    show conjML r.i r.p _ ((compE a F (dE R V)).fam _)
      = (compE a (conjE r A F) (dE R H)).fam _
    rw [compE_fam, compE_fam, compFam_comp, compFam_comp, conjE_fam, dE_fam, dE_fam,
      kcomp_apply, kcomp_apply, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    cases q
    · rw [parML_false_dML, parML_false_dML, map_zero, map_zero, map_zero]
    · rw [parML_dML, parML_dML, ← conjML_twist r.i_even, compL_dML_right])

/-- **Conjugation commutes with the differentials.** -/
theorem conjE_d (F : EndGr R V A) :
    conjE r A (DGOperad.d (R := R) F) = DGOperad.d (R := R) (conjE r A F) := by
  rw [d_eq, d_eq, GrOperad.innerL_apply, GrOperad.innerL_apply, map_sub, map_sum]
  congr 1
  · rw [GrOperad.lcomp_apply, GrOperad.lcomp_apply, conjE_map, conjE_comp_dE_left]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [GrOperad.rcomp_apply, GrOperad.rcomp_apply, conjE_map, conjE_comp_dE_right, conjE_tw]

/-! ## The corner -/

/-- **The idempotent `e = i ∘ p`**, an operation with one input. -/
noncomputable def eE : EndGr R V Unit :=
  ofFam LinOrd.one (MultilinearMap.ofSubsingleton R V V () (r.i ∘ₗ r.p))

lemma eE_fam_apply (y : Unit → V) : (eE r).fam LinOrd.one y = r.i (r.p (y ())) := by
  rw [eE, ofFam_fam]
  rfl

omit [DGSuperMod R V] in
lemma sum_parML (g : EndOp R V B) : ∑ q, parML R V q g = g := by
  rw [Fintype.sum_bool, add_comm, parML_add]

omit [DGSuperMod R V] in
lemma bsg_one' (q : Bool) : bsg R LinOrd.one () q = fun _ => (1 : R) :=
  funext fun c => bsg_one q c

omit [DGSuperMod R V] in
/-- **Composing after an operation with one input**, order by order. -/
lemma lcomp_fam_apply (D : EndGr R V Unit) (G : EndGr R V B) (M : LinOrd B) (y : B → V) :
    (GrOperad.lcomp R D G).fam M y = D.fam LinOrd.one (fun _ => G.fam M y) := by
  rw [GrOperad.lcomp_apply]
  show (mapE (leftUnitEquiv B) (compE () D G)).fam M y = _
  have hM : LinOrd.map (leftUnitEquiv B).symm M = LinOrd.comp () LinOrd.one M := by
    have h := congrArg (LinOrd.map (leftUnitEquiv B).symm) (lo_one_comp M)
    rw [lo_map_symm_map] at h
    exact h.symm
  rw [mapE_fam, compE_fam, hM, compFam_comp, kcomp_apply]
  simp only [bsg_one', twist_one]
  rw [← map_sum, sum_parML]
  rfl

omit [DGSuperMod R V] in
lemma sub_fam' (F G : EndGr R V A) (L : LinOrd A) : (F - G).fam L = F.fam L - G.fam L := rfl

omit [DGSuperMod R V] in
/-- **Composing before an operation with one input, for one input.** -/
lemma rcomp_fam_apply (D X : EndGr R V Unit) (u : Unit) (y : Unit → V) :
    (GrOperad.rcomp R D u X).fam LinOrd.one y
      = X.fam LinOrd.one (fun _ => D.fam LinOrd.one (fun _ => y ())) := by
  cases u
  rw [GrOperad.rcomp_apply]
  show (mapE (rightUnitEquiv ()) (compE () X D)).fam LinOrd.one y = _
  haveI : Subsingleton (Without Unit () ⊕ Unit) := ⟨fun a b => by
    rcases a with ⟨u, hu⟩ | a
    · exact absurd (Subsingleton.elim u ()) hu
    rcases b with ⟨v, hv⟩ | b
    · exact absurd (Subsingleton.elim v ()) hv
    rfl⟩
  have hM : LinOrd.map (rightUnitEquiv ()).symm LinOrd.one
      = LinOrd.comp () LinOrd.one LinOrd.one :=
    LinOrd.eq_of_subsingleton _ _
  rw [mapE_fam, compE_fam, hM, compFam_comp, kcomp_apply]
  simp only [bsg_one', twist_one]
  rw [← map_sum, sum_parML]
  rfl

/-- **The corner condition** `e ∘ G = G`, order by order. -/
lemma ip_of_lcomp {G : EndGr R V B} (hG : GrOperad.lcomp R (eE r) G = G) (M : LinOrd B)
    (y : B → V) : r.i (r.p (G.fam M y)) = G.fam M y := by
  have h := congrArg (fun X : EndGr R V B => X.fam M y) hG
  simp only [lcomp_fam_apply] at h
  rw [eE_fam_apply] at h
  exact h

/-- **Conjugation commutes with composites `F ∘ⱼ G` with `e ∘ G = G`.** -/
theorem conjE_comp_of_lcomp (j : A) (F : EndGr R V A) {G : EndGr R V B}
    (hG : GrOperad.lcomp R (eE r) G = G) :
    conjE r _ (GrOperad.comp (R := R) j F G)
      = GrOperad.comp (R := R) j (conjE r A F) (conjE r B G) :=
  conjE_comp r j F (ip_of_lcomp r hG)

/-! ## The inverse on the corner -/

/-- **The inverse conjugation** `G ↦ i ∘ G ∘ (p, …, p)`, order by order. -/
noncomputable def cconjE (A : Type) [Fintype A] [DecidableEq A] :
    EndGr R H A →ₗ[R] EndGr R V A where
  toFun G := mk (fun L => conjML r.p r.i A (G.fam L)) fun L L' => by
    dsimp only
    rw [fam_compat G L L', conjML_twist r.p_even]
  map_add' F G := ext (dord A) (map_add (conjML r.p r.i A) (F.fam _) (G.fam _))
  map_smul' c F := ext (dord A) (map_smul (conjML r.p r.i A) c (F.fam _))

/-- **Conjugation after the inverse conjugation is the identity**, by `p ∘ i = 1`. -/
theorem conjE_cconjE (G : EndGr R H A) : conjE r A (cconjE r A G) = G :=
  ext (dord A) (MultilinearMap.ext fun x => by
    show r.p (r.i (G.fam (dord A) fun a => r.p (r.i (x a)))) = G.fam (dord A) x
    simp only [r.p_i])

/-- **The inverse conjugation after conjugation is the identity on the corner**: on the
operations `F` with `e ∘ F = F` and `F ∘ₐ e = F` at every input, order by order. -/
theorem cconjE_conjE {F : EndGr R V A}
    (hl : ∀ (L : LinOrd A) (y : A → V), r.i (r.p (F.fam L y)) = F.fam L y)
    (hr : ∀ (L : LinOrd A) (y : A → V), F.fam L (fun a => r.i (r.p (y a))) = F.fam L y) :
    cconjE r A (conjE r A F) = F :=
  ext (dord A) (MultilinearMap.ext fun x => by
    show r.i (r.p (F.fam (dord A) fun a => r.i (r.p (x a)))) = F.fam (dord A) x
    rw [hl, hr])

/-! ## Conjugating twisting morphisms -/

section Conv

variable {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [DGCooperad R C]
  [GrCooperad.Coaug R C]

/-- **Conjugating an invariant family of the convolution operad.** -/
noncomputable def conjInv (α : GrOperad.Inv R (ConvOp R C (EndGr R V))) :
    GrOperad.Inv R (ConvOp R C (EndGr R H)) :=
  ⟨fun A _ _ => ConvOp.of (conjE r A ∘ₗ ConvOp.toLin (α.1 A)), fun A B _ _ _ _ e => by
    show ConvOp.mapC e (ConvOp.of (conjE r A ∘ₗ ConvOp.toLin (α.1 A)))
      = ConvOp.of (conjE r B ∘ₗ ConvOp.toLin (α.1 B))
    ext x
    rw [ConvOp.mapC_apply]
    show GrOperad.map (R := R) e (conjE r A (ConvOp.toLin (α.1 A)
        (SymSpecies.map (R := R) e.symm x))) = conjE r B (ConvOp.toLin (α.1 B) x)
    rw [← conjE_map]
    exact congrArg (conjE r B) (congrArg (fun f => ConvOp.toLin f x) (α.2 A B e))⟩

omit [GrCooperad.Coaug R C] in
lemma conjInv_apply (α : GrOperad.Inv R (ConvOp R C (EndGr R V))) (x : C A) :
    ConvOp.toLin ((conjInv r α).1 A) x = conjE r A (ConvOp.toLin (α.1 A) x) := rfl

omit [GrCooperad.Coaug R C] in
lemma isParC_conjInv {α : GrOperad.Inv R (ConvOp R C (EndGr R V))}
    (hα : ConvOp.IsParC true (α.1 A)) : ConvOp.IsParC true ((conjInv r α).1 A) := by
  intro c x
  rw [conjInv_apply, conjInv_apply, hα c x, conjE_par]

omit [GrCooperad.Coaug R C] in
/-- **Conjugation commutes with the convolution product** when the second factor is odd with
values `G` with `e ∘ G = G`. -/
lemma conjInv_star (α β : GrOperad.Inv R (ConvOp R C (EndGr R V)))
    (hβ : ∀ (B : Type) [Fintype B] [DecidableEq B], ConvOp.IsParC true (β.1 B))
    (hc : ∀ (B : Type) [Fintype B] [DecidableEq B] (y : C B),
      GrOperad.lcomp R (eE r) (ConvOp.toLin (β.1 B) y) = ConvOp.toLin (β.1 B) y)
    (X : Type) [Fintype X] [DecidableEq X] (x : C X) :
    ConvOp.toLin ((GrOperad.Inv.star R _ (conjInv r α) (conjInv r β)).1 X) x
      = conjE r X (ConvOp.toLin ((GrOperad.Inv.star R _ α β).1 X) x) := by
  rw [GrOperad.Inv.star_apply, GrOperad.Inv.star_apply, ConvOp.toLin_sum, ConvOp.toLin_sum,
    LinearMap.coe_sum, LinearMap.coe_sum, Finset.sum_apply, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  show ConvOp.toLin (ConvOp.mapC (splitEquiv S)
      (ConvOp.compC none ((conjInv r α).1 (SOut S)) ((conjInv r β).1 (SIn S)))) x
    = conjE r X (ConvOp.toLin (ConvOp.mapC (splitEquiv S)
      (ConvOp.compC none (α.1 (SOut S)) (β.1 (SIn S)))) x)
  rw [ConvOp.mapC_apply, ConvOp.mapC_apply, conjE_map]
  congr 1
  generalize SymSpecies.map (R := R) (splitEquiv S).symm x = z
  show ConvOp.mu none (ConvOp.kap ((conjInv r α).1 (SOut S)) ((conjInv r β).1 (SIn S))
      (GrCooperad.decomp (R := R) none z))
    = conjE r _ (ConvOp.mu none (ConvOp.kap (α.1 (SOut S)) (β.1 (SIn S))
      (GrCooperad.decomp (R := R) none z)))
  rw [ConvOp.kap_hom _ (isParC_conjInv r (hβ (SIn S))), ConvOp.kap_hom _ (hβ (SIn S))]
  induction GrCooperad.decomp (R := R) none z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [TensorProduct.map_tmul, ConvOp.mu_tmul, LinearMap.comp_apply, conjInv_apply]
    rw [conjE_comp_of_lcomp r _ _ (hc _ b)]
  | add u u' hu hu' => simp only [map_add, hu, hu']

/-- **Conjugating a twisting morphism with values in the corner**: a twisting morphism
`α : C → End_V` with values the operations `F` with `e ∘ F = F` gives the twisting morphism
`p ∘ α ∘ (i, …, i) : C → End_H`. -/
noncomputable def conjTw (α : TwistingDG R C (EndGr R V))
    (hα : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      GrOperad.lcomp R (eE r) (ConvOp.toLin (α.1.1 A) x) = ConvOp.toLin (α.1.1 A) x) :
    TwistingDG R C (EndGr R H) :=
  have hodd : ∀ (B : Type) [Fintype B] [DecidableEq B], ConvOp.IsParC true (α.1.1 B) :=
    fun B _ _ => ConvOp.parC_eq_self_iff.1 (α.2.1 B)
  TwistingDG.ofApply (conjInv r α.1)
    (fun A _ _ => ConvOp.parC_eq_self_iff.2 (isParC_conjInv r (hodd A)))
    (fun A _ _ x hx => by rw [conjInv_apply, α.2.2.1 A x hx, map_zero])
    (fun A _ _ x => by
      rw [conjInv_apply, conjInv_apply, conjInv_star r α.1 α.1 hodd hα, ← conjE_d, ← map_add,
        ← map_add, Bar.mc_apply α x, map_zero])

lemma conjTw_apply (α : TwistingDG R C (EndGr R V)) (hα) (x : C A) :
    ConvOp.toLin ((conjTw r α hα).1.1 A) x = conjE r A (ConvOp.toLin (α.1.1 A) x) := rfl

end Conv

/-! ## The retract datum of a contraction -/

section Contraction

/-- A linear map, as an operation with one input. -/
noncomputable def unE (g : V →ₗ[R] V) : EndGr R V Unit :=
  ofFam LinOrd.one (MultilinearMap.ofSubsingleton R V V () g)

omit [DGSuperMod R V] in
lemma unE_fam_apply (g : V →ₗ[R] V) (y : Unit → V) : (unE g).fam LinOrd.one y = g (y ()) := by
  rw [unE, ofFam_fam]
  rfl

omit [DGSuperMod R V] in
/-- **A linear map shifting the parities by `b`** is an operation of parity `b`. -/
lemma par_unE (g : V →ₗ[R] V) (b : Bool)
    (hg : ∀ (c : Bool) (x : V),
      g (SuperMod.pr (R := R) c x) = SuperMod.pr (R := R) (xor c b) (g x)) :
    GrOperad.par (R := R) b (unE g) = unE g := by
  show parE b (unE g) = unE g
  rw [unE, parE_ofFam]
  congr 1
  refine ext_inp fun c => ?_
  have hc : tot c = c () := by
    unfold tot
    rw [Fintype.sum_unique, bodd_toNat]
  rw [inp_parML, hc]
  refine MultilinearMap.ext fun x => ?_
  rw [out_apply, inp_apply]
  show SuperMod.pr (R := R) (xor b (c ())) (g (SuperMod.pr (R := R) (c ()) (x ())))
    = g (SuperMod.pr (R := R) (c ()) (x ()))
  rw [hg, Bool.xor_comm, pr_self]

lemma eE_eq : eE r = unE (r.i ∘ₗ r.p) := rfl

lemma dE_fam_apply (y : Unit → V) :
    (dE R V).fam LinOrd.one y = DGSuperMod.d (R := R) (y ()) := by
  rw [dE_fam, dML_apply]

/-- **The differential of an operation with one input**: `∂g = d ∘ g - (-1)^{|g|} g ∘ d`. -/
lemma d_unE_fam_apply (g : V →ₗ[R] V) (b : Bool)
    (hg : GrOperad.par (R := R) b (unE g) = unE g) (y : Unit → V) :
    (DGOperad.d (R := R) (unE g)).fam LinOrd.one y
      = DGSuperMod.d (R := R) (g (y ())) - σ R b • g (DGSuperMod.d (R := R) (y ())) := by
  rw [d_eq, GrOperad.innerL_apply, Fintype.sum_unique, GrOperad.tw_hom true hg, map_smul,
    sub_fam', smul_fam, MultilinearMap.sub_apply, MultilinearMap.smul_apply, lcomp_fam_apply,
    rcomp_fam_apply, dE_fam_apply, unE_fam_apply, unE_fam_apply, dE_fam_apply, Bool.true_and]

variable (h : V →ₗ[R] V)
  (h_odd : ∀ (c : Bool) (x : V), h (SuperMod.pr (R := R) c x) = SuperMod.pr (R := R) (!c) (h x))
  (hdh : ∀ x, DGSuperMod.d (R := R) (h x) + h (DGSuperMod.d (R := R) x) = r.i (r.p x) - x)

/-- **The retract datum of a contraction** `(i, p, h)` with `d h + h d = i p - 1`, in the graded
endomorphism operad of `V`: `e = i ∘ p` and `h`. -/
noncomputable def retractE : OpRetract R (EndGr R V) where
  e := eE r
  h := unE h
  e_even := par_unE _ false fun c x => by
    rw [Bool.xor_false]
    show r.i (r.p (SuperMod.pr (R := R) c x)) = SuperMod.pr (R := R) c (r.i (r.p x))
    rw [r.p_even, r.i_even]
  h_odd := par_unE _ true fun c x => by rw [Bool.xor_true]; exact h_odd c x
  ee := ext LinOrd.one (MultilinearMap.ext fun y => by
    simp only [lcomp_fam_apply, eE_fam_apply, r.p_i])
  de := ext LinOrd.one (MultilinearMap.ext fun y => by
    have he : GrOperad.par (R := R) false (unE (r.i ∘ₗ r.p)) = unE (r.i ∘ₗ r.p) :=
      par_unE _ false fun c x => by
        rw [Bool.xor_false]
        show r.i (r.p (SuperMod.pr (R := R) c x)) = SuperMod.pr (R := R) c (r.i (r.p x))
        rw [r.p_even, r.i_even]
    rw [eE_eq, d_unE_fam_apply _ false he, zero_fam, MultilinearMap.zero_apply, σ_false,
      one_smul, LinearMap.comp_apply, LinearMap.comp_apply, r.d_i, r.d_p, sub_self])
  dh := ext LinOrd.one (MultilinearMap.ext fun y => by
    have hh : GrOperad.par (R := R) true (unE h) = unE h :=
      par_unE _ true fun c x => by rw [Bool.xor_true]; exact h_odd c x
    rw [d_unE_fam_apply _ true hh, sub_fam', MultilinearMap.sub_apply, eE_fam_apply,
      σ_true, neg_one_smul, sub_neg_eq_add, hdh]
    rfl)

end Contraction

/-! ## Positive arity -/

section Pos

variable (R V)

/-- **The operations with at least one input** of the graded endomorphism operad. -/
def posE : GrSuboperad R (EndGr R V) where
  sub A _ _ :=
    { carrier := {x | Nonempty A ∨ x = 0}
      add_mem' := fun {a b} ha hb => by
        by_cases hA : Nonempty A
        · exact Or.inl hA
        · rw [ha.resolve_left hA, hb.resolve_left hA, add_zero]
          exact Or.inr rfl
      zero_mem' := Or.inr rfl
      smul_mem' := fun c x hx => hx.imp id fun h => by rw [h, smul_zero] }
  par_mem b x hx := hx.imp id fun h => by rw [h, map_zero]
  map_mem e x hx := hx.imp (fun ⟨a⟩ => ⟨e a⟩) fun h => by rw [h, map_zero]
  one_mem := Or.inl ⟨()⟩
  comp_mem i x y hx hy := by
    rcases hy with hB | rfl
    · obtain ⟨b⟩ := hB
      exact Or.inl ⟨Sum.inr b⟩
    · exact Or.inr (by rw [map_zero])

variable {R V}

lemma posE_d {A : Type} [Fintype A] [DecidableEq A] {x : EndGr R V A}
    (hx : x ∈ (posE R V).sub A) : DGOperad.d (R := R) x ∈ (posE R V).sub A :=
  hx.imp id fun h => by rw [h, map_zero]

variable (R V) in
/-- **The operations with at least one input form a dg operad.** -/
noncomputable instance instDGPos : DGOperad R (posE R V).Op :=
  { (inferInstance : GrOperad R (posE R V).Op) with
    d := fun {A} _ _ => (DGOperad.d (R := R) (P := EndGr R V) (A := A)).restrict
      fun _ hx => posE_d hx
    d_d := fun x => Subtype.ext (DGOperad.d_d (R := R) x.1)
    d_par := fun b x => Subtype.ext (DGOperad.d_par (R := R) b x.1)
    map_d := fun e x => Subtype.ext (DGOperad.map_d (R := R) e x.1)
    d_one := Subtype.ext (DGOperad.d_one (R := R) (P := EndGr R V))
    d_comp := fun i x y => Subtype.ext (DGOperad.d_comp (R := R) i x.1 y.1) }

variable (R V) in
/-- **All operations with at least one input**, as an ideal. -/
def topI : GrOperadIdeal R (posE R V).Op where
  sub _ _ _ := ⊤
  par_mem _ _ _ := Submodule.mem_top
  map_mem _ _ _ := Submodule.mem_top
  comp_mem_left _ _ _ _ := Submodule.mem_top
  comp_mem_right _ _ _ _ := Submodule.mem_top

lemma topI_d {A : Type} [Fintype A] [DecidableEq A] {x : (posE R V).Op A}
    (_ : x ∈ (topI R V).sub A) : DGOperad.d (R := R) x ∈ (topI R V).sub A :=
  Submodule.mem_top

omit [DGSuperMod R V] in
lemma topI_zero : ∀ x ∈ (topI R V).sub (Fin 0), x = 0 := fun x _ =>
  Subtype.ext (x.2.resolve_left fun ⟨a⟩ => Fin.elim0 a)

/-- **The retract datum of a contraction**, in the operations with at least one input. -/
noncomputable def retractPos (h : V →ₗ[R] V)
    (h_odd : ∀ (c : Bool) (x : V),
      h (SuperMod.pr (R := R) c x) = SuperMod.pr (R := R) (!c) (h x))
    (hdh : ∀ x, DGSuperMod.d (R := R) (h x) + h (DGSuperMod.d (R := R) x) = r.i (r.p x) - x) :
    OpRetract R (posE R V).Op where
  e := ⟨eE r, Or.inl ⟨()⟩⟩
  h := ⟨unE h, Or.inl ⟨()⟩⟩
  e_even := Subtype.ext (retractE r h h_odd hdh).e_even
  h_odd := Subtype.ext (retractE r h h_odd hdh).h_odd
  ee := Subtype.ext (retractE r h h_odd hdh).ee
  de := Subtype.ext (retractE r h h_odd hdh).de
  dh := Subtype.ext (retractE r h h_odd hdh).dh

end Pos

/-! ## The homotopy transfer theorem -/

section Transfer

variable {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [DGCooperad R C]
  [GrCooperad.Coaug R C]

/-- **A twisting morphism vanishing on the cooperations without inputs**, with values in the
operations with at least one input. -/
noncomputable def liftPos (α : TwistingDG R C (EndGr R V))
    (hα0 : ∀ (A : Type) [Fintype A] [DecidableEq A] [IsEmpty A] (x : C A),
      ConvOp.toLin (α.1.1 A) x = 0) : TwistingDG R C (posE R V).Op :=
  have hpos : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      ConvOp.toLin (α.1.1 A) x ∈ (posE R V).sub A := fun A _ _ x => by
    by_cases hA : Nonempty A
    · exact Or.inl hA
    · haveI : IsEmpty A := not_nonempty_iff.1 hA
      exact Or.inr (hα0 A x)
  let αP : GrOperad.Inv R (ConvOp R C (posE R V).Op) :=
    ⟨fun A _ _ => ConvOp.of ((ConvOp.toLin (α.1.1 A)).codRestrict _ (hpos A)),
      fun A B _ _ _ _ e => by
        show ConvOp.mapC e (ConvOp.of _) = ConvOp.of _
        ext x
        exact congrArg (fun f => ConvOp.toLin f x) (α.1.2 A B e)⟩
  have hinc : GrOperad.Inv.appHom (ConvOp.postHom (C := C) (posE R V).incl) αP = α.1 :=
    Subtype.ext (funext fun A => funext fun _ => funext fun _ => by
      rw [GrOperad.Inv.appHom_apply]
      ext x
      rfl)
  TwistingDG.ofApply αP
    (fun A _ _ => ConvOp.parC_eq_self_iff.2 fun c x => Subtype.ext
      (ConvOp.parC_eq_self_iff.1 (α.2.1 A) c x))
    (fun A _ _ x hx => Subtype.ext (α.2.2.1 A x hx))
    (fun A _ _ x => Subtype.ext (by
      have hs := congrArg (fun q : GrOperad.Inv R (ConvOp R C (EndGr R V)) =>
        ConvOp.toLin (q.1 A) x) (GrOperad.Inv.appHom_star (ConvOp.postHom (C := C)
          (posE R V).incl) αP αP)
      simp only [hinc] at hs
      show DGOperad.d (R := R) (ConvOp.toLin (α.1.1 A) x)
          + ConvOp.toLin (α.1.1 A) (DGCooperad.d (R := R) x)
          + ((posE R V).incl.app A
            (ConvOp.toLin ((GrOperad.Inv.star R _ αP αP).1 A) x)) = 0
      have hs' : (posE R V).incl.app A (ConvOp.toLin ((GrOperad.Inv.star R _ αP αP).1 A) x)
          = ConvOp.toLin ((GrOperad.Inv.star R _ α.1 α.1).1 A) x := hs
      rw [hs']
      exact Bar.mc_apply α x))

/-- **The inclusion of the operations with at least one input**, on twisting morphisms. -/
noncomputable def incTw (α : TwistingDG R C (posE R V).Op) : TwistingDG R C (EndGr R V) :=
  TwistingDG.ofApply (GrOperad.Inv.appHom (ConvOp.postHom (C := C) (posE R V).incl) α.1)
    (fun A _ _ => by
      rw [GrOperad.Inv.appHom_apply, ← (ConvOp.postHom (C := C) (posE R V).incl).app_par,
        α.2.1 A])
    (fun A _ _ x hx => by
      show ((ConvOp.toLin (α.1.1 A) x : (posE R V).Op A) : EndGr R V A) = 0
      rw [α.2.2.1 A x hx]
      rfl)
    (fun A _ _ x => by
      rw [← GrOperad.Inv.appHom_star]
      exact congrArg Subtype.val (Bar.mc_apply α x))

variable (h : V →ₗ[R] V)
  (h_odd : ∀ (c : Bool) (x : V), h (SuperMod.pr (R := R) c x) = SuperMod.pr (R := R) (!c) (h x))
  (hdh : ∀ x, DGSuperMod.d (R := R) (h x) + h (DGSuperMod.d (R := R) x) = r.i (r.p x) - x)

/-- **The homotopy transfer theorem**: for a contraction `(i, p, h)` of `V` onto `H`, a twisting
morphism `α : C → End_V` vanishing on the cooperations without inputs, out of a conilpotent dg
cooperad, over a `ℚ`-algebra with the projectivity hypothesis of `BarAdjunction.lean` for the
operations of `End_V` with at least one input, gives the twisting morphism `C → End_H`,
`x ↦ p ∘ v (f x) ∘ (i, …, i)`, for `v` the van der Laan map of `(i ∘ p, h)` and
`f : C → B(End_V⁺)` the morphism commuting with the differentials with `π ∘ f = α`. -/
theorem exists_transfer_End [Algebra ℚ R] (hC : GrCooperad.Conilpotent R C)
    (hproj : ∀ k, Module.Projective R (GrCooperad.Red R C (Fin k)) ∨
      Module.Projective R (BarGen (topI R V) (Fin k)))
    (α : TwistingDG R C (EndGr R V))
    (hα0 : ∀ (A : Type) [Fintype A] [DecidableEq A] [IsEmpty A] (x : C A),
      ConvOp.toLin (α.1.1 A) x = 0) :
    ∃ β : TwistingDG R C (EndGr R H), ∃ g : GrCooperadHom R C (FreeGrL R (BarGen (topI R V))),
      (∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
        (Bar.piL (topI R V) A (g.app A x) : EndGr R V A) = ConvOp.toLin (α.1.1 A) x) ∧
      (∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
        g.app A (DGCooperad.d (R := R) x) = Bar.dTot topI_d A (g.app A x)) ∧
      ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
        ConvOp.toLin (β.1.1 A) x
          = conjE r A (Bar.vdLL (topI R V) (retractPos r h h_odd hdh) A (g.app A x) :
              EndGr R V A) := by
  have hIα : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      ConvOp.toLin ((liftPos α hα0).1.1 A) x ∈ (topI R V).sub A :=
    fun _ _ _ _ => Submodule.mem_top
  have key := Bar.exists_transfer (I := topI R V) topI_d (retractPos r h h_odd hdh)
    topI_zero hC hproj (liftPos α hα0) hIα
  obtain ⟨α', g, hg, hgd, hα', hc⟩ := key
  refine ⟨conjTw r (incTw α') fun A _ _ x => congrArg Subtype.val (hc A x), g,
    fun A _ _ x => congrArg Subtype.val (hg A x), hgd, fun A _ _ x => ?_⟩
  rw [conjTw_apply, ← hα' A x]
  rfl

end Transfer

end EndGr

end Operad
