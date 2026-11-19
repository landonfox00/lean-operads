/-
# The diagonal of the bar construction in shuffle coordinates, for generators of any arity

Step (2c) of the symmetric–shuffle bridge for generators of any arity, fourth part. Setting as in
`Operad.ShuffleAnyTop`. The image of `T^c(sE) → B(P, Ī_P)` is, in shuffle coordinates, the
diagonal: the bar trees with as many generators as components.

* **Evaluations vertex by vertex**: evaluations along families agreeing on the labels of the
  vertices agree (`FreeGrL.shEvF_congr_allV`), and an evaluation along a family vanishing on the
  label of a vertex vanishes (`FreeGrL.shEvF_eq_zero`).
* **The diagonal**: a bar tree `toBar t` has at least as many generators as components
  (`ShuffleAnySym.weight_le_weight_toBar`), with equality iff every vertex of `t` carries a
  monomial with one generator (`ShuffleAnySym.allV_iff_weight_toBar`).
* **The retraction on the shuffle basis**: the retraction of `B(P, Ī_P)(Fin n)` onto the image
  of `T^c(sE)` (`ShuffleAnySym.retrN`) fixes the projections of the basis vectors on the diagonal
  (`ShuffleAnySym.retr_of_allV`) and kills the others (`ShuffleAnySym.retr_of_not_allV`).
* Hence every value of `T^c(sE) → B(P, Ī_P)` is the projection of an element of `B(T, Ī)` whose
  bar trees are on the diagonal (`ShuffleAnySym.exists_diag_lift`), and every combination of bar
  trees on the diagonal comes from `T^c(sE)` (`ShuffleAnySym.exists_cut_of_diag`).
-/
import Operad.ShuffleAnyTop
import Operad.ShuffleEvF

universe u

namespace Operad

open Function Sym GerBV GrComposite STree FreeGr Bar

namespace STree

variable {B : ℕ → Type*}

/-- **Every vertex of the tree carries a label satisfying `P`.** -/
def AllV (P : ∀ k, B k → Prop) : STree B → Prop
  | .leaf _ => True
  | .node β c => P _ β ∧ ∀ j, AllV P (c j)

/-- A tree with a vertex whose label fails `P` has such a vertex at some position. -/
lemma exists_get?_of_not_allV {P : ∀ k, B k → Prop} : ∀ {t : STree B}, ¬AllV P t →
    ∃ (q : List ℕ) (k : ℕ) (β : B k) (ch : Fin k → STree B),
      t.get? q = some (.node β ch) ∧ ¬P k β
  | .leaf _, h => absurd trivial h
  | .node (k := k) β c, h => by
    by_cases hβ : P k β
    · have hex : ∃ j, ¬AllV P (c j) := by
        by_contra hcon
        exact h ⟨hβ, fun j => not_not.1 fun hj => hcon ⟨j, hj⟩⟩
      obtain ⟨j, hj⟩ := hex
      obtain ⟨q, k', β', ch', hq, hP⟩ := exists_get?_of_not_allV hj
      exact ⟨j.1 :: q, k', β', ch', by rw [get?_node_cons_fin]; exact hq, hP⟩
    · exact ⟨[], k, β, c, get?_nil _, hβ⟩

lemma AllV.mono {P Q : ∀ k, B k → Prop} (h : ∀ k β, P k β → Q k β) :
    ∀ {t : STree B}, AllV P t → AllV Q t
  | .leaf _, _ => trivial
  | .node _ _, ht => ⟨h _ _ ht.1, fun j => AllV.mono h (ht.2 j)⟩

end STree

namespace FreeGrL

variable {R : Type u} [CommRing R] {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)] [GrSpecies R W]
  {B : ℕ → Type*}

/-- **Evaluations along families agreeing on the labels of the vertices agree.** -/
theorem shEvF_congr_allV {v v' : ∀ k, B k → W (Fin k)} :
    ∀ (t : STree B) (Y : Finset ℕ) (h : t.labels = Y.val),
      t.AllV (fun k β => v k β = v' k β) → shEvF (R := R) v t Y h = shEvF v' t Y h
  | .leaf a, Y, h, _ => by rw [shEvF_leaf, shEvF_leaf]
  | .node β c, Y, h, hall => by
    rw [shEvF_node, shEvF_node, hall.1]
    congr 3
    funext j
    rw [shEvF_congr_allV (c j) _ _ (hall.2 j)]

/-- **An evaluation along a family vanishing on the label of a vertex vanishes.** -/
theorem shEvF_eq_zero {v : ∀ k, B k → W (Fin k)} {t : STree B} {q : List ℕ} {k : ℕ} {β : B k}
    {ch : Fin k → STree B} (hq : t.get? q = some (.node β ch)) (hβ : v k β = 0) (Y : Finset ℕ)
    (h : t.labels = Y.val) : shEvF (R := R) v t Y h = 0 := by
  have hself : t.replace q (.node β ch) = t := replace_self hq
  have h' : ∀ _ : Unit, (t.replace q (.node β ch)).labels = Y.val := fun _ => by rw [hself, h]
  have := sum_shEvF_replace (R := R) v (Finset.univ : Finset Unit) (fun _ => (1 : R))
    (fun _ => β) ch (by simp [hβ]) q t β hq Y h'
  rw [Fintype.sum_unique, one_smul] at this
  exact (shEvF_congr v hself.symm Y h (h' default)).trans this

end FreeGrL

namespace ShuffleAnySym

open ShuffleBarSym

/-! ## The weight of the bar tree -/

section Weight

variable {T : ℕ → Type}

lemma weight_toBar_node {k : ℕ} (m : VMono T k) (ch : Fin k → STree (VMono T)) :
    (toBar (STree.node m ch)).weight = m.1.1.weight + ∑ j, (toBar (ch j)).weight := by
  rw [toBar_node, weight_subst, weight_fl, labels_fl, m.labels]
  congr 1
  rw [← Finset.range_val, ← Finset.sum_eq_multiset_sum,
    ← Fin.sum_univ_eq_sum_range (fun a => (kids ch a).weight) k]
  exact Finset.sum_congr rfl fun j _ => by rw [kids_fin, weight_cutRoot]

lemma VMono.weight_pos {k : ℕ} (m : VMono T k) : 1 ≤ m.1.1.weight := by
  obtain ⟨l, e, c, h⟩ := m.exists_node
  rw [h]
  simp [STree.weight]

/-- A bar tree has at least as many generators as components. -/
lemma weight_le_weight_toBar : ∀ t : STree (VMono T), t.weight ≤ (toBar t).weight
  | .leaf _ => le_rfl
  | .node m ch => by
    rw [weight_toBar_node]
    have h1 := m.weight_pos
    have h2 : ∑ j, (ch j).weight ≤ ∑ j, (toBar (ch j)).weight :=
      Finset.sum_le_sum fun j _ => weight_le_weight_toBar (ch j)
    simp only [STree.weight]
    omega

/-- **The trees on the diagonal**: as many generators as components iff every vertex carries a
monomial with one generator. -/
theorem allV_iff_weight_toBar : ∀ t : STree (VMono T),
    t.AllV (fun _ m => m.1.1.weight = 1) ↔ (toBar t).weight = t.weight
  | .leaf _ => ⟨fun _ => rfl, fun _ => trivial⟩
  | .node m ch => by
    rw [weight_toBar_node]
    have h1 := m.weight_pos
    have h2 : ∀ j ∈ (Finset.univ : Finset (Fin _)), (ch j).weight ≤ (toBar (ch j)).weight :=
      fun j _ => weight_le_weight_toBar (ch j)
    have h3 := Finset.sum_le_sum h2
    have h4 := Finset.sum_eq_sum_iff_of_le h2
    simp only [STree.weight, STree.AllV]
    constructor
    · rintro ⟨hm, hall⟩
      have : ∑ j, (ch j).weight = ∑ j, (toBar (ch j)).weight :=
        h4.2 fun j _ => ((allV_iff_weight_toBar (ch j)).1 (hall j)).symm
      omega
    · intro h
      have hsum : ∑ j, (ch j).weight = ∑ j, (toBar (ch j)).weight := by omega
      exact ⟨by omega, fun j =>
        (allV_iff_weight_toBar (ch j)).2 (h4.1 hsum j (Finset.mem_univ j)).symm⟩

end Weight

/-! ## The retraction onto the generators, vertex by vertex -/

section Retr

variable {K : Type u} [Field K] [CharZero K]
  {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {T : ℕ → Type} [IsEmpty (T 0)] [IsEmpty (T 1)]
  (c : ∀ k, Module.Basis (T k) K (E (Fin k)))
  (hc : ∀ k (β : T k), GrSpecies.par (R := K) false (c k β) = c k β)
  (r : ∀ n : ℕ, Set (FreeGrL K E (Fin n)))
  (hq : Koszul.IsQuadratic K E r)

local notation "𝒥" => GrOperadIdeal.span K r

omit [CharZero K] [IsEmpty (T 1)] in
/-- A basis monomial with `w` generators has `w` vertices. -/
lemma tBasis_mem_vx {k : ℕ} (m : VMono T k) :
    (idealBasis c hc k m : FreeGrL K E (Fin k)) ∈ FreeGrL.vx K E m.1.1.weight (Fin k) := by
  rw [idealBasis_apply, tBasis_apply, FreeGrL.shuffleBasis_apply]
  exact FreeGrL.map_mem_eig _ (FreeGrL.shEv_mem_vx c hc _ m.1.1 le_rfl m.1.2.1 _ _)

/-- The generators of the bar construction of the presented operad over the basis monomials. -/
noncomputable def projGen (k : ℕ) (m : VMono T k) : BarGen (Ipres K E c hc r) (Fin k) :=
  (barProjGen c hc r).app (Fin k) (genBasis c hc k m)

/-- The same generators, through the retraction onto `sE`. -/
noncomputable def retrGen (k : ℕ) (m : VMono T k) : BarGen (Ipres K E c hc r) (Fin k) :=
  (Koszul.barGen (Ipres K E c hc r) (hE_pres c hc r)).app (Fin k)
    ((barRet c hc r hq).app (Fin k) (projGen c hc r k m))

omit [IsEmpty (T 1)] in
lemma barRet_projGen {k : ℕ} (m : VMono T k) :
    (barRet c hc r hq).app (Fin k) (projGen c hc r k m)
      = FreeGrL.genCoef K E (Fin k) (idealBasis c hc k m : FreeGrL K E (Fin k)) := rfl

/-- **The retraction fixes the monomials with one generator.** -/
lemma retrGen_of_weight_one {k : ℕ} {m : VMono T k} (hm : m.1.1.weight = 1) :
    retrGen c hc r hq k m = projGen c hc r k m := by
  refine IdealSp.ext _ ?_
  show (𝒥).proj (Fin k) ((FreeGrL.ι K E).app (Fin k)
    (FreeGrL.genCoef K E (Fin k) (idealBasis c hc k m : FreeGrL K E (Fin k))))
      = (𝒥).proj (Fin k) (idealBasis c hc k m : FreeGrL K E (Fin k))
  have h1 := tBasis_mem_vx c hc m
  rw [hm] at h1
  rw [← FreeGrL.eq_ι_genCoef h1]

/-- **The retraction kills the monomials with several generators.** -/
lemma retrGen_of_weight_ne_one {k : ℕ} {m : VMono T k} (hm : m.1.1.weight ≠ 1) :
    retrGen c hc r hq k m = 0 := by
  rw [retrGen, barRet_projGen, CutLift.genCoef_of_mem_vx hm (tBasis_mem_vx c hc m)]
  exact map_zero _

/-! ## The retraction on the shuffle basis -/

/-- The projection `B(T, Ī)(Fin n) → B(P, Ī_P)(Fin n)`. -/
noncomputable def projN (n : ℕ) : BarCoop (Ibar K E c hc) (Fin n) →ₗ[K]
    FreeGrL K (BarGen (Ipres K E c hc r)) (Fin n) :=
  (FreeGrL.mapSp (barProjGen c hc r)).app (Fin n)

/-- The morphism `T^c(sE)(Fin n) → B(P, Ī_P)(Fin n)`. -/
noncomputable def cutN (n : ℕ) : Koszul.Cut K E (Fin n) →ₗ[K]
    FreeGrL K (BarGen (Ipres K E c hc r)) (Fin n) :=
  (FreeGrL.mapSp (Koszul.barGen (Ipres K E c hc r) (hE_pres c hc r))).app (Fin n)

/-- The retraction of `B(P, Ī_P)(Fin n)` onto the image of `T^c(sE)(Fin n)`. -/
noncomputable def retrN (n : ℕ) : FreeGrL K (BarGen (Ipres K E c hc r)) (Fin n) →ₗ[K]
    FreeGrL K (BarGen (Ipres K E c hc r)) (Fin n) :=
  cutN c hc r n ∘ₗ (FreeGrL.mapSp (barRet c hc r hq)).app (Fin n)

/-- The retraction fixes the image of `T^c(sE)`. -/
lemma retrN_cutN (n : ℕ) (y : Koszul.Cut K E (Fin n)) :
    retrN c hc r hq n (cutN c hc r n y) = cutN c hc r n y :=
  congrArg (cutN c hc r n) (mapSp_barRet_barGen c hc r hq y)

/-- The values of the retraction come from `T^c(sE)`. -/
lemma retrN_mem_range (n : ℕ) (z : FreeGrL K (BarGen (Ipres K E c hc r)) (Fin n)) :
    retrN c hc r hq n z ∈ LinearMap.range (cutN c hc r n) := ⟨_, rfl⟩

omit [CharZero K] [IsEmpty (T 0)] [IsEmpty (T 1)] in
lemma labN {n : ℕ} (t : SMono (VMono T) (Finset.range n)) :
    t.1.labels = (Finset.range (Fintype.card (Fin n))).val := by
  rw [Fintype.card_fin]
  exact t.2.2

omit [CharZero K] [IsEmpty (T 1)] in
lemma mapSp_proj_shEv (n : ℕ) (t : SMono (VMono T) (Finset.range n)) :
    (FreeGrL.mapSp (barProjGen c hc r)).app _ (FreeGrL.shEv (genBasis c hc) t.1 _ (labN t))
      = FreeGrL.shEvF (R := K) (W := BarGen (Ipres K E c hc r)) (projGen c hc r) t.1 _
          (labN t) := by
  rw [FreeGrL.shEv_eq_shEvF]
  exact FreeGrL.mapSp_shEvF _ _ _ _ _

lemma mapSp_retr_shEvF (n : ℕ) (t : SMono (VMono T) (Finset.range n)) :
    (FreeGrL.mapSp (Koszul.barGen (Ipres K E c hc r) (hE_pres c hc r))).app _
      ((FreeGrL.mapSp (barRet c hc r hq)).app _
        (FreeGrL.shEvF (R := K) (W := BarGen (Ipres K E c hc r)) (projGen c hc r) t.1 _
          (labN t)))
      = FreeGrL.shEvF (R := K) (W := BarGen (Ipres K E c hc r)) (retrGen c hc r hq) t.1 _
          (labN t) :=
  (congrArg _ (FreeGrL.mapSp_shEvF _ _ _ _ _)).trans (FreeGrL.mapSp_shEvF _ _ _ _ _)

omit [CharZero K] [IsEmpty (T 1)] in
/-- The projection of a basis vector of `B(T, Ī)`, as an evaluation. -/
lemma projN_barBasisN (n : ℕ) (t : SMono (VMono T) (Finset.range n)) :
    projN c hc r n (barBasisN c hc n t)
      = GrOperad.map (R := K) (FreeGrL.posEquiv (Fin n)).symm
        (FreeGrL.shEvF (R := K) (W := BarGen (Ipres K E c hc r)) (projGen c hc r) t.1 _
          (labN t)) := by
  have h1 := congrArg (projN c hc r n) (barBasisN_eq_shEv c hc n t (labN t))
  have h2 := GrOperadHom.app_map (FreeGrL.mapSp (barProjGen c hc r))
    (FreeGrL.posEquiv (Fin n)).symm (FreeGrL.shEv (genBasis c hc) t.1 _ (labN t))
  exact h1.trans (h2.trans (congrArg (GrOperad.map (R := K) (FreeGrL.posEquiv (Fin n)).symm)
    (mapSp_proj_shEv c hc r n t)))

/-- The retraction onto `T^c(sE)` of the projection of a basis vector, as an evaluation. -/
lemma retr_barBasisN (n : ℕ) (t : SMono (VMono T) (Finset.range n)) :
    retrN c hc r hq n (projN c hc r n (barBasisN c hc n t))
      = GrOperad.map (R := K) (FreeGrL.posEquiv (Fin n)).symm
        (FreeGrL.shEvF (R := K) (W := BarGen (Ipres K E c hc r)) (retrGen c hc r hq) t.1 _
          (labN t)) := by
  have h1 := congrArg (retrN c hc r hq n) (projN_barBasisN c hc r n t)
  have h2 := (congrArg (cutN c hc r n) (GrOperadHom.app_map (FreeGrL.mapSp (barRet c hc r hq))
    (FreeGrL.posEquiv (Fin n)).symm (FreeGrL.shEvF (R := K)
      (W := BarGen (Ipres K E c hc r)) (projGen c hc r)
      t.1 _ (labN t)))).trans (GrOperadHom.app_map
        (FreeGrL.mapSp (Koszul.barGen (Ipres K E c hc r) (hE_pres c hc r)))
        (FreeGrL.posEquiv (Fin n)).symm _)
  exact h1.trans (h2.trans (congrArg (GrOperad.map (R := K) (FreeGrL.posEquiv (Fin n)).symm)
    (mapSp_retr_shEvF c hc r hq n t)))

/-- **The retraction fixes the basis vectors on the diagonal.** -/
theorem retr_of_allV {n : ℕ} {t : SMono (VMono T) (Finset.range n)}
    (hall : t.1.AllV (fun _ m => m.1.1.weight = 1)) :
    retrN c hc r hq n (projN c hc r n (barBasisN c hc n t))
      = projN c hc r n (barBasisN c hc n t) := by
  have h2 : FreeGrL.shEvF (R := K) (W := BarGen (Ipres K E c hc r)) (retrGen c hc r hq) t.1 _
      (labN t) = FreeGrL.shEvF (R := K) (W := BarGen (Ipres K E c hc r)) (projGen c hc r)
        t.1 _ (labN t) :=
    FreeGrL.shEvF_congr_allV t.1 _ (labN t)
      (hall.mono fun _ _ hm => retrGen_of_weight_one c hc r hq hm)
  exact (retr_barBasisN c hc r hq n t).trans ((congrArg (GrOperad.map (R := K)
    (P := FreeGrL K (BarGen (Ipres K E c hc r)))
    (FreeGrL.posEquiv (Fin n)).symm) h2).trans
    (projN_barBasisN c hc r n t).symm)

lemma retr_of_get? {n : ℕ} {t : SMono (VMono T) (Finset.range n)} {q : List ℕ} {k : ℕ}
    {β : VMono T k} {ch : Fin k → STree (VMono T)} (hq' : t.1.get? q = some (.node β ch))
    (hβ : β.1.1.weight ≠ 1) :
    retrN c hc r hq n (projN c hc r n (barBasisN c hc n t)) = 0 := by
  have h2 : FreeGrL.shEvF (R := K) (W := BarGen (Ipres K E c hc r)) (retrGen c hc r hq) t.1 _
      (labN t) = 0 :=
    FreeGrL.shEvF_eq_zero hq' (retrGen_of_weight_ne_one c hc r hq hβ) _ (labN t)
  exact (retr_barBasisN c hc r hq n t).trans ((congrArg (GrOperad.map (R := K)
    (P := FreeGrL K (BarGen (Ipres K E c hc r)))
    (FreeGrL.posEquiv (Fin n)).symm) h2).trans
    (LinearMap.map_zero _))

/-- **The retraction kills the basis vectors off the diagonal.** -/
theorem retr_of_not_allV {n : ℕ} {t : SMono (VMono T) (Finset.range n)}
    (hall : ¬t.1.AllV (fun _ m => m.1.1.weight = 1)) :
    retrN c hc r hq n (projN c hc r n (barBasisN c hc n t)) = 0 := by
  have h := exists_get?_of_not_allV hall
  obtain ⟨q, k, β, ch, hq', hβ⟩ := h
  exact retr_of_get? c hc r hq hq' hβ

include hq in
/-- The projection of a basis vector on the diagonal comes from `T^c(sE)`. -/
lemma projN_mem_range_of_allV {n : ℕ} {t : SMono (VMono T) (Finset.range n)}
    (hall : t.1.AllV (fun _ m => m.1.1.weight = 1)) :
    projN c hc r n (barBasisN c hc n t) ∈ LinearMap.range (cutN c hc r n) :=
  ⟨(FreeGrL.mapSp (barRet c hc r hq)).app (Fin n) (projN c hc r n (barBasisN c hc n t)),
    retr_of_allV c hc r hq hall⟩

/-! ## The diagonal -/

variable (T) in
/-- **The bar trees on the diagonal**: as many generators as components. -/
def diagSet (n : ℕ) : Set (SMono (BE T) (Finset.range n)) :=
  {X | rootF X.1 = false ∧ X.1.weight = (cuts X).card + 1}

omit [CharZero K] in
lemma treeEquiv_mem_diagSet {n : ℕ} (hn : 2 ≤ n) (t : SMono (VMono T) (Finset.range n)) :
    (treeEquiv n t : barSet T n).1 ∈ diagSet T n ↔ t.1.AllV (fun _ m => m.1.1.weight = 1) := by
  rw [allV_iff_weight_toBar]
  have h1 := card_cuts_treeEquiv hn t
  constructor
  · rintro ⟨-, h⟩
    have h' : (toBar t.1).weight = (cuts (treeEquiv n t : barSet T n).1).card + 1 := h
    omega
  · intro h
    refine ⟨(treeEquiv n t).2, ?_⟩
    show (toBar t.1).weight = _
    omega

/-- **The diagonal part** of an element of the bar construction `B(T, Ī)`. -/
noncomputable def diagPart (n : ℕ) :
    BarCoop (Ibar K E c hc) (Fin n) →ₗ[K] BarCoop (Ibar K E c hc) (Fin n) :=
  (barBasisN c hc n).constr K fun t =>
    @ite _ (t.1.AllV (fun _ m => m.1.1.weight = 1)) (Classical.propDecidable _)
      (barBasisN c hc n t) 0

omit [CharZero K] [IsEmpty (T 1)] in
lemma diagPart_of_allV {n : ℕ} {t : SMono (VMono T) (Finset.range n)}
    (hall : t.1.AllV (fun _ m => m.1.1.weight = 1)) :
    diagPart c hc n (barBasisN c hc n t) = barBasisN c hc n t := by
  rw [diagPart, Module.Basis.constr_basis, if_pos hall]

omit [CharZero K] [IsEmpty (T 1)] in
lemma diagPart_of_not_allV {n : ℕ} {t : SMono (VMono T) (Finset.range n)}
    (hall : ¬t.1.AllV (fun _ m => m.1.1.weight = 1)) :
    diagPart c hc n (barBasisN c hc n t) = 0 := by
  rw [diagPart, Module.Basis.constr_basis, if_neg hall]

/-- **The projection of the diagonal part is the retraction of the projection.** -/
theorem barProj_diagPart (n : ℕ) (v : BarCoop (Ibar K E c hc) (Fin n)) :
    projN c hc r n (diagPart c hc n v)
      = retrN c hc r hq n (projN c hc r n v) := by
  have h : projN c hc r n ∘ₗ diagPart c hc n
      = retrN c hc r hq n ∘ₗ projN c hc r n :=
    (barBasisN c hc n).ext fun t => by
      show projN c hc r n (diagPart c hc n (barBasisN c hc n t))
        = retrN c hc r hq n (projN c hc r n (barBasisN c hc n t))
      by_cases hall : t.1.AllV (fun _ m => m.1.1.weight = 1)
      · exact (congrArg (projN c hc r n) (diagPart_of_allV c hc hall)).trans
          (retr_of_allV c hc r hq hall).symm
      · exact (congrArg (projN c hc r n) (diagPart_of_not_allV c hc hall)).trans
          ((map_zero _).trans (retr_of_not_allV c hc r hq hall).symm)
  exact LinearMap.congr_fun h v

omit [CharZero K] in
/-- **The diagonal part lies on the diagonal.** -/
theorem ΦL_diagPart_mem {n : ℕ} (hn : 2 ≤ n) (v : BarCoop (Ibar K E c hc) (Fin n)) :
    ΦL c hc n (diagPart c hc n v) ∈ Finsupp.supported K K (diagSet T n) := by
  have hle : LinearMap.range (ΦL c hc n ∘ₗ diagPart c hc n)
      ≤ Finsupp.supported K K (diagSet T n) := by
    rw [LinearMap.range_eq_map, ← (barBasisN c hc n).span_eq, Submodule.map_span,
      Submodule.span_le]
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    rw [LinearMap.comp_apply]
    by_cases hall : t.1.AllV (fun _ m => m.1.1.weight = 1)
    · rw [diagPart_of_allV c hc hall, Φ_barBasisN]
      exact Submodule.smul_mem _ _ (Finsupp.single_mem_supported K _
        ((treeEquiv_mem_diagSet hn t).2 hall))
    · rw [diagPart_of_not_allV c hc hall, map_zero]
      exact zero_mem _
  exact hle (LinearMap.mem_range_self _ v)

include hq in
/-- **`T^c(sE)` lifts to the diagonal**: every value of `T^c(sE) → B(P, Ī_P)` is the projection
of an element of `B(T, Ī)` whose bar trees are on the diagonal. -/
theorem exists_diag_lift {n : ℕ} (hn : 2 ≤ n) (y : Koszul.Cut K E (Fin n)) :
    ∃ v : BarCoop (Ibar K E c hc) (Fin n),
      projN c hc r n v
        = cutN c hc r n y ∧
      ΦL c hc n v ∈ Finsupp.supported K K (diagSet T n) := by
  obtain ⟨v₀, hv₀⟩ := barProj_surjective c hc r (Fin n) (cutN c hc r n y)
  refine ⟨diagPart c hc n v₀, ?_, ΦL_diagPart_mem c hc hn v₀⟩
  have hv₀' : projN c hc r n v₀ = cutN c hc r n y := hv₀
  exact (barProj_diagPart c hc r hq n v₀).trans
    ((congrArg (retrN c hc r hq n) hv₀').trans (retrN_cutN c hc r hq n y))

/-- **The combinations of bar trees coming from `T^c(sE)`**: `ΦL` of the elements of `B(T, Ī)`
whose projection is a value of `T^c(sE) → B(P, Ī_P)`. -/
noncomputable def cutSub (n : ℕ) : Submodule K (SMono (BE T) (Finset.range n) →₀ K) where
  carrier := {X | ∃ (v : BarCoop (Ibar K E c hc) (Fin n)) (y : Koszul.Cut K E (Fin n)),
    ΦL c hc n v = X ∧ projN c hc r n v = cutN c hc r n y}
  add_mem' := by
    rintro _ _ ⟨v, y, rfl, hy⟩ ⟨v', y', rfl, hy'⟩
    exact ⟨v + v', y + y', map_add _ _ _,
      (LinearMap.map_add _ _ _).trans ((congrArg₂ (· + ·) hy hy').trans
        (LinearMap.map_add _ _ _).symm)⟩
  zero_mem' := ⟨0, 0, map_zero _, (LinearMap.map_zero _).trans (LinearMap.map_zero _).symm⟩
  smul_mem' := by
    rintro a _ ⟨v, y, rfl, hy⟩
    exact ⟨a • v, a • y, map_smul _ _ _,
      (LinearMap.map_smul _ _ _).trans ((congrArg (a • ·) hy).trans
        (LinearMap.map_smul _ _ _).symm)⟩

omit [CharZero K] in
lemma mem_cutSub {n : ℕ} {X : SMono (BE T) (Finset.range n) →₀ K} :
    X ∈ cutSub c hc r n ↔ ∃ (v : BarCoop (Ibar K E c hc) (Fin n)) (y : Koszul.Cut K E (Fin n)),
      ΦL c hc n v = X ∧ projN c hc r n v = cutN c hc r n y := Iff.rfl

include hq in
/-- A bar tree on the diagonal comes from `T^c(sE)`. -/
lemma single_mem_cutSub {n : ℕ} (hn : 2 ≤ n) {X : SMono (BE T) (Finset.range n)}
    (hX : X ∈ diagSet T n) : Finsupp.single X (1 : K) ∈ cutSub c hc r n := by
  obtain ⟨t, ht⟩ := (treeEquiv n).surjective ⟨X, hX.1⟩
  have hX' : (treeEquiv n t : barSet T n).1 = X := congrArg Subtype.val ht
  have hall : t.1.AllV (fun _ m => m.1.1.weight = 1) :=
    (treeEquiv_mem_diagSet hn t).1 (hX'.symm ▸ hX)
  have h1 : projN c hc r n (wsign K t.1 • barBasisN c hc n t)
      = wsign K t.1 • projN c hc r n (barBasisN c hc n t) := LinearMap.map_smul _ _ _
  have h2 : projN c hc r n (wsign K t.1 • barBasisN c hc n t)
      ∈ LinearMap.range (cutN c hc r n) :=
    (congrArg (· ∈ LinearMap.range (cutN c hc r n)) h1).mpr
      ((LinearMap.range (cutN c hc r n)).smul_mem (wsign K t.1)
        (projN_mem_range_of_allV c hc r hq hall))
  obtain ⟨y, hy⟩ := LinearMap.mem_range.1 h2
  refine (mem_cutSub c hc r).2 ⟨wsign K t.1 • barBasisN c hc n t, y, ?_, hy.symm⟩
  rw [map_smul, Φ_barBasisN, smul_smul, wsign_mul_self, one_smul, hX']

include hq in
/-- **The diagonal comes from `T^c(sE)`**: a combination of bar trees on the diagonal is `ΦL` of
an element of `B(T, Ī)` whose projection is a value of `T^c(sE) → B(P, Ī_P)`. -/
theorem exists_cut_of_diag {n : ℕ} (hn : 2 ≤ n) {X : SMono (BE T) (Finset.range n) →₀ K}
    (hX : X ∈ Finsupp.supported K K (diagSet T n)) :
    ∃ (v : BarCoop (Ibar K E c hc) (Fin n)) (y : Koszul.Cut K E (Fin n)), ΦL c hc n v = X ∧
      projN c hc r n v = cutN c hc r n y := by
  have hle : Finsupp.supported K K (diagSet T n) ≤ cutSub c hc r n := by
    rw [Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨Y, hY, rfl⟩
    exact single_mem_cutSub c hc r hq hn hY
  exact (mem_cutSub c hc r).1 (hle hX)

end Retr

end ShuffleAnySym

end Operad
