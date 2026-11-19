/-
# The kernel of the projection of the bar constructions, for generators of any arity

Step (2c) of the symmetric–shuffle bridge for generators of any arity, sixth part; the binary
case is the middle of `Operad.ShuffleBarJ`. Setting as in `Operad.ShuffleAnyProj`.

* **A vertex labelled by an operation** (`ShuffleAnySym.Tq`): for a shuffle tree of monomials
  `t` and a vertex at the position `q`, the trees with that vertex labelled by each basis
  monomial, with the coordinates of an operation `y ∈ T(E) (Fin k)`. For `y` in the ideal `(r)`
  they lie in the relator ideal `Krel` (`ShuffleAnySym.Tq_mem_Krel`).
* **The kernel of the projection** `B(T, Ī) → B(P, Ī_P)` is spanned by these trees
  (`ShuffleAnySym.krel_eq_span`): choosing basis monomials `S k` whose images form a basis of
  `sĪ_P (Fin k)` (`ShuffleAnySym.exists_sel`), the projection is injective on the trees with all
  vertex labels in `S` (`ShuffleAnySym.eq_zero_of_mem_sel`), and every tree is a combination of
  those modulo the trees labelled at one vertex by `(r)` (`ShuffleAnySym.barBasisN_mem_sup`).

The generators need not be finite in number: the coordinates of an operation are a finitely
supported function on the monomials.
-/
import Operad.ShuffleAnyCrit
import Operad.ShuffleBarJ

universe u v w x

namespace Operad

open Function Sym GerBV GrComposite STree FreeGr Bar

namespace ShuffleAnySym

open ShuffleBarSym

/-! ## Counting the vertices outside a set of labels -/

section Count

variable {T : ℕ → Type} (S : ∀ k, Set (VMono T k))

open Classical in
/-- **The number of vertices whose label is not in `S`.** -/
noncomputable def nS : STree (VMono T) → ℕ
  | .leaf _ => 0
  | .node (k := k) m ch => (if m ∈ S k then 0 else 1) + ∑ j, nS (ch j)

open Classical in
lemma nS_node {k : ℕ} (m : VMono T k) (ch : Fin k → STree (VMono T)) :
    nS S (.node m ch) = (if m ∈ S k then 0 else 1) + ∑ j, nS S (ch j) := by
  rw [nS]

lemma mem_of_nS_node {k : ℕ} {m : VMono T k} {ch : Fin k → STree (VMono T)}
    (h : nS S (.node m ch) = 0) : m ∈ S k := by
  classical
  rw [nS_node] at h
  by_contra hm
  rw [if_neg hm] at h
  omega

lemma nS_child {k : ℕ} {m : VMono T k} {ch : Fin k → STree (VMono T)}
    (h : nS S (.node m ch) = 0) (j : Fin k) : nS S (ch j) = 0 := by
  rw [nS_node] at h
  exact (Finset.sum_eq_zero_iff.1 (Nat.add_eq_zero_iff.1 h).2) j (Finset.mem_univ j)

open Classical in
/-- **Relabelling one vertex** changes the count by the membership of the two labels. -/
lemma nS_replace {k : ℕ} (m m' : VMono T k) (ch : Fin k → STree (VMono T)) :
    ∀ (q : List ℕ) (t : STree (VMono T)), t.get? q = some (.node m ch) →
      nS S (t.replace q (.node m' ch)) + (if m ∈ S k then 0 else 1)
        = nS S t + (if m' ∈ S k then 0 else 1)
  | [], t, ht => by
    rw [get?_nil, Option.some_inj] at ht
    subst ht
    rw [replace_nil, nS_node, nS_node]
    omega
  | _ :: _, .leaf _, ht => by simp at ht
  | i :: q, .node (k := k') γ c, ht => by
    obtain ⟨hi, hc⟩ := get?_node_cons_eq_some.1 ht
    have ih := nS_replace m m' ch q _ hc
    rw [replace_node_cons, nS_node, nS_node]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨i, hi⟩ : Fin k')),
      ← Finset.add_sum_erase _ (fun j => nS S (c j)) (Finset.mem_univ (⟨i, hi⟩ : Fin k'))]
    have hrest : ∑ j ∈ Finset.univ.erase (⟨i, hi⟩ : Fin k'), nS S (if (j : ℕ) = i then
        (c j).replace q (.node m' ch) else c j)
          = ∑ j ∈ Finset.univ.erase (⟨i, hi⟩ : Fin k'), nS S (c j) :=
      Finset.sum_congr rfl fun j hj => by
        rw [if_neg fun h => Finset.ne_of_mem_erase hj (Fin.ext h)]
    rw [hrest, if_pos rfl]
    omega

/-- **A tree with a vertex outside `S` has one at some position.** -/
lemma exists_get?_not_mem : ∀ t : STree (VMono T), nS S t ≠ 0 →
    ∃ (q : List ℕ) (k : ℕ) (m : VMono T k) (ch : Fin k → STree (VMono T)),
      t.get? q = some (.node m ch) ∧ m ∉ S k
  | .leaf _, h => absurd rfl h
  | .node (k := k) m ch, h => by
    by_cases hm : m ∈ S k
    · obtain ⟨j, hj⟩ : ∃ j, nS S (ch j) ≠ 0 := by
        by_contra hall
        exact h (by
          classical
          rw [nS_node, if_pos hm, Finset.sum_eq_zero fun j _ => not_not.1 fun hj => hall ⟨j, hj⟩]
          rfl)
      obtain ⟨q, k', m', ch', hq, hm'⟩ := exists_get?_not_mem (ch j) hj
      exact ⟨j.1 :: q, k', m', ch', by rw [get?_node_cons_fin]; exact hq, hm'⟩
    · exact ⟨[], k, m, ch, get?_nil _, hm⟩

/-- **The tree over `S` of a tree with all vertices in `S`.** -/
noncomputable def liftS : (t : STree (VMono T)) → nS S t = 0 → STree fun k => ↥(S k)
  | .leaf a, _ => .leaf a
  | .node m ch, h => .node ⟨m, mem_of_nS_node S h⟩ fun j => liftS (ch j) (nS_child S h j)

lemma mapV_liftS : ∀ (t : STree (VMono T)) (h : nS S t = 0),
    (liftS S t h).mapV (fun _ m => m.1) = t
  | .leaf _, _ => rfl
  | .node m ch, h => by
    show STree.node m (fun j => (liftS S (ch j) (nS_child S h j)).mapV _) = _
    congr 1
    funext j
    exact mapV_liftS (ch j) _

end Count

/-! ## A vertex labelled by an operation -/

section Vertex

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {T : ℕ → Type} [IsEmpty (T 0)] [IsEmpty (T 1)]
  (c : ∀ k, Module.Basis (T k) K (E (Fin k)))
  (hc : ∀ k (β : T k), GrSpecies.par (R := K) false (c k β) = c k β)
  (r : ∀ n : ℕ, Set (FreeGrL K E (Fin n)))

local notation "𝒥" => GrOperadIdeal.span K r

variable {n : ℕ} (t : SMono (VMono T) (Finset.range n)) {q : List ℕ} {k : ℕ} {m₀ : VMono T k}
  {ch : Fin k → STree (VMono T)} (hq : t.1.get? q = some (.node m₀ ch))

/-- **The tree with the vertex at `q` relabelled by `m`.** -/
def replT (m : VMono T k) : SMono (VMono T) (Finset.range n) :=
  ⟨t.1.replace q (.node m ch), isShuffle_replace t.2.1 hq
    (isShuffle_get? t.2.1 hq : (STree.node m₀ ch).IsShuffle) rfl,
    (labels_replace_of_eq (v := .node m ch) hq rfl).trans t.2.2⟩

omit [IsEmpty (T 0)] [IsEmpty (T 1)] in
lemma get?_replT (m : VMono T k) : (replT t hq m).1.get? q = some (.node m ch) :=
  get?_replace (by rw [hq]; rfl) _

omit [IsEmpty (T 0)] [IsEmpty (T 1)] in
lemma replT_replT (m m' : VMono T k) :
    replT (replT t hq m) (get?_replT t hq m) m' = replT t hq m' :=
  Subtype.ext (replace_replace _ _ _ _)

/-- **The trees with the vertex at `q` labelled by an operation of arity `k`**: the operation
written in the basis `tBasis`, each basis monomial labelling the vertex. -/
noncomputable def Tq : FreeGrL K E (Fin k) →ₗ[K] BarCoop (Ibar K E c hc) (Fin n) :=
  (tBasis c hc (Fin k)).constr K fun i => barBasisN c hc n
    (replT t hq ⟨⟨i.1, i.2.1, by simpa using i.2.2⟩, m₀.2⟩)

omit [IsEmpty (T 1)] in
lemma Tq_tBasis (m : VMono T k) :
    Tq c hc t hq (tBasis c hc (Fin k) m.idx) = barBasisN c hc n (replT t hq m) := by
  rw [Tq, Module.Basis.constr_basis]
  rfl

omit [IsEmpty (T 1)] in
/-- **The trees labelled by an operation of the relator ideal lie in the relator ideal of the bar
construction.** -/
theorem Tq_mem_Krel {y : FreeGrL K E (Fin k)} (hy : y ∈ (𝒥).sub (Fin k)) :
    Tq c hc t hq y ∈ (Krel K E c hc r).sub (Fin n) := by
  refine (mem_Krel_iff c hc r (A := Fin n) (Tq c hc t hq y)).2 ?_
  let βs : SMono T (Finset.range (Fintype.card (Fin k))) → VMono T k :=
    fun i => ⟨⟨i.1, i.2.1, by simpa using i.2.2⟩, m₀.2⟩
  let a := fun i => (tBasis c hc (Fin k)).repr y i
  let s := ((tBasis c hc (Fin k)).repr y).support
  have hlab : ∀ i, (t.1.replace q (.node (βs i) ch)).labels
      = (Finset.range (Fintype.card (Fin n))).val := fun i =>
    (replT t hq (βs i)).2.2.trans (by rw [Fintype.card_fin])
  have hsum : Tq c hc t hq y = ∑ i ∈ s, a i • GrOperad.map (R := K)
      (FreeGrL.posEquiv (Fin n)).symm
      (FreeGrL.shEv (genBasis c hc) (t.1.replace q (.node (βs i) ch)) _ (hlab i)) := by
    rw [Tq, Module.Basis.constr_apply]
    exact Finset.sum_congr rfl fun i _ =>
      congrArg (a i • ·) (barBasisN_eq_shEv c hc n _ (hlab i))
  have hz : IdealSp.val _ (∑ i ∈ s, a i • genBasis c hc k (βs i)) = y := by
    show ((∑ i ∈ s, a i • idealBasis c hc k (βs i) : (Ibar K E c hc).sub (Fin k)) :
      FreeGrL K E (Fin k)) = y
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul, idealBasis_apply]
    have h := (tBasis c hc (Fin k)).linearCombination_repr y
    rw [Finsupp.linearCombination_apply] at h
    exact h
  have hv : ∑ i ∈ s, a i • (barProjGen c hc r).app (Fin k) (genBasis c hc k (βs i))
      = 0 := by
    simp only [← map_smul, ← map_sum]
    rw [barProjGen_eq_zero_iff]
    convert hy using 1
  exact (congrArg ((FreeGrL.mapSp (barProjGen c hc r)).app (Fin n)) hsum).trans
    (FreeGrL.mapSp_sum_shEv_replace (genBasis c hc) (barProjGen c hc r) s a βs ch hv q
      t.1 m₀ hq _ hlab)

end Vertex

/-! ## The kernel of the projection of the bar constructions -/

section Kernel

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {T : ℕ → Type} [IsEmpty (T 0)] [IsEmpty (T 1)]
  (c : ∀ k, Module.Basis (T k) K (E (Fin k)))
  (hc : ∀ k (β : T k), GrSpecies.par (R := K) false (c k β) = c k β)
  (r : ∀ n : ℕ, Set (FreeGrL K E (Fin n)))

local notation "𝒥" => GrOperadIdeal.span K r

omit [IsEmpty (T 1)] in
/-- **A basis of `sĪ_P` among the images of the basis of `sĪ`.** -/
lemma exists_sel (k : ℕ) : ∃ S : Set (VMono T k),
    LinearIndependent K (fun m : S => projGen c hc r k m.1) ∧
      ⊤ ≤ Submodule.span K (Set.range fun m : S => projGen c hc r k m.1) := by
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K (projGen c hc r k)
  refine ⟨Set.range a, (linearIndependent_equiv (Equiv.ofInjective a ha)
    (f := fun m : Set.range a => projGen c hc r k m.1)).1 hli, ?_⟩
  have hr : (Set.range fun m : Set.range a => projGen c hc r k m.1)
      = Set.range (projGen c hc r k ∘ a) := by
    ext x
    constructor
    · rintro ⟨⟨_, y, rfl⟩, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨⟨a y, y, rfl⟩, rfl⟩
  rw [hr, hsp, show (projGen c hc r k) = (barProjGen c hc r).app (Fin k) ∘ genBasis c hc k from rfl,
    Set.range_comp, Submodule.span_image, (genBasis c hc k).span_eq, Submodule.map_top,
    LinearMap.range_eq_top.2 (barProjGen_surjective c hc r (Fin k))]

variable (S : ∀ k, Set (VMono T k))
  (hli : ∀ k, LinearIndependent K (fun m : S k => projGen c hc r k m.1))
  (hsp : ∀ k, ⊤ ≤ Submodule.span K (Set.range fun m : S k => projGen c hc r k m.1))

/-- The chosen basis of `sĪ_P`. -/
noncomputable def selBasis (k : ℕ) : Module.Basis (S k) K (BarGen (Ipres K E c hc r) (Fin k)) :=
  Module.Basis.mk (hli k) (hsp k)

include hli hsp in
omit [IsEmpty (T 1)] in
lemma selBasis_apply (k : ℕ) (j : S k) : selBasis c hc r S hli hsp k j = projGen c hc r k j.1 :=
  Module.Basis.mk_apply _ _ _

include hli hsp in
omit [IsEmpty (T 1)] in
lemma par_selBasis (k : ℕ) (j : S k) :
    GrSpecies.par (R := K) ((fun _ _ => true) k j) (selBasis c hc r S hli hsp k j)
      = selBasis c hc r S hli hsp k j := by
  rw [selBasis_apply, projGen, ← (barProjGen c hc r).app_par]
  exact congrArg _ (par_genBasis c hc k j.1)

include hli hsp in
omit [IsEmpty (T 1)] in
/-- **The projection is injective on the trees with all vertices in `S`.** -/
theorem eq_zero_of_mem_sel {n : ℕ} {x : BarCoop (Ibar K E c hc) (Fin n)}
    (hx : x ∈ Submodule.span K (Set.range fun t : {t : SMono (VMono T) (Finset.range n) //
      nS S t.1 = 0} => barBasisN c hc n t.1))
    (hπ : (FreeGrL.mapSp (barProjGen c hc r)).app (Fin n) x = 0) : x = 0 := by
  haveI : IsEmpty (S 0) := ⟨fun m => isEmptyElim m.1⟩
  let φ : {t : SMono (VMono T) (Finset.range n) // nS S t.1 = 0} →
      SMono (fun k => S k) (Finset.range (Fintype.card (Fin n))) := fun t =>
    ⟨liftS S t.1.1 t.2, (isShuffle_mapV _ _).1 (by rw [mapV_liftS]; exact t.1.2.1), by
      rw [← labels_mapV (fun _ m => m.1), mapV_liftS, t.1.2.2, Fintype.card_fin]⟩
  have hφ : Function.Injective φ := fun t t' h => by
    have h' := congrArg (fun T => T.1.mapV (fun _ m => m.1)) h
    simp only [φ, mapV_liftS] at h'
    exact Subtype.ext (Subtype.ext h')
  have hπb : ∀ t, (FreeGrL.mapSp (barProjGen c hc r)).app (Fin n) (barBasisN c hc n t.1)
      = FreeGrL.shuffleBasis (selBasis c hc r S hli hsp) (par_selBasis c hc r S hli hsp) (Fin n)
        (φ t) := fun t => by
    have h₁ : t.1.1.labels = (Finset.range (Fintype.card (Fin n))).val := by
      rw [t.1.2.2, Fintype.card_fin]
    have h₂ : ((liftS S t.1.1 t.2).mapV fun _ m => m.1).labels
        = (Finset.range (Fintype.card (Fin n))).val := by
      rw [mapV_liftS]
      exact h₁
    exact (congrArg ((FreeGrL.mapSp (barProjGen c hc r)).app (Fin n))
      (barBasisN_eq_shEv c hc n _ h₁)).trans ((congrArg (fun z =>
        (FreeGrL.mapSp (barProjGen c hc r)).app (Fin n)
          (GrOperad.map (R := K) (FreeGrL.posEquiv (Fin n)).symm z))
        (shEv_congr c hc (mapV_liftS S t.1.1 t.2).symm _ h₁ h₂)).trans
        ((FreeGrL.mapSp_map_shEv_mapV (genBasis c hc) (selBasis c hc r S hli hsp)
          (fun _ m => m.1) (barProjGen c hc r)
          (fun k j => (selBasis_apply c hc r S hli hsp k j).symm) _ _ h₂ (φ t).2.2).trans
          (FreeGrL.shuffleBasis_apply _ _ _ (φ t)).symm))
  have hli' : LinearIndependent K fun t : {t : SMono (VMono T) (Finset.range n) // nS S t.1 = 0}
      => (FreeGrL.mapSp (barProjGen c hc r)).app (Fin n) (barBasisN c hc n t.1) := by
    rw [show (fun t : {t : SMono (VMono T) (Finset.range n) // nS S t.1 = 0} =>
        (FreeGrL.mapSp (barProjGen c hc r)).app (Fin n) (barBasisN c hc n t.1))
      = (FreeGrL.shuffleBasis (selBasis c hc r S hli hsp) (par_selBasis c hc r S hli hsp) (Fin n))
        ∘ φ from funext hπb]
    exact (Module.Basis.linearIndependent _).comp φ hφ
  exact eq_zero_of_linearIndependent_comp _ _ hli' hx hπ

/-- **The trees labelled at one vertex by an operation of the relator ideal.** -/
def relTrees (n : ℕ) : Set (BarCoop (Ibar K E c hc) (Fin n)) :=
  {x | ∃ (t : SMono (VMono T) (Finset.range n)) (q : List ℕ) (k : ℕ) (m₀ : VMono T k)
    (ch : Fin k → STree (VMono T)) (hq : t.1.get? q = some (.node m₀ ch))
    (y : FreeGrL K E (Fin k)), y ∈ (𝒥).sub (Fin k) ∧ x = Tq c hc t hq y}

include hli hsp in
omit [IsEmpty (T 1)] in
/-- **Every tree is a combination of trees with all vertices in `S` modulo the trees labelled at one
vertex by the relator ideal**, by induction on the number of vertices outside `S`. -/
theorem barBasisN_mem_sup {n : ℕ} : ∀ (N : ℕ) (t : SMono (VMono T) (Finset.range n)),
    nS S t.1 ≤ N → barBasisN c hc n t ∈ Submodule.span K (relTrees c hc r n) ⊔
      Submodule.span K (Set.range fun t : {t : SMono (VMono T) (Finset.range n) //
        nS S t.1 = 0} => barBasisN c hc n t.1) := by
  intro N
  induction N with
  | zero =>
    intro t ht
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨⟨t, by omega⟩, rfl⟩)
  | succ N ih =>
    intro t ht
    by_cases h0 : nS S t.1 = 0
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨⟨t, h0⟩, rfl⟩)
    obtain ⟨q, k, m, ch, hq, hm⟩ := exists_get?_not_mem S t.1 h0
    let d := (selBasis c hc r S hli hsp k).repr (projGen c hc r k m)
    have hfm : projGen c hc r k m = d.sum fun j a => a • projGen c hc r k j.1 := by
      conv_lhs => rw [← (selBasis c hc r S hli hsp k).linearCombination_repr (projGen c hc r k m)]
      rw [Finsupp.linearCombination_apply]
      simp only [selBasis_apply]
      rfl
    let y : FreeGrL K E (Fin k) := tBasis c hc (Fin k) m.idx -
      d.sum fun j a => a • tBasis c hc (Fin k) (VMono.idx j.1)
    have hy : y ∈ (𝒥).sub (Fin k) := by
      let z : BarGen (Ibar K E c hc) (Fin k) := genBasis c hc k m -
        d.sum fun j a => a • genBasis c hc k j.1
      have hz : IdealSp.val _ z = y := by
        show ((idealBasis c hc k m - d.sum fun j a => a • idealBasis c hc k j.1 :
          (Ibar K E c hc).sub (Fin k)) : FreeGrL K E (Fin k)) = y
        rw [Submodule.coe_sub, idealBasis_apply, Finsupp.sum, Submodule.coe_sum]
        simp only [Submodule.coe_smul, idealBasis_apply]
        rfl
      rw [← hz, ← barProjGen_eq_zero_iff, map_sub, map_finsuppSum]
      simp only [map_smul]
      exact sub_eq_zero.2 hfm
    have hTq : Tq c hc t hq y = barBasisN c hc n t
        - d.sum fun j a => a • barBasisN c hc n (replT t hq j.1) := by
      simp only [y, map_sub, map_finsuppSum, map_smul, Tq_tBasis]
      rw [show replT t hq m = t from Subtype.ext (replace_self hq)]
    have hdecomp : barBasisN c hc n t = Tq c hc t hq y
        + d.sum fun j a => a • barBasisN c hc n (replT t hq j.1) := by
      rw [hTq, sub_add_cancel]
    rw [hdecomp]
    refine add_mem (Submodule.mem_sup_left (Submodule.subset_span
      ⟨t, q, k, m, ch, hq, y, hy, rfl⟩)) (Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (ih _ ?_))
    classical
    have := nS_replace S m j.1 ch q t.1 hq
    rw [if_neg hm, if_pos j.2] at this
    show nS S (t.1.replace q (.node j.1 ch)) ≤ N
    omega

omit hli hsp [IsEmpty (T 1)] in
/-- **The relator ideal of the bar construction is spanned by the trees labelled at one vertex by
an operation of the relator ideal.** -/
theorem krel_eq_span (n : ℕ) :
    (Krel K E c hc r).sub (Fin n) = Submodule.span K (relTrees c hc r n) := by
  have hQK : Submodule.span K (relTrees c hc r n) ≤ (Krel K E c hc r).sub (Fin n) := by
    rw [Submodule.span_le]
    rintro _ ⟨t, q, k, m₀, ch, hq, y, hy, rfl⟩
    exact Tq_mem_Krel c hc r t hq hy
  refine le_antisymm (fun (x : BarCoop (Ibar K E c hc) (Fin n)) hx => ?_) hQK
  choose S hli hsp using exists_sel c hc r
  have htop : ⊤ ≤ Submodule.span K (relTrees c hc r n) ⊔
      Submodule.span K (Set.range fun t : {t : SMono (VMono T) (Finset.range n) //
        nS S t.1 = 0} => barBasisN c hc n t.1) := by
    rw [← (barBasisN c hc n).span_eq, Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    exact barBasisN_mem_sup c hc r S hli hsp _ t le_rfl
  obtain ⟨q₁, hq₁, s₁, hs₁, hqs⟩ := Submodule.mem_sup.1 (htop Submodule.mem_top (x := x))
  have hsK : s₁ ∈ (Krel K E c hc r).sub (Fin n) := by
    have e : x - q₁ = s₁ := sub_eq_of_eq_add' hqs.symm
    exact e ▸ sub_mem hx (hQK hq₁)
  have hs0 : s₁ = 0 := eq_zero_of_mem_sel c hc r S hli hsp hs₁
    ((mem_Krel_iff c hc r (A := Fin n) s₁).1 hsK)
  rw [← hqs, hs0, add_zero]
  exact hq₁

end Kernel

end ShuffleAnySym

end Operad
