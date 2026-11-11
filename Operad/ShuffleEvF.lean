/-
# Evaluating trees along any family of operations

The evaluation `FreeGrL.shEv b` of a tree in the free graded operad `T(W)` uses only the vectors
`b k β` of the basis at the vertices. This file evaluates trees along **any family**
`v k : B k → W (Fin k)` (`FreeGrL.shEvF`), so that the vertices may carry vectors that are not
basis vectors, and a morphism of generators may be applied to the vertex labels.

* `FreeGrL.shEv_eq_shEvF`: the evaluation along a basis is the evaluation along its vectors.
* **Naturality** (`FreeGrL.mapSp_shEvF`): the morphism `mapSp f : T(V) → T(W)` extending
  `f : V → W` sends the evaluation along `v` to the evaluation along `f ∘ v`. It comes from the
  naturality of grafting (`FreeGrL.mapSp_graft_mk`), through the morphism of set operads of
  homogeneous operations with sign data induced by a morphism of graded operads
  (`GrOperadHom.sgnHom`).
* **Relabelling the vertices** (`STree.mapV`, `FreeGrL.shEvF_mapV`): evaluating a tree whose
  vertex labels are moved along `g` is evaluating the tree along `v ∘ g`.
* **Linearity in one vertex** (`FreeGrL.sum_shEvF_replace`): for a vertex at the position `q`,
  if `∑ a_i v(β_i) = 0` then `∑ a_i ev(t[q := β_i])` vanishes, `t[q := β]` the tree with the label
  of that vertex replaced by `β` (`STree.replace`).
-/
import Operad.ShuffleFreeGrL
import Operad.FreeGrDer

universe u v w x

namespace Operad

open Function Sym GerBV GrComposite STree

/-! ## Morphisms of graded operads on operations with sign data -/

namespace GrOperadHom

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]

/-- **A morphism of graded operads on homogeneous operations with sign data**, a morphism of set
operads keeping the sign data. -/
noncomputable def sgnHom (φ : GrOperadHom R P Q) : SetOperadHom (SgnOp R P) (SgnOp R Q) where
  app A _ _ p := SgnOp.mk (φ.app A p.op) p.dat (by rw [← φ.app_par, p.par_op])
  app_map e p := SgnOp.ext (φ.app_map e p.op) rfl
  app_one := SgnOp.ext φ.app_one rfl
  app_comp i p p' := SgnOp.ext (by
    show φ.app _ (σ R _ • GrOperad.comp (R := R) i p.op p'.op)
      = σ R _ • GrOperad.comp (R := R) i (φ.app _ p.op) (φ.app _ p'.op)
    rw [map_smul, φ.app_comp]
    rfl) rfl

@[simp] lemma sgnHom_op (φ : GrOperadHom R P Q) {A : Type} [Fintype A] [DecidableEq A]
    (p : SgnOp R P A) : ((sgnHom φ).app A p).op = φ.app A p.op := rfl

lemma sgnHom_cor (φ : GrOperadHom R P Q) {A : Type} [Fintype A] [DecidableEq A] (L : LinOrd A)
    (q : Bool) (y : P A) :
    (sgnHom φ).app A (SgnOp.cor (R := R) L q y) = SgnOp.cor (R := R) L q (φ.app A y) :=
  SgnOp.ext (φ.app_par q y) rfl

end GrOperadHom

/-! ## Relabelling the vertices of a tree -/

namespace STree

variable {B : ℕ → Type w} {B' : ℕ → Type x}

/-- **Relabelling the vertices** of a tree along `g`. -/
def mapV (g : ∀ k, B k → B' k) : STree B → STree B'
  | leaf a => leaf a
  | node β c => node (g _ β) fun j => mapV g (c j)

variable (g : ∀ k, B k → B' k)

@[simp] lemma mapV_leaf (a : ℕ) : (leaf a : STree B).mapV g = leaf a := rfl

lemma mapV_node {k : ℕ} (β : B k) (c : Fin k → STree B) :
    (node β c).mapV g = node (g _ β) fun j => (c j).mapV g := rfl

@[simp] lemma labels_mapV : ∀ t : STree B, (t.mapV g).labels = t.labels
  | leaf _ => rfl
  | node β c => by
    rw [mapV_node, labels_node, labels_node]
    exact Finset.sum_congr rfl fun j _ => labels_mapV (c j)

@[simp] lemma first_mapV : ∀ t : STree B, (t.mapV g).first = t.first
  | leaf _ => rfl
  | @node _ k β c => by
    rw [mapV_node]
    by_cases hk : 0 < k
    · rw [first_node _ _ hk, first_node _ _ hk, first_mapV]
    · simp only [first, dif_neg hk]

lemma isShuffle_mapV : ∀ t : STree B, (t.mapV g).IsShuffle ↔ t.IsShuffle
  | leaf _ => Iff.rfl
  | node β c => by
    rw [mapV_node, isShuffle_node, isShuffle_node]
    simp only [first_mapV, isShuffle_mapV]

end STree

namespace FreeGrL

variable {R : Type u} [CommRing R]
  {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)] [GrSpecies R W]

/-! ## Naturality of grafting -/

/-- **Grafting is natural**: the morphism extending `f` sends the grafting of a generator to the
grafting of the generator with `f` applied to the outer operation and `mapSp f` to the inner ones.
-/
theorem mapSp_graft_mk (f : GrSpeciesHom R V W) {S : Type} [Fintype S] [DecidableEq S]
    (g : GrCompGen V (FreeGrL R V) S) :
    (mapSp f).app S (graft R V S (mk R g)) = graft R W S (mk R
      ⟨g.A, g.B, g.L, f.app g.A g.m, fun a => (mapSp f).app (g.B a) (g.y a), g.e⟩) := by
  simp only [graft, total_mk, totalFun, map_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun c _ => ?_
  simp only [totalGen]
  rw [GrOperadHom.app_map]
  congr 1
  have h := congrArg SgnOp.op (May.app_total (GrOperadHom.sgnHom (mapSp f))
    (SgnOp.cor (R := R) g.L p ((ι R V).toSymSpeciesHom.app g.A g.m))
    fun a => SgnOp.cor (R := R) (ordOf (g.B a)) (c a) (g.y a))
  refine h.trans ?_
  simp only [GrOperadHom.sgnHom_cor]
  congr 3
  exact mapSp_ι f g.m

/-- The relabelling-invariant unit is kept by a morphism of graded operads. -/
lemma app_unitL (φ : GrOperadHom R (FreeGrL R V) (FreeGrL R W)) (A : Type) [Fintype A]
    [DecidableEq A] : φ.app A (unitL R V A) = unitL R W A := by
  rw [unitL, unitL, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [φ.app_map, φ.app_one]

/-! ## The evaluation along a family -/

variable {B : ℕ → Type x} (v : ∀ k, B k → W (Fin k))

/-- **The evaluation of a tree along a family of operations**: a leaf is the unit, and a vertex
labelled by `β` is the operation `v β` grafted with the evaluations of its children. -/
noncomputable def shEvF : (t : STree B) → (Y : Finset ℕ) → t.labels = Y.val → FreeGrL R W (Lab Y)
  | .leaf _, Y, _ => unitL R W (Lab Y)
  | .node β c, Y, h => graft R W (Lab Y) (mk R (ownGen (LinOrd.std _) (v _ β) (own h)
      fun j => GrOperad.map (R := R) (childEquiv h j) (shEvF (c j) (cLab c j) (labels_child h j))))

lemma shEvF_leaf (a : ℕ) (Y : Finset ℕ) (h : (STree.leaf a : STree B).labels = Y.val) :
    shEvF (R := R) v (.leaf a) Y h = unitL R W (Lab Y) := by
  rw [shEvF]

lemma shEvF_node {k : ℕ} (β : B k) (c : Fin k → STree B) (Y : Finset ℕ)
    (h : (STree.node β c).labels = Y.val) :
    shEvF (R := R) v (.node β c) Y h = graft R W (Lab Y) (mk R (ownGen (LinOrd.std _) (v _ β)
      (own h) fun j => GrOperad.map (R := R) (childEquiv h j) (shEvF v (c j) (cLab c j)
        (labels_child h j)))) := by
  rw [shEvF]

lemma shEvF_congr {t t' : STree B} (ht : t = t') (Y : Finset ℕ) (h : t.labels = Y.val)
    (h' : t'.labels = Y.val) : shEvF (R := R) v t Y h = shEvF v t' Y h' := by
  subst ht
  rfl

/-- **The evaluation along equal sets of leaves**, relabelled along the identity of the values. -/
lemma map_shEvF {t : STree B} {Y Y' : Finset ℕ} (hY : Y = Y') (h : t.labels = Y.val)
    (h' : t.labels = Y'.val) (e : Lab Y ≃ Lab Y') (he : ∀ x, (e x).1 = x.1) :
    GrOperad.map (R := R) e (shEvF v t Y h) = shEvF (R := R) v t Y' h' := by
  subst hY
  rw [show e = Equiv.refl _ from Equiv.ext fun x => Subtype.ext (he x), GrOperad.map_refl]

/-- **The evaluation along a basis is the evaluation along its vectors.** -/
theorem shEv_eq_shEvF {B : ℕ → Type x} (b : ∀ k, Module.Basis (B k) R (W (Fin k))) :
    ∀ (t : STree B) (Y : Finset ℕ) (h : t.labels = Y.val),
      shEv b t Y h = shEvF (fun k => ⇑(b k)) t Y h
  | .leaf a, Y, h => by rw [shEv_leaf, shEvF_leaf]
  | .node β c, Y, h => by
    rw [shEv_node, shEvF_node]
    congr 4
    funext j
    rw [shEv_eq_shEvF b (c j)]

/-- **The evaluation at a vertex whose children have the leaves of another family of trees**: the
owners and the leaves of the children may be taken from that family. -/
theorem shEvF_node_congr {B₀ : ℕ → Type*} {k : ℕ} (γ : B k) (c' : Fin k → STree B) (β₀ : B₀ k)
    (c : Fin k → STree B₀) (hc : ∀ j, (c' j).labels = (c j).labels) (Y : Finset ℕ)
    (h : (STree.node β₀ c).labels = Y.val) (h' : (STree.node γ c').labels = Y.val) :
    shEvF (R := R) v (.node γ c') Y h' = graft R W (Lab Y) (mk R (ownGen (LinOrd.std _) (v _ γ)
      (own h) fun j => GrOperad.map (R := R) (childEquiv h j) (shEvF v (c' j) (cLab c j)
        ((hc j).trans (labels_child h j))))) := by
  have hown : own h' = own h := funext fun s => own_eq h' (by rw [hc]; exact mem_own h s)
  rw [shEvF_node, mk_ownGen_congr _ _ hown]
  congr 4
  funext j
  have hY : cLab c' j = cLab c j := by simp only [cLab, hc]
  rw [← map_shEvF v hY (labels_child h' j) _ (Equiv.subtypeEquivRight fun x => by rw [hY])
    fun _ => rfl]
  show GrOperad.map (R := R) _ (GrOperad.map (R := R) _ _) = _
  simp only [← GrOperad.map_trans]
  apply gmap_congr
  intro x
  rfl

/-! ## Naturality -/

/-- **Naturality of the evaluation**: the morphism of free graded operads extending `f` sends the
evaluation along `v` to the evaluation along `f ∘ v`. -/
theorem mapSp_shEvF {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
    (u : ∀ k, B k → V (Fin k)) (f : GrSpeciesHom R V W) :
    ∀ (t : STree B) (Y : Finset ℕ) (h : t.labels = Y.val),
      (mapSp f).app (Lab Y) (shEvF u t Y h)
        = shEvF (fun k β => f.app (Fin k) (u k β)) t Y h
  | .leaf a, Y, h => by rw [shEvF_leaf, shEvF_leaf, app_unitL]
  | .node β c, Y, h => by
    rw [shEvF_node, shEvF_node, mapSp_graft_mk]
    congr 3
    funext j
    rw [GrOperadHom.app_map, mapSp_shEvF u f (c j)]

/-! ## Relabelling vertices, and linearity in one vertex -/

/-- **Evaluating a tree with relabelled vertices** is evaluating the tree along the composite. -/
theorem shEvF_mapV {B' : ℕ → Type*} (g : ∀ k, B' k → B k) :
    ∀ (t : STree B') (Y : Finset ℕ) (h : t.labels = Y.val) (h' : (t.mapV g).labels = Y.val),
      shEvF (R := R) v (t.mapV g) Y h' = shEvF (fun k β => v k (g k β)) t Y h
  | .leaf a, Y, h, h' => (shEvF_leaf v a Y h').trans (shEvF_leaf _ a Y h).symm
  | .node β c, Y, h, h' => by
    rw [shEvF_congr v (mapV_node g β c) Y h' h',
      shEvF_node_congr v (g _ β) (fun j => (c j).mapV g) β c (fun j => labels_mapV g (c j)) Y h h',
      shEvF_node]
    congr 4
    funext j
    rw [shEvF_mapV g (c j)]

/-- **Linearity in the label of one vertex**: for the vertex at the position `q` of `t`, with
children `ch`, if `∑ a_i v(β_i) = 0` then the evaluations of the trees with that vertex labelled
`β_i` have `∑ a_i ev(t[q := β_i]) = 0`. -/
theorem sum_shEvF_replace {ι : Type*} (s : Finset ι) (a : ι → R) {k : ℕ} (βs : ι → B k)
    (ch : Fin k → STree B) (hv : ∑ i ∈ s, a i • v k (βs i) = 0) :
    ∀ (q : List ℕ) (t : STree B) (β₀ : B k), t.get? q = some (.node β₀ ch) → ∀ (Y : Finset ℕ)
      (h : ∀ i, (t.replace q (.node (βs i) ch)).labels = Y.val),
      ∑ i ∈ s, a i • shEvF (R := R) v (t.replace q (.node (βs i) ch)) Y (h i) = 0
  | [], t, β₀, ht, Y, h => by
    rw [get?_nil, Option.some_inj] at ht
    subst ht
    rcases s.eq_empty_or_nonempty with hs | ⟨i₀, -⟩
    · rw [hs, Finset.sum_empty]
    have h₀ : (STree.node β₀ ch).labels = Y.val := h i₀
    let g : GrCompGen W (FreeGrL R W) (Lab Y) := ownGen (LinOrd.std _) (0 : W (Fin k)) (own h₀)
      fun j => GrOperad.map (R := R) (childEquiv h₀ j) (shEvF v (ch j) (cLab ch j)
        (labels_child h₀ j))
    have hterm : ∀ i, shEvF (R := R) v ((STree.node β₀ ch).replace [] (.node (βs i) ch)) Y (h i)
        = graft R W (Lab Y) (mkM g (v k (βs i))) := fun i => by
      rw [mkM_apply]
      exact shEvF_node v (βs i) ch Y (h i)
    simp only [hterm, ← map_smul, ← map_sum, hv, map_zero]
  | _ :: _, .leaf _, _, ht, _, _ => by simp at ht
  | j :: q', .node (k := k') γ c, β₀, ht, Y, h => by
    obtain ⟨hj, hc⟩ := get?_node_cons_eq_some.1 ht
    rcases s.eq_empty_or_nonempty with hs | ⟨i₀, -⟩
    · rw [hs, Finset.sum_empty]
    let jj : Fin k' := ⟨j, hj⟩
    let ci : ι → Fin k' → STree B := fun i l =>
      if (l : ℕ) = j then (c l).replace q' (.node (βs i) ch) else c l
    have hci : ∀ i l, (ci i l).labels = (c l).labels := fun i l => by
      simp only [ci]
      split_ifs with hl
      · have hl' : l = jj := Fin.ext hl
        subst hl'
        exact labels_replace_of_eq (v := .node (βs i) ch) hc rfl
      · rfl
    have h₀ : (STree.node γ c).labels = Y.val := by
      rw [← h i₀, replace_node_cons, labels_node, labels_node]
      exact Finset.sum_congr rfl fun l _ => (hci i₀ l).symm
    let ys₀ : ∀ l, FreeGrL R W (Fib (own h₀) l) := fun l =>
      GrOperad.map (R := R) (childEquiv h₀ l) (shEvF v (c l) (cLab c l) (labels_child h₀ l))
    let g : GrCompGen W (FreeGrL R W) (Lab Y) := ownGen (LinOrd.std _) (v _ γ) (own h₀) ys₀
    let Ψ : FreeGrL R W (Lab (cLab c jj)) →ₗ[R] FreeGrL R W (Lab Y) :=
      (graft R W (Lab Y)).comp (((mkY g).toLinearMap ys₀ jj).comp
        (GrOperad.map (R := R) (childEquiv h₀ jj)))
    have hjl : ∀ i, ((c jj).replace q' (.node (βs i) ch)).labels = (cLab c jj).val := fun i =>
      (labels_replace_of_eq (v := .node (βs i) ch) hc rfl).trans (labels_child h₀ jj)
    have hterm : ∀ i, shEvF (R := R) v ((STree.node γ c).replace (j :: q') (.node (βs i) ch)) Y
        (h i) = Ψ (shEvF v ((c jj).replace q' (.node (βs i) ch)) (cLab c jj) (hjl i)) := by
      intro i
      rw [shEvF_congr v (replace_node_cons γ c j q' _) Y (h i) (by rw [← h i]; rfl),
        shEvF_node_congr v γ (ci i) γ c (hci i) Y h₀]
      show _ = graft R W (Lab Y) (mk R { g with y := update ys₀ jj _ })
      congr 4
      funext l
      by_cases hl : l = jj
      · subst hl
        rw [update_self]
        congr 1
        exact shEvF_congr v (if_pos rfl) _ _ _
      · rw [update_of_ne hl]
        congr 1
        exact shEvF_congr v (if_neg fun h' => hl (Fin.ext h')) _ _ _
    simp only [hterm, ← map_smul, ← map_sum]
    rw [sum_shEvF_replace s a βs ch hv q' (c jj) β₀ hc (cLab c jj) hjl, map_zero]

/-- **The morphism extending `f` on a combination of relabelled evaluations of trees differing in
the label of one vertex** vanishes when the combination of the images of the labels does. -/
theorem mapSp_sum_shEv_replace {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
    (b : ∀ k, Module.Basis (B k) R (V (Fin k))) (f : GrSpeciesHom R V W) {ι : Type*}
    (s : Finset ι) (a : ι → R) {k : ℕ} (βs : ι → B k) (ch : Fin k → STree B)
    (hv : ∑ i ∈ s, a i • f.app (Fin k) (b k (βs i)) = 0) (q : List ℕ) (t : STree B) (β₀ : B k)
    (hq : t.get? q = some (.node β₀ ch)) {Y : Finset ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (e : Lab Y ≃ A) (h : ∀ i, (t.replace q (.node (βs i) ch)).labels = Y.val) :
    (mapSp f).app A (∑ i ∈ s, a i • GrOperad.map (R := R) e
      (shEv b (t.replace q (.node (βs i) ch)) Y (h i))) = 0 := by
  simp only [map_sum, map_smul, GrOperadHom.app_map, shEv_eq_shEvF, mapSp_shEvF]
  rw [← map_zero (GrOperad.map (R := R) (P := FreeGrL R W) e),
    ← sum_shEvF_replace (fun k β => f.app (Fin k) (b k β)) s a βs ch hv q t β₀ hq Y h]
  simp only [map_sum, map_smul]

end FreeGrL

end Operad
