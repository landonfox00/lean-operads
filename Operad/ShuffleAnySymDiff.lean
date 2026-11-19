/-
# The bar differential on the trees with at most two vertices, for generators of any arity

Step (2b) of the symmetric–shuffle bridge for generators of any arity, second part; the binary
case is `Operad.ShuffleBarSymDiff`. Setting and notation as in `Operad.ShuffleAnySym`.

* **Composing basis vectors** of `T(E)`: the composite of two relabelled basis vectors is the
  evaluation of the merged monomial `ShuffleAnySym.mergeMono`, without sign, the generators being
  even (`ShuffleAnySym.comp_tBasis`).
* **The bar differential of a tree with two vertices** is the corolla of its merged monomial
  (`ShuffleAnySym.d_shEv_two`, `ShuffleAnySym.d_barBasisN_two`), a monomial on the leaves of the
  tree (`ShuffleAnySym.twoMono_mem`); on bar trees, merging the cut edge
  (`ShuffleAnySym.setF_toBar_two`, the only one: `ShuffleAnySym.cutKeys_toBar_two`).
* Hence **`ΦL ∘ Bar.d = STree.Bar.d ∘ ΦL` on the trees with one or two vertices**
  (`ShuffleAnySym.ΦL_d_of_mem_deg`).
-/
import Operad.ShuffleAnySym
import Operad.ShuffleBarSymDiff

universe u

namespace Operad

open Function Sym GerBV GrComposite STree FreeGr Bar

namespace ShuffleAnySym

open ShuffleBarSym

section CompT

variable {K : Type u} [CommRing K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {T : ℕ → Type} [IsEmpty (T 0)]
  (c : ∀ k, Module.Basis (T k) K (E (Fin k)))
  (hc : ∀ k (β : T k), GrSpecies.par (R := K) false (c k β) = c k β)

/-- **The merged monomial**: the monomial `m₂`, its leaves relabelled by `f₂`, grafted on the leaf
`q` of the monomial `m₁`, the other leaves of `m₁` relabelled by `f₁`. -/
def mergeMono (m₁ : STree T) (q : ℕ) (m₂ : STree T) (f₁ f₂ : ℕ → ℕ) : STree T :=
  m₁.subst fun a => if a = q then m₂.subst (fun i => .leaf (f₂ i)) else .leaf (f₁ a)

lemma tBasis_apply (A : Type) [Fintype A] [LinearOrder A]
    (t : SMono T (Finset.range (Fintype.card A))) :
    tBasis c hc A t = FreeGrL.shuffleBasis c (p := fun _ _ => false) hc A t := rfl

omit [IsEmpty (T 0)] in
lemma labels_relabel_mono {k : ℕ} (m : SMono T (Finset.range (Fintype.card (Fin k))))
    {Y : Finset ℕ} (θ : Fin k ≃ Lab Y) (f : ℕ → ℕ) (hf : ∀ j : Fin k, (θ j).1 = f j) :
    (m.1.relabel f).labels = Y.val := by
  rw [STree.labels_relabel, m.2.2]
  exact val_map_of_equiv ((FreeGrL.posEquiv (Fin k)).symm.trans θ) fun x => by
    rw [Equiv.trans_apply, hf, val_symm_posEquiv]

/-- **A relabelled basis vector** of the free graded operad is the evaluation of the relabelled
tree. -/
lemma map_tBasis {k : ℕ} (m : SMono T (Finset.range (Fintype.card (Fin k))))
    {Y : Finset ℕ} (θ : Fin k ≃ Lab Y) (f : ℕ → ℕ) (hf : ∀ j : Fin k, (θ j).1 = f j)
    (h : (m.1.relabel f).labels = Y.val) :
    GrOperad.map (R := K) θ (tBasis c hc (Fin k) m) = FreeGrL.shEv c (m.1.relabel f) Y h := by
  rw [tBasis_apply, FreeGrL.shuffleBasis_apply, ← GrOperad.map_trans]
  refine (FreeGrL.shEv_relabel c f _ _ _ Y h _ fun x => ?_).symm
  rw [Equiv.trans_apply, hf, val_symm_posEquiv]

/-- **Composing two basis vectors** of the free graded operad on even generators, relabelled
along bijections with finite sets: the evaluation of the merged monomial, without sign. -/
theorem comp_tBasis {k l : ℕ} (m₁ : SMono T (Finset.range (Fintype.card (Fin k))))
    (m₂ : SMono T (Finset.range (Fintype.card (Fin l)))) {Y₁ Y₂ Y : Finset ℕ}
    (θ₁ : Fin k ≃ Lab Y₁) (θ₂ : Fin l ≃ Lab Y₂) (f₁ f₂ : ℕ → ℕ)
    (hf₁ : ∀ j : Fin k, (θ₁ j).1 = f₁ j) (hf₂ : ∀ i : Fin l, (θ₂ i).1 = f₂ i) (q : Fin k)
    (hY : (mergeMono m₁.1 q m₂.1 f₁ f₂).labels = Y.val)
    (E' : Lab Y ≃ Without (Lab Y₁) (θ₁ q) ⊕ Lab Y₂) (hE : ∀ x, FreeGrL.sval (E' x) = x.1) :
    GrOperad.comp (R := K) (θ₁ q) (GrOperad.map (R := K) θ₁ (tBasis c hc (Fin k) m₁))
        (GrOperad.map (R := K) θ₂ (tBasis c hc (Fin l) m₂))
      = GrOperad.map (R := K) E' (FreeGrL.shEv c (mergeMono m₁.1 q m₂.1 f₁ f₂) Y hY) := by
  have h₁ := labels_relabel_mono m₁ θ₁ f₁ hf₁
  have h₂ := labels_relabel_mono m₂ θ₂ f₂ hf₂
  rw [map_tBasis c hc m₁ θ₁ f₁ hf₁ h₁, map_tBasis c hc m₂ θ₂ f₂ hf₂ h₂]
  have hlt : ∀ a ∈ m₁.1.labels, a < k := fun a ha => by
    rw [m₁.2.2, Finset.mem_val, Finset.mem_range, Fintype.card_fin] at ha
    exact ha
  have hsub : (m₁.1.relabel f₁).subst
      (Function.update STree.leaf (θ₁ q).1 (m₂.1.relabel f₂))
        = mergeMono m₁.1 q m₂.1 f₁ f₂ := by
    rw [mergeMono, STree.relabel, STree.subst_subst]
    refine STree.subst_congr _ fun a ha => ?_
    rw [STree.subst_leaf']
    by_cases haq : a = q
    · rw [if_pos haq, haq, ← hf₁ q, Function.update_self]
      rfl
    · rw [if_neg haq]
      have hne : f₁ a ≠ (θ₁ q).1 := fun h' => by
        have h'' : θ₁ ⟨a, hlt a ha⟩ = θ₁ q := Subtype.ext (by rw [hf₁]; exact h')
        exact haq (congrArg Fin.val (θ₁.injective h''))
      rw [Function.update_of_ne hne]
  have hY' : ((m₁.1.relabel f₁).subst
      (Function.update STree.leaf (θ₁ q).1 (m₂.1.relabel f₂))).labels = Y.val := by
    rw [hsub]
    exact hY
  have := FreeGrL.comp_shEv c (p := fun _ _ => false) hc (m₂.1.relabel f₂) Y₂ h₂
    (m₁.1.relabel f₁) Y₁ h₁ (θ₁ q).1 (θ₁ q).2 Y hY' E' hE
  rw [vpar_false, Bool.false_and, σ_false, one_smul] at this
  rw [this, ← FreeGrL.map_shEv c hsub rfl hY' hY (Equiv.refl _) fun _ => rfl, GrOperad.map_refl]

end CompT

section Two

open STree

variable {K : Type u} [CommRing K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {T : ℕ → Type} [IsEmpty (T 0)]
  (c : ∀ k, Module.Basis (T k) K (E (Fin k)))
  (hc : ∀ k (β : T k), GrSpecies.par (R := K) false (c k β) = c k β)

/-- A decoration, as an index of `tBasis`. -/
def VMono.idx {k : ℕ} (m : VMono T k) : SMono T (Finset.range (Fintype.card (Fin k))) :=
  ⟨m.1.1, m.1.2.1, by simpa using m.1.2.2⟩

/-- **The merged monomial of a tree with two vertices**: the monomial of the child `j₀` grafted on
the leaf `j₀` of the monomial of the root, all leaves named by the leaves of the tree. -/
def twoMono {k l : ℕ} (m₁ : VMono T k) (ch : Fin k → STree (VMono T)) (j₀ : Fin k)
    (m₂ : VMono T l) (c₂ : Fin l → STree (VMono T)) : STree T :=
  mergeMono m₁.1.1 j₀ m₂.1.1 (firstFn ch) (firstFn c₂)

/-- The merge step of `d_shEv_two`, for a composite of two relabelled generators at a variable
input. -/
lemma d_eq_of_comp_two {k l N : ℕ} {Y₁ Y₂ : Finset ℕ} (m₁ : VMono T k) (m₂ : VMono T l)
    (θ₁ : Fin k ≃ Lab Y₁) (θ₂ : Fin l ≃ Lab Y₂) (j₀ : Fin k) (i : Lab Y₁) (hq : θ₁ j₀ = i)
    (f₁ f₂ : ℕ → ℕ) (hf₁ : ∀ j : Fin k, (θ₁ j).1 = f₁ j) (hf₂ : ∀ i : Fin l, (θ₂ i).1 = f₂ i)
    (hN : N + 1 = k + l)
    (hM : (mergeMono m₁.1.1 j₀ m₂.1.1 f₁ f₂).IsShuffle ∧
      (mergeMono m₁.1.1 j₀ m₂.1.1 f₁ f₂).labels = (Finset.range N).val) (hN2 : 2 ≤ N)
    (X : FreeGrL K (BarGen (Ibar K E c hc)) (Lab (Finset.range (Fintype.card (Fin N)))))
    (E' : Lab (Finset.range (Fintype.card (Fin N))) ≃ Without (Lab Y₁) i ⊕ Lab Y₂)
    (hE : ∀ x, FreeGrL.sval (E' x) = x.1)
    (hcomp : GrOperad.comp (R := K) i
        (GrOperad.map (R := K) θ₁ ((FreeGrL.ι K (BarGen (Ibar K E c hc))).app (Fin k)
          (genBasis c hc k m₁)))
        (GrOperad.map (R := K) θ₂ ((FreeGrL.ι K (BarGen (Ibar K E c hc))).app (Fin l)
          (genBasis c hc l m₂)))
      = GrOperad.map (R := K) E' X) :
    Bar.d (Ibar K E c hc) _ X = GrOperad.map (R := K) (FreeGrL.posEquiv (Fin N))
      ((FreeGrL.ι K (BarGen (Ibar K E c hc))).app (Fin N)
        (genBasis c hc N ⟨⟨_, hM⟩, hN2⟩)) := by
  subst hq
  have hA := Bar.d_map_ι (Ibar K E c hc) θ₁ (genBasis c hc k m₁)
  have hA' := Bar.d_map_ι (Ibar K E c hc) θ₂ (genBasis c hc l m₂)
  have hd := Bar.d_comp (Ibar K E c hc) (θ₁ j₀)
    (GrOperad.map (R := K) θ₁ ((FreeGrL.ι K (BarGen (Ibar K E c hc))).app (Fin k)
      (genBasis c hc k m₁)))
    (GrOperad.map (R := K) θ₂ ((FreeGrL.ι K (BarGen (Ibar K E c hc))).app (Fin l)
      (genBasis c hc l m₂)))
  have hdm := Bar.d_map (I := Ibar K E c hc) E' X
  have hmc := Bar.mc_map_ι _ θ₁ θ₂ j₀ (genBasis c hc k m₁) (genBasis c hc l m₂)
    (par_genBasis c hc k m₁) (par_genBasis c hc l m₂) N hN
  simp only [hcomp, hdm, hA, hA', hmc, map_zero, LinearMap.zero_apply, zero_add] at hd
  have hY : (mergeMono m₁.1.1 j₀ m₂.1.1 f₁ f₂).labels
      = (Finset.range (Fintype.card (Fin N))).val := by
    rw [Fintype.card_fin]
    exact hM.2
  have hB := comp_tBasis c hc m₁.idx m₂.idx θ₁ θ₂ f₁ f₂ hf₁ hf₂ j₀ hY E' hE
  have hmerge : Bar.msVal (Ibar K E c hc) true (genBasis c hc k m₁) j₀ (genBasis c hc l m₂) N hN
      = SymSpecies.map (R := K) ((FreeGrL.posEquiv (Fin N)).trans (E'.trans
          ((compEquiv θ₁ θ₂ j₀).symm.trans (posEquivF j₀ l N hN))))
        (genBasis c hc N ⟨⟨_, hM⟩, hN2⟩) := by
    refine IdealSp.ext _ ?_
    rw [Bar.val_msVal]
    show _ = GrOperad.map (R := K) _ (idealBasis c hc N ⟨⟨_, hM⟩, hN2⟩ : FreeGrL K E (Fin N))
    rw [Bool.not_true, σ_false, one_smul]
    show GrOperad.map (R := K) _ (GrOperad.comp (R := K) j₀
      (idealBasis c hc k m₁ : FreeGrL K E (Fin k)) (idealBasis c hc l m₂ : FreeGrL K E (Fin l)))
      = _
    rw [idealBasis_apply, idealBasis_apply, idealBasis_apply, tBasis_apply c hc (Fin N),
      FreeGrL.shuffleBasis_apply]
    have hc' := GrOperad.map_comp (R := K) (P := FreeGrL K E) θ₁ θ₂ j₀
      (tBasis c hc (Fin k) m₁.idx) (tBasis c hc (Fin l) m₂.idx)
    rw [hB] at hc'
    have hc'' := congrArg (GrOperad.map (R := K) (compEquiv θ₁ θ₂ j₀).symm) hc'
    rw [← GrOperad.map_trans, Equiv.self_trans_symm, GrOperad.map_refl] at hc''
    show GrOperad.map (R := K) _ (GrOperad.comp (R := K) j₀ (tBasis c hc (Fin k) m₁.idx)
      (tBasis c hc (Fin l) m₂.idx)) = _
    rw [hc'', ← GrOperad.map_trans, ← GrOperad.map_trans, ← GrOperad.map_trans]
    apply gmap_congr
    intro x
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  have happ := (FreeGrL.ι K (BarGen (Ibar K E c hc))).app_map ((FreeGrL.posEquiv (Fin N)).trans
    (E'.trans ((compEquiv θ₁ θ₂ j₀).symm.trans (posEquivF j₀ l N hN))))
    (genBasis c hc N ⟨⟨_, hM⟩, hN2⟩)
  simp only [hmerge, happ] at hd
  have hd' := congrArg (GrOperad.map (R := K) E'.symm) hd
  simp only [GrOperad.toGrSpecies_map, ← GrOperad.map_trans, Equiv.self_trans_symm,
    GrOperad.map_refl] at hd'
  refine hd'.trans (gmap_congr (fun x => ?_) _)
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- **The bar differential of a tree with two vertices**: the evaluation of the corolla of the
merged monomial, without sign. -/
theorem d_shEv_two {k l N : ℕ} (m₁ : VMono T k) (ch : Fin k → STree (VMono T)) (j₀ : Fin k)
    (m₂ : VMono T l) (c₂ : Fin l → STree (VMono T)) (hj₀ : ch j₀ = .node m₂ c₂)
    (hl₁ : ∀ j, j ≠ j₀ → ∃ a, ch j = .leaf a) (hl₂ : ∀ i, ∃ a, c₂ i = .leaf a)
    (ht : (STree.node m₁ ch).IsShuffle)
    (h : (STree.node m₁ ch).labels = (Finset.range (Fintype.card (Fin N))).val)
    (hM : (twoMono m₁ ch j₀ m₂ c₂).IsShuffle ∧
      (twoMono m₁ ch j₀ m₂ c₂).labels = (Finset.range N).val) (hN2 : 2 ≤ N)
    (h' : (STree.node (⟨⟨_, hM⟩, hN2⟩ : VMono T N) fun j : Fin N => .leaf j.1).labels
      = (Finset.range (Fintype.card (Fin N))).val) :
    Bar.d (Ibar K E c hc) _ (FreeGrL.shEv (genBasis c hc) (.node m₁ ch) _ h)
      = FreeGrL.shEv (genBasis c hc)
          (.node (⟨⟨_, hM⟩, hN2⟩ : VMono T N) fun j : Fin N => .leaf j.1) _ h' := by
  obtain ⟨Y₁, Y₂, h₁, h₂, hm, E', hE, hcomp⟩ :=
    FreeGrL.shEv_split (genBasis c hc) (par_genBasis c hc) m₁ ch ht _ h j₀
  have hall₁ : ∀ j, ∃ a, Function.update ch j₀ (.leaf (ch j₀).first) j = .leaf a := fun j => by
    by_cases hj : j = j₀
    · subst hj
      exact ⟨_, Function.update_self _ _ _⟩
    · rw [Function.update_of_ne hj]
      exact hl₁ j hj
  have hv : STree.vaft (fun _ _ => true) (STree.node m₁ (Function.update ch j₀
      (.leaf (ch j₀).first))) (ch j₀).first = false := STree.vaft_corolla _ _ _ hall₁ _
  simp only [hv, Bool.and_false, σ_false, one_smul] at hcomp
  obtain ⟨θ₁, hθ₁, hev₁⟩ := FreeGrL.exists_shEv_corolla (genBasis c hc) m₁ _ Y₁ h₁ hall₁
  have h₂' : (STree.node m₂ c₂).labels = Y₂.val := hj₀ ▸ h₂
  obtain ⟨θ₂, hθ₂, hev₂⟩ := FreeGrL.exists_shEv_corolla (genBasis c hc) m₂ c₂ Y₂ h₂' hl₂
  have hev₂' : FreeGrL.shEv (genBasis c hc) (ch j₀) Y₂ h₂
      = FreeGrL.shEv (genBasis c hc) (.node m₂ c₂) Y₂ h₂' := by
    have := FreeGrL.map_shEv (genBasis c hc) hj₀ rfl h₂ h₂' (Equiv.refl _) fun _ => rfl
    rwa [GrOperad.map_refl] at this
  replace hcomp := (congrArg₂ (fun x y => GrOperad.comp (R := K) (⟨(ch j₀).first, hm⟩ : Lab Y₁) x y)
    hev₁ (hev₂'.trans hev₂)).symm.trans hcomp
  have hq : θ₁ j₀ = ⟨(ch j₀).first, hm⟩ := Subtype.ext (by
    have := hθ₁ j₀
    rw [Function.update_self] at this
    exact (STree.leaf.inj this).symm)
  have hf₁ : ∀ j : Fin k, (θ₁ j).1 = firstFn ch j := fun j => by
    rw [firstFn_fin]
    by_cases hj : j = j₀
    · subst hj
      rw [hq]
    · have := hθ₁ j
      rw [Function.update_of_ne hj] at this
      rw [this]
      rfl
  have hf₂ : ∀ i : Fin l, (θ₂ i).1 = firstFn c₂ i := fun i => by
    rw [firstFn_fin, hθ₂ i]
    rfl
  have hN : N + 1 = k + l := by
    have h1 := Fintype.card_congr E'
    rw [Fintype.card_sum, Reg.card_without, ← Fintype.card_congr θ₁,
      ← Fintype.card_congr θ₂] at h1
    simp only [Fintype.card_coe, Finset.card_range, Fintype.card_fin] at h1
    have := j₀.pos
    omega
  refine (d_eq_of_comp_two c hc m₁ m₂ θ₁ θ₂ j₀ _ hq (firstFn ch) (firstFn c₂) hf₁ hf₂ hN hM hN2 _
    E' hE hcomp).trans ?_
  have hπ : (fun j : Fin N => STree.leaf (FreeGrL.posEquiv (Fin N) j).1)
      = fun j : Fin N => (STree.leaf j.1 : STree (VMono T)) :=
    funext fun j => by rw [FreeGrL.posEquiv_apply, opos_fin]
  have h'' : (STree.node (E := VMono T) (k := N) ⟨⟨_, hM⟩, hN2⟩
      fun j : Fin N => STree.leaf (FreeGrL.posEquiv (Fin N) j).1).labels
        = (Finset.range (Fintype.card (Fin N))).val := by rw [hπ]; exact h'
  have e1 := FreeGrL.shEv_corolla (genBasis c hc) (⟨⟨_, hM⟩, hN2⟩ : VMono T N) _
    (FreeGrL.posEquiv (Fin N)) h''
  have e2 := FreeGrL.map_shEv (genBasis c hc) (congrArg (STree.node _) hπ) rfl h'' h'
    (Equiv.refl _) fun _ => rfl
  exact e1.symm.trans ((GrOperad.map_refl _).symm.trans e2)

end Two

/-! ## The bar trees of the trees with two vertices -/

lemma wsign_eq_one_of_weight_le_two (K : Type u) [CommRing K] {T : ℕ → Type}
    (t : STree (VMono T)) (h : t.weight ≤ 2) : wsign K t = 1 := by
  rw [wsign, inv_eq_zero_of_length_le_one, pow_zero]
  rw [List.length_tail, length_wKeys]
  omega

section TwoTrees

open STree

variable {T : ℕ → Type}

lemma toBar_corolla {n : ℕ} (M : VMono T n) :
    toBar (STree.node M fun j : Fin n => .leaf j.1) = fl false M.1.1 := by
  rw [toBar_node]
  conv_rhs => rw [← subst_leaf (fl false M.1.1)]
  refine subst_congr _ fun a _ => ?_
  unfold kids
  split_ifs <;> rfl

section Shape

variable {k l : ℕ} (m₁ : VMono T k) (ch : Fin k → STree (VMono T)) (j₀ : Fin k) (m₂ : VMono T l)
  (c₂ : Fin l → STree (VMono T))

lemma kids_of_leaf {a : ℕ} (ha : a < k) {x : ℕ} (hx : ch ⟨a, ha⟩ = .leaf x) :
    kids ch a = STree.leaf x := by
  rw [kids_of_lt ch ha, hx]
  rfl

lemma firstFn_of_leaf {a : ℕ} (ha : a < k) {x : ℕ} (hx : ch ⟨a, ha⟩ = .leaf x) :
    firstFn ch a = x := by
  rw [firstFn, dif_pos ha, hx]
  rfl

/-- **The key of the cut edge of a tree with two vertices**: the key of the child. -/
def twoKey : ℕ ×ₗ ℕ := STree.key (kids ch j₀)

variable {m₁ ch j₀ m₂ c₂}

lemma kids_child_two (hj₀ : ch j₀ = .node m₂ c₂) (hl₂ : ∀ i, ∃ a, c₂ i = .leaf a) :
    kids ch j₀ = (fl true m₂.1.1).subst fun i => STree.leaf (firstFn c₂ i) := by
  obtain ⟨l', e₂, g₂, h₂⟩ := m₂.exists_node
  rw [kids_fin, hj₀, toBar_node, h₂]
  show (fl true (STree.node e₂ g₂)).subst (kids c₂) = _
  rw [← h₂]
  refine subst_congr _ fun a ha => ?_
  rw [labels_fl] at ha
  have hal := m₂.lt ha
  obtain ⟨x, hx⟩ := hl₂ ⟨a, hal⟩
  rw [kids_of_leaf c₂ hal hx, firstFn_of_leaf c₂ hal hx]

/-- **Merging the cut edge of a tree with two vertices** gives the bar tree of the corolla of the
merged monomial. -/
theorem setF_toBar_two (hj₀ : ch j₀ = .node m₂ c₂) (hl₁ : ∀ j, j ≠ j₀ → ∃ a, ch j = .leaf a)
    (hl₂ : ∀ i, ∃ a, c₂ i = .leaf a) :
    setF (twoKey ch j₀) false (toBar (STree.node m₁ ch)) = fl false (twoMono m₁ ch j₀ m₂ c₂) := by
  rw [toBar_node, setF_false_fl_subst, ite_self, twoMono, mergeMono, fl_false, fl_false,
    allF_subst]
  refine subst_congr _ fun a ha => ?_
  rw [labels_allF] at ha
  have hak := m₁.lt ha
  by_cases ha0 : a = j₀
  · subst ha0
    rw [if_pos rfl, kids_child_two hj₀ hl₂, setF_false_fl_subst,
      if_pos (by rw [twoKey, kids_child_two hj₀ hl₂]), fl_false, allF_subst]
    rfl
  · rw [if_neg ha0]
    have hne : (⟨a, hak⟩ : Fin k) ≠ j₀ := fun h' => ha0 (by rw [← h'])
    obtain ⟨x, hx⟩ := hl₁ _ hne
    rw [kids_of_leaf ch hak hx, firstFn_of_leaf ch hak hx]
    rfl

/-- **A tree with two vertices has one cut edge.** -/
theorem cutKeys_toBar_two (hj₀ : ch j₀ = .node m₂ c₂) (hl₂ : ∀ i, ∃ a, c₂ i = .leaf a)
    (hs : (STree.node m₁ ch).IsShuffle) (hnd : (STree.node m₁ ch).labels.Nodup)
    (hw : (STree.node m₁ ch).weight = 2) :
    cutKeys (toBar (STree.node m₁ ch)) = {twoKey ch j₀} := by
  have hcd := card_cutKeys_toBar m₁ ch hs hnd
  rw [hw] at hcd
  obtain ⟨κ, hκ⟩ := Finset.card_eq_one.1
    (show (cutKeys (toBar (STree.node m₁ ch))).card = 1 by omega)
  rw [hκ, Finset.singleton_inj]
  have hmem : twoKey ch j₀ ∈ cutKeys (toBar (STree.node m₁ ch)) := by
    rw [cutKeys_toBar_node]
    refine Finset.mem_biUnion.2 ⟨j₀, Finset.mem_range.2 j₀.2, ?_⟩
    obtain ⟨l', e₂, g₂, h₂⟩ := m₂.exists_node
    rw [twoKey, kids_child_two hj₀ hl₂, h₂, mem_cutKeys_fl_subst]
    exact Or.inl ⟨rfl, rfl⟩
  rw [hκ] at hmem
  exact (Finset.mem_singleton.1 hmem).symm

lemma strictMonoOn_firstFn {k' : ℕ} (m : VMono T k') {c : Fin k' → STree (VMono T)}
    (hmono : StrictMono fun j => (c j).first) :
    StrictMonoOn (firstFn c) {a | a ∈ m.1.1.labels} := by
  intro a ha b hb hab
  rw [firstFn, dif_pos (m.lt ha), firstFn, dif_pos (m.lt hb)]
  exact hmono (show (⟨a, m.lt ha⟩ : Fin k') < ⟨b, m.lt hb⟩ from hab)

/-- **The merged monomial of a tree with two vertices is a monomial** on the leaves of the tree. -/
theorem twoMono_mem (hj₀ : ch j₀ = .node m₂ c₂) (hl₁ : ∀ j, j ≠ j₀ → ∃ a, ch j = .leaf a)
    (hl₂ : ∀ i, ∃ a, c₂ i = .leaf a) {n : ℕ} (ht : (STree.node m₁ ch).IsShuffle)
    (hlab : (STree.node m₁ ch).labels = (Finset.range n).val) :
    ((twoMono m₁ ch j₀ m₂ c₂).IsShuffle ∧
      (twoMono m₁ ch j₀ m₂ c₂).labels = (Finset.range n).val) ∧ 2 ≤ n := by
  have ht₂ : (STree.node m₂ c₂).IsShuffle := hj₀ ▸ ht.2.1 j₀
  have hs₂ : StrictMonoOn (fun i => (STree.leaf (firstFn c₂ i) : STree T).first)
      {a | a ∈ m₂.1.1.labels} := strictMonoOn_firstFn m₂ ht₂.2.2
  have hmin : ∀ a ∈ m₁.1.1.labels, (if a = (j₀ : ℕ) then
      m₂.1.1.subst (fun i => STree.leaf (firstFn c₂ i)) else STree.leaf (firstFn ch a)).first
        = firstFn ch a := fun a _ => by
    by_cases ha0 : a = j₀
    · subst ha0
      rw [if_pos rfl, first_subst m₂.isShuffle, m₂.first, firstFn_fin, hj₀,
        first_node _ _ ht₂.1]
      show firstFn c₂ 0 = _
      exact dif_pos ht₂.1
    · rw [if_neg ha0]
      rfl
  have hshuf : (twoMono m₁ ch j₀ m₂ c₂).IsShuffle := by
    unfold twoMono mergeMono
    refine isShuffle_subst m₁.isShuffle (fun a _ => ?_) fun a ha b hb hab => ?_
    · split_ifs
      · exact isShuffle_subst m₂.isShuffle (fun _ _ => trivial) hs₂
      · trivial
    · beta_reduce
      rw [hmin a ha, hmin b hb]
      exact strictMonoOn_firstFn m₁ ht.2.2 ha hb hab
  have hlabs : (twoMono m₁ ch j₀ m₂ c₂).labels = (STree.node m₁ ch).labels := by
    rw [twoMono, mergeMono, labels_subst, bind_kids m₁, labels_node]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = j₀
    · rw [hj, if_pos rfl, labels_subst, bind_kids m₂, hj₀, labels_node]
      refine Finset.sum_congr rfl fun i _ => ?_
      obtain ⟨x, hx⟩ := hl₂ i
      rw [firstFn_fin, hx]
      rfl
    · rw [if_neg (fun h' => hj (Fin.ext h'))]
      obtain ⟨x, hx⟩ := hl₁ j hj
      rw [firstFn_fin, hx]
      rfl
  refine ⟨⟨hshuf, hlabs.trans hlab⟩, ?_⟩
  have hcd := congrArg Multiset.card hlab
  rw [labels_node, Multiset.card_sum, Finset.range_val, Multiset.card_range] at hcd
  have hk : ∑ _j : Fin k, 1 ≤ ∑ j, Multiset.card (ch j).labels :=
    Finset.sum_le_sum fun j _ => Multiset.card_pos.2 (labels_ne_zero _ (ht.2.1 j))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hk
  have := m₁.2
  omega

end Shape

end TwoTrees

/-! ## `Φ` and the differentials in vertex degrees one and two -/

section PhiTwo

open STree

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {T : ℕ → Type} [IsEmpty (T 0)] [IsEmpty (T 1)]
  (c : ∀ k, Module.Basis (T k) K (E (Fin k)))
  (hc : ∀ k (β : T k), GrSpecies.par (R := K) false (c k β) = c k β)

omit [IsEmpty (T 0)] [IsEmpty (T 1)] in
lemma labels_corolla {n : ℕ} (M : VMono T n) :
    (STree.node M fun j : Fin n => STree.leaf j.1).labels = (Finset.range n).val := by
  rw [labels_node]
  simp only [STree.labels_leaf]
  rw [Fin.sum_univ_eq_sum_range (fun i => ({i} : Multiset ℕ)) n, Finset.sum_eq_multiset_sum,
    Multiset.sum_map_singleton]

omit [IsEmpty (T 0)] [IsEmpty (T 1)] in
lemma isShuffle_corolla {n : ℕ} (M : VMono T n) :
    (STree.node M fun j : Fin n => STree.leaf j.1).IsShuffle :=
  ⟨by have := M.2; omega, fun _ => trivial, fun _ _ h => h⟩

/-- **The corolla of a monomial**, as a shuffle tree of monomials. -/
def corollaS {n : ℕ} (M : VMono T n) : SMono (VMono T) (Finset.range n) :=
  ⟨STree.node M fun j : Fin n => STree.leaf j.1, isShuffle_corolla M, labels_corolla M⟩

omit [IsEmpty (T 1)] in
lemma barBasisN_eq_shEv (n : ℕ) (t : SMono (VMono T) (Finset.range n))
    (h : t.1.labels = (Finset.range (Fintype.card (Fin n))).val) :
    barBasisN c hc n t = GrOperad.map (R := K) (FreeGrL.posEquiv (Fin n)).symm
      (FreeGrL.shEv (genBasis c hc) t.1 _ h) := by
  rw [barBasisN_apply, barBasis]
  exact FreeGrL.shuffleBasis_apply (genBasis c hc) (par_genBasis c hc) (Fin n) _

omit [IsEmpty (T 1)] in
/-- **The bar differential of a tree with two vertices** is the basis vector of the corolla of its
merged monomial. -/
theorem d_barBasisN_two {n : ℕ} {k l : ℕ} (m₁ : VMono T k) (ch : Fin k → STree (VMono T))
    (j₀ : Fin k) (m₂ : VMono T l) (c₂ : Fin l → STree (VMono T)) (hj₀ : ch j₀ = .node m₂ c₂)
    (hl₁ : ∀ j, j ≠ j₀ → ∃ a, ch j = .leaf a) (hl₂ : ∀ i, ∃ a, c₂ i = .leaf a)
    (ht : (STree.node m₁ ch).IsShuffle) (hlab : (STree.node m₁ ch).labels = (Finset.range n).val) :
    Bar.d (Ibar K E c hc) (Fin n) (barBasisN c hc n ⟨_, ht, hlab⟩)
      = barBasisN c hc n (corollaS ⟨⟨_, (twoMono_mem hj₀ hl₁ hl₂ ht hlab).1⟩,
          (twoMono_mem hj₀ hl₁ hl₂ ht hlab).2⟩) := by
  have hM := twoMono_mem hj₀ hl₁ hl₂ ht hlab
  have h₁ : (STree.node m₁ ch).labels = (Finset.range (Fintype.card (Fin n))).val := by
    rw [Fintype.card_fin]
    exact hlab
  have h₂ : (corollaS (⟨⟨_, hM.1⟩, hM.2⟩ : VMono T n)).1.labels
      = (Finset.range (Fintype.card (Fin n))).val := by
    rw [Fintype.card_fin]
    exact labels_corolla _
  have e1 := barBasisN_eq_shEv c hc n ⟨_, ht, hlab⟩ h₁
  have e2 := barBasisN_eq_shEv c hc n (corollaS ⟨⟨_, hM.1⟩, hM.2⟩) h₂
  have e3 := d_shEv_two c hc m₁ ch j₀ m₂ c₂ hj₀ hl₁ hl₂ ht h₁ hM.1 hM.2 h₂
  have e4 := Bar.d_map (I := Ibar K E c hc) (FreeGrL.posEquiv (Fin n)).symm
    (FreeGrL.shEv (genBasis c hc) (STree.node m₁ ch) _ h₁)
  refine (congrArg (Bar.d (Ibar K E c hc) (Fin n)) e1).trans (e4.trans ?_)
  exact (congrArg (GrOperad.map (R := K) (FreeGrL.posEquiv (Fin n)).symm) e3).trans e2.symm

/-- **`Φ` intertwines the differentials on the trees with two vertices.** -/
theorem ΦL_d_barBasisN_of_weight_two {n : ℕ} (t : SMono (VMono T) (Finset.range n))
    (hw : t.1.weight = 2) :
    ΦL c hc n (Bar.d (Ibar K E c hc) (Fin n) (barBasisN c hc n t))
      = STree.Bar.d K (ΦL c hc n (barBasisN c hc n t)) := by
  obtain ⟨t, ht, hlab⟩ := t
  obtain ⟨k, m₁, ch, j₀, l, m₂, c₂, rfl, hj₀, hl₁, hl₂⟩ := exists_two hw
  have hnd : (STree.node m₁ ch).labels.Nodup := by
    rw [hlab]
    exact Finset.nodup _
  have hM := twoMono_mem hj₀ hl₁ hl₂ ht hlab
  have hs1 : wsign K (STree.node m₁ ch) = 1 := wsign_eq_one_of_weight_le_two K _ (le_of_eq hw)
  have hs2 : wsign K (corollaS (⟨⟨_, hM.1⟩, hM.2⟩ : VMono T n)).1 = 1 :=
    wsign_eq_one_of_weight_le_two K _ (by simp [corollaS, STree.weight])
  have hcut : cuts (treeEquiv n ⟨STree.node m₁ ch, ht, hlab⟩ : barSet T n).1
      = {twoKey ch j₀} := cutKeys_toBar_two hj₀ hl₂ ht hnd hw
  rw [d_barBasisN_two c hc m₁ ch j₀ m₂ c₂ hj₀ hl₁ hl₂ ht hlab, Φ_barBasisN, Φ_barBasisN, hs2]
  dsimp only
  rw [hs1, one_smul, one_smul, STree.Bar.d, CutComplex.d_single, one_smul, CutComplex.dX,
    hcut, Finset.sum_singleton, CutComplex.sgn, Finset.filter_singleton, if_neg (lt_irrefl _),
    Finset.card_empty, pow_zero, one_smul]
  refine congrArg (fun x => Finsupp.single x (1 : K)) (Subtype.ext ?_)
  show toBar (corollaS _).1 = setF (twoKey ch j₀) false (toBar (STree.node m₁ ch))
  rw [setF_toBar_two hj₀ hl₁ hl₂]
  exact toBar_corolla _

omit [IsEmpty (T 1)] in
/-- **The bar differential kills the corollas.** -/
theorem d_barBasisN_of_weight_one {n : ℕ} (t : SMono (VMono T) (Finset.range n))
    (hw : t.1.weight = 1) :
    Bar.d (Ibar K E c hc) (Fin n) (barBasisN c hc n t) = (0 : BarCoop (Ibar K E c hc) (Fin n)) := by
  obtain ⟨t, ht, hlab⟩ := t
  obtain ⟨l, m, ch, rfl, hl⟩ := exists_corolla_of_weight_eq_one hw
  have h₁ : (STree.node m ch).labels = (Finset.range (Fintype.card (Fin n))).val := by
    rw [Fintype.card_fin]
    exact hlab
  obtain ⟨θ, -, hev⟩ := FreeGrL.exists_shEv_corolla (genBasis c hc) m ch _ h₁ hl
  have e1 := barBasisN_eq_shEv c hc n ⟨_, ht, hlab⟩ h₁
  have e2 := Bar.d_map (I := Ibar K E c hc) (FreeGrL.posEquiv (Fin n)).symm
    (FreeGrL.shEv (genBasis c hc) (STree.node m ch) _ h₁)
  refine (congrArg (Bar.d (Ibar K E c hc) (Fin n)) e1).trans (e2.trans ?_)
  rw [hev, Bar.d_map_ι, map_zero]
  rfl

/-- **`Φ` intertwines the differentials on the corollas**: both vanish. -/
theorem ΦL_d_barBasisN_of_weight_one {n : ℕ} (t : SMono (VMono T) (Finset.range n))
    (hw : t.1.weight = 1) :
    ΦL c hc n (Bar.d (Ibar K E c hc) (Fin n) (barBasisN c hc n t))
      = STree.Bar.d K (ΦL c hc n (barBasisN c hc n t)) := by
  rw [d_barBasisN_of_weight_one c hc t hw, map_zero, Φ_barBasisN, map_smul, STree.Bar.d,
    CutComplex.d_single, one_smul]
  obtain ⟨t, ht, hlab⟩ := t
  obtain ⟨l, m, ch, rfl, hl⟩ := exists_corolla_of_weight_eq_one hw
  have hnd : (STree.node m ch).labels.Nodup := by
    rw [hlab]
    exact Finset.nodup _
  have hc0 := card_cutKeys_toBar m ch ht hnd
  have hw' : (STree.node m ch).weight = 1 := hw
  rw [hw', Nat.add_eq_right, Finset.card_eq_zero] at hc0
  have hcut : cuts (treeEquiv n ⟨STree.node m ch, ht, hlab⟩ : barSet T n).1 = ∅ := hc0
  rw [CutComplex.dX, hcut, Finset.sum_empty, smul_zero]

/-- **`Φ` intertwines the differentials in vertex degrees one and two**: on the span of the trees
with one or two vertices, `ΦL ∘ Bar.d = STree.Bar.d ∘ ΦL`. -/
theorem ΦL_d_of_mem_deg {n s : ℕ} (hs : s = 1 ∨ s = 2) {x : BarCoop (Ibar K E c hc) (Fin n)}
    (hx : x ∈ deg c hc n s) :
    ΦL c hc n (Bar.d (Ibar K E c hc) (Fin n) x) = STree.Bar.d K (ΦL c hc n x) := by
  let D : BarCoop (Ibar K E c hc) (Fin n) →ₗ[K] BarCoop (Ibar K E c hc) (Fin n) :=
    Bar.d (Ibar K E c hc) (Fin n)
  have hle : deg c hc n s ≤
      LinearMap.eqLocus ((ΦL c hc n).comp D) ((STree.Bar.d K).comp (ΦL c hc n)) := by
    rw [deg, Submodule.span_le]
    rintro _ ⟨t, ht, rfl⟩
    rcases hs with rfl | rfl
    · exact ΦL_d_barBasisN_of_weight_one c hc t ht
    · exact ΦL_d_barBasisN_of_weight_two c hc t ht
  exact hle hx

end PhiTwo

end ShuffleAnySym

end Operad
