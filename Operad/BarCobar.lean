/-
# The universal twisting morphism of the bar construction

For a graded operad `P` and an ideal `I`, **the universal twisting morphism** `π : B(P, I) → P`
(`Bar.piL`, `Bar.pi`) is the projection onto the cogenerators, desuspended: the `ε`-part of the
morphism of graded operads `B(P, I) → P ⊕ εP`, `s a ↦ ε a`, into the square-zero extension by an
odd parameter (`Bar.epsHom`). It is odd, vanishes on the coaugmentation, and vanishes on the trees
without exactly one vertex (`Bar.piL_proj_bas_of_ne`, from `FreeGr.vanish_bas`).

**It satisfies the Maurer–Cartan equation** `π ∘ d + π ⋆ π = 0` (`Bar.mc_pi`), when `I` has no
operations without inputs, which the convolution square, a sum over nonempty sets of inputs, does
not see. Both terms only see the trees with two vertices (`Bar.star_piF_bas_of_ne`,
`Bar.piL_barD_bas_of_ne`), relabelled composites of two corollas (`Bar.exists_corollas`). On such a
composite the bar differential merges the corollas with the sign `(-1)^{|a|}`
(`Bar.piL_barD_corollas`), and in the convolution square only the splitting by the inputs of the
inner corolla contributes, through its unique factorization into two corollas
(`Bar.star_piF_corollas`): the inputs of the inner corolla of a composite of two corollas are a
window of ranks determined by the planar tree (`FreeGr.inner_inputs`), and composite orders
determine their factors (`Sym.LinOrd.comp_cancel`).

So `π` is a twisting morphism out of the dg cooperad `B(P, I)` (`Bar.twisting`), and the cobar
adjunction gives **the counit of the bar–cobar adjunction**, the morphism of dg operads
`ΩB(P, I) → P` (`Bar.counit`). Conversely, **a morphism of coaugmented dg cooperads `C → B(P, I)`
gives the twisting morphism `π ∘ f`** (`Bar.twistingOfHom`).
-/
import Operad.Bar
import Operad.TwistingDG
import Operad.GrKoszulDual

universe u v w

namespace Operad

open Sym GerBV TreeOfArity FreeGr
open scoped TensorProduct

/-! ## Morphisms sending the generators to `ε`-multiples -/

namespace FreeGr

variable {R : Type u} [CommRing R] {T : ℕ → Type v} {gp : ∀ k, T k → Bool}
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
  {A : Type} [Fintype A] [DecidableEq A]

/-- The number of vertices of a tree. -/
abbrev nVert (x : Reg (TreeOfArity T) A) : ℕ := FreeReg.cntR (fun _ _ => 1) x

lemma bas_comp_eq {B : Type} [Fintype B] [DecidableEq B] (i : A) (x : Reg (TreeOfArity T) A)
    (y : Reg (TreeOfArity T) B) :
    SgnLin.bas (treeSgn gp) R (SetOperad.comp i x y)
      = σ R (Tree.tpar gp (treeOf y) && Tree.apar gp (treeOf x) (x.1.rank i)) •
          GrOperad.comp (R := R) i (SgnLin.bas (treeSgn gp) R x) (SgnLin.bas (treeSgn gp) R y) := by
  rw [comp_bas_eq, smul_smul, σ_mul_self, one_smul]

/-- **A morphism sending the generators to `ε`-multiples** vanishes on the trees with vertices,
and its `ε`-part vanishes outside the trees with one vertex. -/
theorem vanish_bas (Ψ : GrOperadHom R (FreeGr R gp) (DualExt R Q true))
    (h0 : ∀ k (c : T k), DualExt.fst (Ψ.app (Fin k) (gen (R := R) (gp := gp) c)) = 0)
    (x : Reg (TreeOfArity T) A) :
    (1 ≤ nVert x → DualExt.fst (Ψ.app A (SgnLin.bas (treeSgn gp) R x)) = 0) ∧
      (nVert x ≠ 1 → DualExt.snd (Ψ.app A (SgnLin.bas (treeSgn gp) R x)) = 0) := by
  refine FreeReg.induction (P := fun A _ _ x => (1 ≤ nVert x →
      DualExt.fst (Ψ.app A (SgnLin.bas (treeSgn gp) R x)) = 0) ∧
      (nVert x ≠ 1 → DualExt.snd (Ψ.app A (SgnLin.bas (treeSgn gp) R x)) = 0)) ?_ ?_ ?_ ?_ x
  · intro A B _ _ _ _ e x hx
    rw [nVert, FreeReg.cntR_map, ← SgnLin.map_bas, Ψ.app_map]
    exact ⟨fun h => by
      show GrOperad.map (R := R) e (DualExt.fst (Ψ.app A (SgnLin.bas (treeSgn gp) R x))) = 0
      rw [hx.1 h, map_zero], fun h => by
      show GrOperad.map (R := R) e (DualExt.snd (Ψ.app A (SgnLin.bas (treeSgn gp) R x))) = 0
      rw [hx.2 h, map_zero]⟩
  · refine ⟨fun h => absurd h (by rw [nVert, FreeReg.cntR_one]; omega), fun _ => ?_⟩
    show DualExt.snd (Ψ.app Unit (GrOperad.one (R := R))) = 0
    rw [Ψ.app_one]
    rfl
  · intro A B _ _ _ _ i x y hx hy
    rw [nVert, FreeReg.cntR_comp, bas_comp_eq, map_smul, Ψ.app_comp]
    have hx0 := hx.1
    have hx1 := hx.2
    have hy0 := hy.1
    have hy1 := hy.2
    rw [nVert] at hx0 hx1 hy0 hy1
    refine ⟨fun h => ?_, fun h => ?_⟩
    · show σ R _ • GrOperad.comp (R := R) i (DualExt.fst (Ψ.app A _)) (DualExt.fst (Ψ.app B _))
        = 0
      rcases Nat.eq_zero_or_pos (FreeReg.cntR (fun _ _ => 1) x) with h1 | h1
      · rw [hy0 (by omega), map_zero, smul_zero]
      · rw [hx0 h1, LinearMap.map_zero₂, smul_zero]
    · show σ R _ • (GrOperad.comp (R := R) i (DualExt.snd (Ψ.app A _)) (DualExt.fst (Ψ.app B _))
        + GrOperad.comp (R := R) i (GrOperad.tw (R := R) true (DualExt.fst (Ψ.app A _)))
            (DualExt.snd (Ψ.app B _))) = 0
      rcases Nat.eq_zero_or_pos (FreeReg.cntR (fun _ _ => 1) x) with h1 | h1
      · rw [hx1 (by omega), hy1 (by omega), LinearMap.map_zero₂, map_zero, add_zero,
          smul_zero]
      · rw [hx0 h1, map_zero, LinearMap.map_zero₂, add_zero]
        rcases Nat.eq_zero_or_pos (FreeReg.cntR (fun _ _ => 1) y) with h2 | h2
        · rw [hx1 (by omega), LinearMap.map_zero₂, smul_zero]
        · rw [hy0 h2, map_zero, smul_zero]
  · intro k c
    refine ⟨fun _ => h0 k c, fun h => absurd ?_ h⟩
    rw [nVert, FreeReg.cntR_std]

end FreeGr

/-! ## Trees with two vertices -/

namespace Tree

variable {E : ℕ → Type v}

mutual

/-- **Counting the vertices with weight one** counts them. -/
theorem cnt_one : ∀ t : Tree E, cnt (fun _ _ => 1) t = t.weight
  | .leaf => rfl
  | .node _ f => by rw [cnt_node, weight_node, cntF_one f, add_comm]

theorem cntF_one : ∀ {k : ℕ} (f : Forest E k), Forest.cntF (fun _ _ => 1) f = f.weightF
  | _, .nil => rfl
  | _, .cons t f => by rw [cntF_cons, Forest.weightF, cnt_one t, cntF_one f]

end

lemma vbF_leaves : ∀ (k p : ℕ), (TreeOfArity.leaves (E := E) k).vbF p = 0
  | 0, _ => rfl
  | k + 1, p => by
    rw [TreeOfArity.leaves, Forest.vbF]
    split_ifs
    · rfl
    · rw [weight_leaf, zero_add, vbF_leaves k]

/-- **The cut of a graft of two corollas at its second vertex** recovers them and the leaf of the
graft. -/
lemma cutV_graft_corolla {k l : ℕ} (c : E k) (g : E l) {r : ℕ} (hr : r < k) :
    ((corolla c).1.graft r (corolla g).1).cutV 1 = ((corolla c).1, (corolla g).1, r) := by
  have h := cutV_graft (corolla c).1 r (corolla g).1 (by rw [(corolla c).2]; exact hr) rfl
  have hv : (corolla c).1.vb r = 1 := by
    show (TreeOfArity.leaves k).vbF r + 1 = 1
    rw [vbF_leaves]
  rwa [hv] at h

end Tree

namespace Sym.LinOrd

variable {A B : Type} [DecidableEq A]

/-- **A composite order determines its factors**, when the inner one is not empty. -/
lemma comp_cancel {i : A} {P P' : LinOrd A} {Q Q' : LinOrd B} (b₀ : B)
    (h : LinOrd.comp i P Q = LinOrd.comp i P' Q') : P = P' ∧ Q = Q' := by
  have hl : ∀ w w', compLt P.lt Q.lt i w w' ↔ compLt P'.lt Q'.lt i w w' := fun w w' => by
    have := congrArg LinOrd.lt h
    exact Iff.of_eq (congrFun (congrFun this w) w')
  refine ⟨LinOrd.ext fun a a' => ?_, LinOrd.ext fun b b' => hl (Sum.inr b) (Sum.inr b')⟩
  by_cases ha : a = i <;> by_cases ha' : a' = i
  · subst ha ha'
    exact ⟨fun h => absurd h (P.irrefl _), fun h => absurd h (P'.irrefl _)⟩
  · subst ha
    exact hl (Sum.inr b₀) (Sum.inl ⟨a', ha'⟩)
  · subst ha'
    exact hl (Sum.inl ⟨a, ha⟩) (Sum.inr b₀)
  · exact hl (Sum.inl ⟨a, ha⟩) (Sum.inl ⟨a', ha'⟩)

variable [Fintype A] [Fintype B]

/-- **The inputs of the inner operation of a composite form a window of ranks.** -/
lemma mem_window (i : A) (P : LinOrd A) (Q : LinOrd B) (w : Without A i ⊕ B) :
    (P.rank i ≤ (LinOrd.comp i P Q).rank w ∧
        (LinOrd.comp i P Q).rank w < P.rank i + Fintype.card B) ↔ ∃ b, w = Sum.inr b := by
  rcases w with ⟨a, ha⟩ | b
  · refine ⟨fun ⟨h1, h2⟩ => ?_, fun ⟨b, hb⟩ => absurd hb Sum.inl_ne_inr⟩
    exfalso
    rcases P.total a i ha with h | h
    · rw [rank_comp_inl_of_lt i P Q ⟨a, ha⟩ h] at h1
      exact absurd (P.rank_lt_rank h) (not_lt.2 h1)
    · have e := rank_comp_inl_of_gt i P Q ⟨a, ha⟩ h
      have := P.rank_lt_rank h
      dsimp only at e
      omega
  · refine ⟨fun _ => ⟨b, rfl⟩, fun _ => ?_⟩
    rw [rank_comp_inr]
    have := Q.rank_lt_card b
    omega

end Sym.LinOrd

namespace FreeGr

variable {T : ℕ → Type v}

lemma nVert_eq {A : Type} [Fintype A] [DecidableEq A] (x : Reg (TreeOfArity T) A) :
    nVert x = (treeOf x).weight :=
  Tree.cnt_one _

/-- The trees with one vertex are the corollas. -/
lemma eq_corolla_of_nVert {A : Type} [Fintype A] [DecidableEq A] {x : Reg (TreeOfArity T) A}
    (h : nVert x = 1) : ∃ (k : ℕ) (c : T k), treeOf x = (corolla c).1 := by
  rw [nVert_eq] at h
  exact eq_corolla_of_weight h

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **The data of a composite of two corollas**: its tree determines the graft leaf and the
corollas. -/
lemma graft_corolla_data {A' B' : Type} [Fintype A'] [DecidableEq A'] [Fintype B']
    [DecidableEq B'] {i : A} {i' : A'} {p : Reg (TreeOfArity T) A} {q : Reg (TreeOfArity T) B}
    {p' : Reg (TreeOfArity T) A'} {q' : Reg (TreeOfArity T) B'} (hp : nVert p = 1)
    (hq : nVert q = 1) (hp' : nVert p' = 1) (hq' : nVert q' = 1)
    (h : (treeOf p).graft (p.1.rank i) (treeOf q) = (treeOf p').graft (p'.1.rank i') (treeOf q')) :
    p.1.rank i = p'.1.rank i' ∧ treeOf p = treeOf p' ∧ treeOf q = treeOf q' := by
  obtain ⟨k, c, hc⟩ := eq_corolla_of_nVert hp
  obtain ⟨l, g, hg⟩ := eq_corolla_of_nVert hq
  obtain ⟨k', c', hc'⟩ := eq_corolla_of_nVert hp'
  obtain ⟨l', g', hg'⟩ := eq_corolla_of_nVert hq'
  have hr := rank_lt_arity p i
  have hr' := rank_lt_arity p' i'
  rw [hc, (corolla c).2] at hr
  rw [hc', (corolla c').2] at hr'
  have e := congrArg (fun t => t.cutV 1) h
  simp only at e
  rw [hc, hg, hc', hg', Tree.cutV_graft_corolla c g hr, Tree.cutV_graft_corolla c' g' hr'] at e
  simp only [Prod.mk.injEq] at e
  exact ⟨e.2.2, by rw [hc, hc', e.1], by rw [hg, hg', e.2.1]⟩

/-- **Factorizations into two corollas are unique**, when the inner one has inputs. -/
lemma fact_corolla_unique {i : A} (b₀ : B) {p p' : Reg (TreeOfArity T) A}
    {q q' : Reg (TreeOfArity T) B} (hp : nVert p = 1) (hq : nVert q = 1) (hp' : nVert p' = 1)
    (hq' : nVert q' = 1) (h : SetOperad.comp i p q = SetOperad.comp i p' q') : p = p' ∧ q = q' := by
  have ho := LinOrd.comp_cancel b₀ (congrArg Prod.fst h)
  have ht := congrArg treeOf h
  rw [treeOf_comp, treeOf_comp] at ht
  obtain ⟨-, h1, h2⟩ := graft_corolla_data hp hq hp' hq' ht
  exact ⟨reg_ext ho.1 h1, reg_ext ho.2 h2⟩

/-- **The inputs of the inner corolla of a composite of two corollas are determined by the
composite.** -/
lemma inner_inputs {X : Type} [Fintype X] [DecidableEq X] {A' B' : Type} [Fintype A']
    [DecidableEq A'] [Fintype B'] [DecidableEq B'] {i : A} {i' : A'} (e : Without A i ⊕ B ≃ X)
    (e' : Without A' i' ⊕ B' ≃ X) {p : Reg (TreeOfArity T) A} {q : Reg (TreeOfArity T) B}
    {p' : Reg (TreeOfArity T) A'} {q' : Reg (TreeOfArity T) B'} (hp : nVert p = 1)
    (hq : nVert q = 1) (hp' : nVert p' = 1) (hq' : nVert q' = 1)
    (h : SetOperad.map e (SetOperad.comp i p q) = SetOperad.map e' (SetOperad.comp i' p' q'))
    (a : X) : (∃ b, e (Sum.inr b) = a) ↔ ∃ b, e' (Sum.inr b) = a := by
  have ht := congrArg treeOf h
  simp only [treeOf_map, treeOf_comp] at ht
  obtain ⟨hr, -, hq2⟩ := graft_corolla_data hp hq hp' hq' ht
  have hcard : Fintype.card B = Fintype.card B' := by
    rw [← q.2.2, ← q'.2.2, ← treeOf_arity, ← treeOf_arity, hq2]
  have ho := congrArg (fun x : Reg (TreeOfArity T) X => x.1.rank a) h
  simp only [map_fst, comp_fst, LinOrd.rank_map] at ho
  have w := LinOrd.mem_window i p.1 q.1 (e.symm a)
  have w' := LinOrd.mem_window i' p'.1 q'.1 (e'.symm a)
  rw [ho, hr, hcard, w'] at w
  constructor
  · rintro ⟨b, rfl⟩
    obtain ⟨b', hb'⟩ := w.2 ⟨b, by rw [Equiv.symm_apply_apply]⟩
    exact ⟨b', by rw [← hb', Equiv.apply_symm_apply]⟩
  · rintro ⟨b', rfl⟩
    obtain ⟨b, hb⟩ := w.1 ⟨b', by rw [Equiv.symm_apply_apply]⟩
    exact ⟨b, by rw [← hb, Equiv.apply_symm_apply]⟩

/-- **Two labelled trees with the same planar tree are relabellings of each other.** -/
lemma exists_map_eq {x : Reg (TreeOfArity T) A} {y : Reg (TreeOfArity T) B}
    (h : treeOf x = treeOf y) : ∃ e : A ≃ B, SetOperad.map e x = y := by
  have hc : Fintype.card A = Fintype.card B := by
    rw [← x.2.2, ← y.2.2, ← treeOf_arity, ← treeOf_arity, h]
  refine ⟨x.1.toRank.trans ((finCongr hc).trans y.1.toRank.symm), reg_ext ?_ h⟩
  refine LinOrd.ext fun a b => ?_
  rw [map_fst, LinOrd.map_lt, x.1.lt_iff_rank_lt, y.1.lt_iff_rank_lt]
  have key : ∀ c : B, x.1.rank ((x.1.toRank.trans ((finCongr hc).trans y.1.toRank.symm)).symm c)
      = y.1.rank c := fun c => by
    have := congrArg Fin.val (x.1.toRank.apply_symm_apply
      ((finCongr hc).symm (y.1.toRank c)))
    rw [LinOrd.toRank_apply] at this
    simpa [Equiv.symm_trans_apply, LinOrd.toRank_apply] using this
  rw [key, key]

/-- Composites at equal inputs are relabellings of each other, in a set operad. -/
lemma setComp_slot {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type w} [SetOperad S]
    {j j' : A} (h : j = j') (x : S A) (y : S B) :
    SetOperad.comp j' x y = SetOperad.map (slotEquiv (B := B) h) (SetOperad.comp j x y) := by
  subst h
  have : slotEquiv (B := B) (rfl : j = j) = Equiv.refl _ := Equiv.ext fun z => by
    rcases z with (⟨a, ha⟩ | b) <;> rfl
  rw [this, SetOperad.map_refl]

/-- **The canonical form of a composite of labelled trees**, at the splitting of its inputs by
those of the inner tree. -/
lemma map_comp_canon_reg {X : Type} [Fintype X] [DecidableEq X] {i : A}
    (e : Without A i ⊕ B ≃ X) (S : Finset X) (hS : ∀ x, x ∈ S ↔ ∃ b, e (Sum.inr b) = x)
    (x : Reg (TreeOfArity T) A) (y : Reg (TreeOfArity T) B) :
    SetOperad.map e (SetOperad.comp i x y)
      = SetOperad.map (splitEquiv S) (SetOperad.comp none
          (SetOperad.map (GrOperad.canonOut e S hS) x)
          (SetOperad.map (GrOperad.canonIn e S hS) y)) := by
  have hE : (compEquiv (GrOperad.canonOut e S hS) (GrOperad.canonIn e S hS) i).trans
      ((slotEquiv (B := SIn S) (GrOperad.canonOut_self e S hS)).trans (splitEquiv S)) = e := by
    ext z
    rcases z with (⟨a, ha⟩ | b)
    · simp only [Equiv.trans_apply, compEquiv_inl, slotEquiv_inl, splitEquiv_inl]
      exact outVal_eq_of_eq _ (GrOperad.canonOut_ne e S hS ha)
    · rfl
  rw [setComp_slot (GrOperad.canonOut_self e S hS), ← SetOperad.map_comp,
    ← SetOperad.map_trans, ← SetOperad.map_trans, hE]

end FreeGr

/-! ## The universal twisting morphism -/

section Pi

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  (I : GrOperadIdeal R P)

local notation "𝒥" => GrOperadIdeal.span R (grLinRel R (BarGen I))

namespace Bar

/-- The generators `s a ↦ ε a`, into the square-zero extension of `P` by an odd parameter. -/
noncomputable def epsGen : GrSpeciesHom R (BarGen I) (DualExt R P true) where
  app A _ _ :=
    { toFun := fun w => DualExt.mk 0 (IdealSp.val I w)
      map_add' := fun w w' => Prod.ext (add_zero 0).symm rfl
      map_smul' := fun a w => Prod.ext (smul_zero a).symm rfl }
  app_map e w := Prod.ext (by
    show (0 : P _) = GrOperad.map (R := R) e 0
    rw [map_zero]) rfl
  app_par c w := Prod.ext (by
    show (0 : P _) = GrOperad.par (R := R) c 0
    rw [map_zero]) (by
    show IdealSp.val I (GrSpecies.par (R := R) (V := IdealSp I) (!c) w)
      = GrOperad.par (R := R) (xor c true) (IdealSp.val I w)
    rw [Bool.xor_true]
    rfl)

/-- **The morphism `B(P, I) → P ⊕ εP`**, `s a ↦ ε a`. -/
noncomputable def epsHom : GrOperadHom R (FreeGrL R (BarGen I)) (DualExt R P true) :=
  FreeGrL.homEquiv.symm (epsGen I)

/-- **The universal twisting morphism** `π : B(P, I) → P`: the projection onto the cogenerators,
desuspended. -/
noncomputable def piL (A : Type) [Fintype A] [DecidableEq A] :
    FreeGrL R (BarGen I) A →ₗ[R] P A :=
  DualExt.snd ∘ₗ (epsHom I).app A

variable {I}

lemma epsHom_ι {A : Type} [Fintype A] [DecidableEq A] (w : BarGen I A) :
    (epsHom I).app A ((FreeGrL.ι R (BarGen I)).app A w) = DualExt.mk 0 (IdealSp.val I w) := by
  rw [epsHom, FreeGrL.homEquiv_symm_ι]
  rfl

lemma piL_ι {A : Type} [Fintype A] [DecidableEq A] (w : BarGen I A) :
    piL I A ((FreeGrL.ι R (BarGen I)).app A w) = IdealSp.val I w := by
  rw [piL, LinearMap.comp_apply, epsHom_ι]
  rfl

lemma piL_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    (x : FreeGrL R (BarGen I) A) :
    piL I B (GrOperad.map (R := R) e x) = GrOperad.map (R := R) e (piL I A x) := by
  rw [piL, LinearMap.comp_apply, (epsHom I).app_map]
  rfl

/-- **The universal twisting morphism is odd.** -/
lemma piL_par {A : Type} [Fintype A] [DecidableEq A] (c : Bool) (x : FreeGrL R (BarGen I) A) :
    piL I A (GrOperad.par (R := R) c x) = GrOperad.par (R := R) (!c) (piL I A x) := by
  rw [piL, LinearMap.comp_apply, (epsHom I).app_par, ← Bool.xor_true]
  rfl

lemma piL_one : piL I Unit (GrOperad.one (R := R)) = 0 := by
  rw [piL, LinearMap.comp_apply, (epsHom I).app_one]
  rfl

/-- The morphism of `s a ↦ ε a` on the trees decorated by homogeneous elements. -/
noncomputable abbrev epsF : GrOperadHom R (FreeGr R (grGenPar R (BarGen I))) (DualExt R P true) :=
  (epsHom I).comp (𝒥).projHom

lemma proj_gen {k : ℕ} (c : BarT I k) :
    (𝒥).proj (Fin k) (gen (R := R) (gp := grGenPar R (BarGen I)) c)
      = (FreeGrL.ι R (BarGen I)).app (Fin k) c.1.1 :=
  (FreeGrL.ι_app_hom c.2).symm

lemma epsF_gen {k : ℕ} (c : BarT I k) :
    (epsF (I := I)).app (Fin k) (gen (R := R) (gp := grGenPar R (BarGen I)) c)
      = DualExt.mk 0 c.val := by
  show (epsHom I).app (Fin k) ((𝒥).proj (Fin k) (gen c)) = _
  rw [proj_gen, epsHom_ι]
  rfl

/-- **The universal twisting morphism on a generator** is its desuspension. -/
lemma piL_proj_gen {k : ℕ} (c : BarT I k) :
    piL I (Fin k) ((𝒥).proj (Fin k) (gen (R := R) (gp := grGenPar R (BarGen I)) c)) = c.val := by
  rw [proj_gen, piL_ι]
  rfl

/-- **The universal twisting morphism vanishes on the trees without exactly one vertex.** -/
theorem piL_proj_bas_of_ne {A : Type} [Fintype A] [DecidableEq A]
    (x : Reg (TreeOfArity (BarT I)) A) (hx : nVert x ≠ 1) :
    piL I A ((𝒥).proj A (SgnLin.bas (treeSgn (grGenPar R (BarGen I))) R x)) = 0 :=
  (FreeGr.vanish_bas (epsF (I := I)) (fun k c => by rw [epsF_gen]; rfl) x).2 hx

end Bar

end Pi

/-! ## The convolution square on basis trees -/

namespace FreeGr

variable {R : Type u} [CommRing R] {T : ℕ → Type v} {gp : ∀ k, T k → Bool}
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
  {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- **A convolution composite on a basis tree**: the signed sum over its factorizations. -/
lemma compC_bas (i : X) (f : ConvOp R (FreeGr R gp) Q X) {g : ConvOp R (FreeGr R gp) Q Y}
    (hg : ConvOp.IsParC true g) (t : Reg (TreeOfArity T) (Without X i ⊕ Y)) :
    ConvOp.toLin (ConvOp.compC i f g) (SgnLin.bas (treeSgn gp) R t)
      = ∑ pq ∈ (SetOperad.FiniteFact.finite i t).toFinset,
          σ R (Tree.tpar gp (treeOf pq.2) && Tree.apar gp (treeOf pq.1) (pq.1.1.rank i)) •
            GrOperad.comp (R := R) i
              (ConvOp.toLin f (GrSpecies.tw (R := R) true (SgnLin.bas (treeSgn gp) R pq.1)))
              (ConvOp.toLin g (SgnLin.bas (treeSgn gp) R pq.2)) := by
  rw [ConvOp.toLin_compC, LinearMap.comp_apply, LinearMap.comp_apply, decomp_bas, map_sum,
    map_sum]
  refine Finset.sum_congr rfl fun pq _ => ?_
  rw [map_smul, map_smul, ConvOp.kap_tmul f hg, ConvOp.mu_tmul]

lemma tw_bas' (t : Reg (TreeOfArity T) X) :
    GrSpecies.tw (R := R) (V := FreeGr R gp) true (SgnLin.bas (treeSgn gp) R t)
      = σ R (Tree.tpar gp (treeOf t)) • SgnLin.bas (treeSgn gp) R t :=
  (GrSpecies.tw_hom true (SgnLin.par_bas t)).trans (by rw [Bool.true_and]; rfl)

end FreeGr

section MC

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {I : GrOperadIdeal R P}

local notation "𝒥" => GrOperadIdeal.span R (grLinRel R (BarGen I))

namespace Bar

/-- The bar differential kills the coaugmentation. -/
instance instDOne : DGCooperad.DOne R (BarCoop I) := ⟨d_one⟩

variable (I) in
/-- **The universal twisting morphism**, an invariant family of the convolution operad of the bar
construction and `P`. -/
noncomputable def pi : GrOperad.Inv R (ConvOp R (BarCoop I) (ZeroDG R P)) :=
  ⟨fun A _ _ => ConvOp.of (piL I A), fun A B _ _ _ _ e => by
    show ConvOp.mapC e (ConvOp.of (piL I A)) = ConvOp.of (piL I B)
    ext x
    rw [ConvOp.mapC_apply, ConvOp.toLin_of, ConvOp.toLin_of]
    show GrOperad.map (R := R) e (piL I A (GrOperad.map (R := R) e.symm x)) = _
    rw [← piL_map, ← GrOperad.map_trans, Equiv.symm_trans_self, GrOperad.map_refl]⟩

lemma pi_apply (A : Type) [Fintype A] [DecidableEq A] : (pi I).1 A = ConvOp.of (piL I A) := rfl

/-- **The universal twisting morphism is odd.** -/
lemma isPar_pi : GrOperad.Inv.IsPar true (pi I) := by
  intro A _ _
  show ConvOp.parC true (ConvOp.of (piL I A)) = ConvOp.of (piL I A)
  rw [ConvOp.parC_eq_self_iff]
  intro c x
  rw [ConvOp.toLin_of, Bool.xor_true]
  exact piL_par c x

/-- **The universal twisting morphism vanishes on the coaugmentation.** -/
lemma killsUnit_pi : KillsUnit R (BarCoop I) (ZeroDG R P) (pi I) := by
  intro A _ _ x hx
  show piL I A x = 0
  refine Submodule.span_induction (p := fun x _ => piL I A x = 0) ?_ (map_zero _) ?_ ?_ hx
  · rintro _ ⟨e, rfl⟩
    show piL I A (GrOperad.map (R := R) e (GrOperad.one (R := R))) = 0
    rw [piL_map, piL_one, map_zero]
  · intro x y _ _ hx hy
    beta_reduce at hx hy ⊢
    rw [map_add, hx, hy, add_zero]
  · intro a x _ hx
    beta_reduce at hx ⊢
    rw [map_smul, hx, smul_zero]

variable (I) in
/-- The projection from the free graded operad on the homogeneous decorations. -/
noncomputable abbrev projB :
    GrCooperadHom R (FreeGr R (grGenPar R (BarGen I))) (BarCoop I) :=
  FreeGrL.projHom R (BarGen I)

variable (I) in
/-- **The universal twisting morphism on the trees decorated by homogeneous elements.** -/
noncomputable def piF : GrOperad.Inv R (ConvOp R (FreeGr R (grGenPar R (BarGen I))) (ZeroDG R P)) :=
  GrOperad.Inv.appHom (ConvOp.preHom (P := ZeroDG R P) (projB I)) (pi I)

lemma piF_apply {A : Type} [Fintype A] [DecidableEq A] (y : FreeGr R (grGenPar R (BarGen I)) A) :
    ConvOp.toLin ((piF I).1 A) y = piL I A ((𝒥).proj A y) := rfl

lemma isParC_piF (A : Type) [Fintype A] [DecidableEq A] : ConvOp.IsParC true ((piF I).1 A) := by
  rw [← ConvOp.parC_eq_self_iff]
  show ConvOp.parC true ((ConvOp.preHom (P := ZeroDG R P) (projB I)).app A ((pi I).1 A)) = _
  rw [← ConvOp.par_def, ← (ConvOp.preHom (P := ZeroDG R P) (projB I)).app_par, isPar_pi (I := I) A]
  rfl

lemma star_proj {A : Type} [Fintype A] [DecidableEq A] (y : FreeGr R (grGenPar R (BarGen I)) A) :
    ConvOp.toLin ((GrOperad.Inv.star R _ (pi I) (pi I)).1 A) ((𝒥).proj A y)
      = ConvOp.toLin ((GrOperad.Inv.star R _ (piF I) (piF I)).1 A) y := by
  rw [piF, ← GrOperad.Inv.appHom_star]
  rfl

/-- The terms of the convolution square on a basis tree, at a splitting. -/
lemma term_bas {A : Type} [Fintype A] [DecidableEq A] (S : Finset A)
    (t : Reg (TreeOfArity (BarT I)) A) :
    ConvOp.toLin (GrOperad.Inv.term (R := R) (piF I).1 (piF I).1 A S)
        (SgnLin.bas (treeSgn (grGenPar R (BarGen I))) R t)
      = GrOperad.map (R := R) (splitEquiv S) (∑ pq ∈ (SetOperad.FiniteFact.finite none
          (SetOperad.map (splitEquiv S).symm t)).toFinset,
          σ R (Tree.tpar (grGenPar R (BarGen I)) (treeOf pq.2)
            && Tree.apar (grGenPar R (BarGen I)) (treeOf pq.1) (pq.1.1.rank none)) •
            GrOperad.comp (R := R) none
              (σ R (Tree.tpar (grGenPar R (BarGen I)) (treeOf pq.1)) •
                piL I _ ((𝒥).proj _ (SgnLin.bas (treeSgn (grGenPar R (BarGen I))) R pq.1)))
              (piL I _ ((𝒥).proj _ (SgnLin.bas (treeSgn (grGenPar R (BarGen I))) R pq.2)))) := by
  show ConvOp.toLin (ConvOp.mapC (splitEquiv S)
    (ConvOp.compC none ((piF I).1 (SOut S)) ((piF I).1 (SIn S)))) _ = _
  rw [ConvOp.mapC_apply]
  show GrOperad.map (R := R) (splitEquiv S) (ConvOp.toLin (ConvOp.compC none _ _)
    (GrOperad.map (R := R) (splitEquiv S).symm _)) = _
  rw [SgnLin.map_bas, FreeGr.compC_bas none _ (isParC_piF (SIn S))]
  refine congrArg _ (Finset.sum_congr rfl fun pq _ => ?_)
  rw [FreeGr.tw_bas', map_smul]
  rfl

lemma proj_map' {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    (y : FreeGr R (grGenPar R (BarGen I)) A) :
    (𝒥).proj B (GrOperad.map (R := R) e y) = GrOperad.map (R := R) e ((𝒥).proj A y) := rfl

lemma piL_proj_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) (y : FreeGr R (grGenPar R (BarGen I)) A) :
    piL I B ((𝒥).proj B (GrOperad.map (R := R) e y))
      = GrOperad.map (R := R) e (piL I A ((𝒥).proj A y)) := by
  rw [proj_map', piL_map]

/-- **The convolution square of the universal twisting morphism vanishes outside the trees with
two vertices.** -/
lemma star_piF_bas_of_ne {A : Type} [Fintype A] [DecidableEq A]
    (t : Reg (TreeOfArity (BarT I)) A) (ht : nVert t ≠ 2) :
    ConvOp.toLin ((GrOperad.Inv.star R _ (piF I) (piF I)).1 A)
      (SgnLin.bas (treeSgn (grGenPar R (BarGen I))) R t) = 0 := by
  rw [GrOperad.Inv.star_apply, ConvOp.toLin_sum, LinearMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun S _ => ?_
  rw [term_bas]
  refine (congrArg _ (Finset.sum_eq_zero fun pq hpq => ?_)).trans (map_zero _)
  have hc := FreeGr.mem_fib.1 hpq
  have hn : nVert pq.1 + nVert pq.2 = nVert t := by
    rw [nVert, nVert, ← FreeReg.cntR_comp, hc, FreeReg.cntR_map]
  by_cases h1 : nVert pq.1 = 1
  · rw [piL_proj_bas_of_ne pq.2 (by omega), map_zero, smul_zero]
  · rw [piL_proj_bas_of_ne pq.1 h1, smul_zero, LinearMap.map_zero₂, smul_zero]

/-- **The universal twisting morphism after the bar differential vanishes outside the trees with
two vertices.** -/
lemma piL_barD_bas_of_ne {A : Type} [Fintype A] [DecidableEq A]
    (t : Reg (TreeOfArity (BarT I)) A) (ht : nVert t ≠ 2) :
    piL I A ((𝒥).proj A (barD (barMerge I) (grGenPar R (BarGen I)) R A
      (SgnLin.bas (treeSgn (grGenPar R (BarGen I))) R t))) = 0 := by
  rw [barD_bas, map_sum, map_sum]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Finset.mem_Ico] at hk
  rw [map_smul, map_smul, piL_proj_bas_of_ne _ ?_, smul_zero]
  have hw := Tree.weight_contr (barMerge I) hk.1 hk.2
  rw [nVert_eq] at ht ⊢
  rw [treeOf_contrR]
  omega

lemma nVert_std {k : ℕ} (c : BarT I k) : nVert (Reg.std (corolla c)) = 1 :=
  FreeReg.cntR_std _ c

/-- **A composite of two corollas is the composite of the generators.** -/
lemma bas_corollas {k l : ℕ} (c : BarT I k) (g : BarT I l) (r : Fin k) :
    SgnLin.bas (treeSgn (grGenPar R (BarGen I))) R
        (SetOperad.comp r (Reg.std (corolla c)) (Reg.std (corolla g)))
      = GrOperad.comp (R := R) r (gen (R := R) (gp := grGenPar R (BarGen I)) c)
          (gen (R := R) (gp := grGenPar R (BarGen I)) g) := by
  rw [FreeGr.bas_comp_eq]
  have h : Tree.apar (grGenPar R (BarGen I)) (treeOf (Reg.std (corolla c)))
      ((Reg.std (corolla c)).1.rank r) = false := aparF_leaves _ k _
  rw [h, Bool.and_false, σ_false, one_smul]
  rfl

/-- **The bar differential on a composite of two corollas** merges them, with the sign
`(-1)^{|a|}`. -/
theorem piL_barD_corollas {k l : ℕ} (c : BarT I k) (g : BarT I l) (r : Fin k) :
    piL I _ ((𝒥).proj _ (barD (barMerge I) (grGenPar R (BarGen I)) R _
        (SgnLin.bas (treeSgn (grGenPar R (BarGen I))) R
          (SetOperad.comp r (Reg.std (corolla c)) (Reg.std (corolla g))))))
      = σ R (!c.1.2) • GrOperad.comp (R := R) r c.val g.val := by
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = k + l := ⟨k + l - 1, by have := r.2; omega⟩
  rw [bas_corollas, barD_comp barMerge_odd, barD_gen, barD_gen, LinearMap.map_zero₂, map_zero,
    zero_add, zero_add, mcomp_gen_bar c r g m hm, piL_proj_map, piL_proj_gen,
    barMerge_val _ _ ⟨r.2, hm⟩, barVal, Fin.eta, map_smul, map_symm_map]

/-- **The convolution square of the universal twisting morphism on a composite of two corollas**
composes them, with the sign `(-1)^{|s a|}`. Composites with operations without inputs, which the
convolution square does not see, are excluded by asking the ideal to have none. -/
theorem star_piF_corollas (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0) {k l : ℕ} (c : BarT I k)
    (g : BarT I l) (r : Fin k) :
    ConvOp.toLin ((GrOperad.Inv.star R _ (piF I) (piF I)).1 _)
        (SgnLin.bas (treeSgn (grGenPar R (BarGen I))) R
          (SetOperad.comp r (Reg.std (corolla c)) (Reg.std (corolla g))))
      = σ R c.1.2 • GrOperad.comp (R := R) r c.val g.val := by
  set x₀ := SetOperad.comp r (Reg.std (corolla c)) (Reg.std (corolla g))
  rw [GrOperad.Inv.star_apply, ConvOp.toLin_sum, LinearMap.coe_sum, Finset.sum_apply]
  set S₀ : Finset (Without (Fin k) r ⊕ Fin l) := Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩
  have hS₀ : ∀ x, x ∈ S₀ ↔ ∃ b, (Equiv.refl _) (Sum.inr b) = x := fun x => by
    simp [S₀, eq_comm]
  have hoff : ∀ S ∈ nonempties (Without (Fin k) r ⊕ Fin l), S ≠ S₀ →
      ConvOp.toLin (GrOperad.Inv.term (R := R) (piF I).1 (piF I).1 _ S)
        (SgnLin.bas (treeSgn (grGenPar R (BarGen I))) R x₀) = 0 := by
    intro S _ hS
    rw [term_bas]
    refine (congrArg _ (Finset.sum_eq_zero fun pq hpq => ?_)).trans (map_zero _)
    by_cases h1 : nVert pq.1 = 1
    · by_cases h2 : nVert pq.2 = 1
      · exfalso
        apply hS
        have hc := FreeGr.mem_fib.1 hpq
        have hx : SetOperad.map (splitEquiv S) (SetOperad.comp none pq.1 pq.2)
            = SetOperad.map (Equiv.refl _) x₀ := by
          rw [hc, SetOperad.map_map_symm, SetOperad.map_refl]
        have key := FreeGr.inner_inputs (splitEquiv S) (Equiv.refl _) h1 h2 (nVert_std c)
          (nVert_std g) hx
        ext a
        rw [hS₀ a, ← key a]
        constructor
        · intro ha
          exact ⟨⟨a, ha⟩, rfl⟩
        · rintro ⟨b, rfl⟩
          exact b.2
      · rw [piL_proj_bas_of_ne _ h2, map_zero, smul_zero]
    · rw [piL_proj_bas_of_ne _ h1, smul_zero, LinearMap.map_zero₂, smul_zero]
  by_cases hl : l = 0
  · subst hl
    have hg : g.val = 0 := hI0 _ g.mem
    have hzero : ∀ S ∈ nonempties (Without (Fin k) r ⊕ Fin 0),
        ConvOp.toLin (GrOperad.Inv.term (R := R) (piF I).1 (piF I).1 _ S)
          (SgnLin.bas (treeSgn (grGenPar R (BarGen I))) R x₀) = 0 := by
      intro S hS
      refine hoff S hS fun h => ?_
      have hne := (Finset.mem_filter.1 hS).2
      rw [h] at hne
      obtain ⟨⟨a, ha⟩ | b, hb⟩ := hne
      · simp [S₀] at hb
      · exact b.elim0
    rw [Finset.sum_eq_zero hzero, hg, map_zero, smul_zero]
    rfl
  · have hne : S₀ ∈ nonempties (Without (Fin k) r ⊕ Fin l) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨Sum.inr ⟨0, by omega⟩, by simp [S₀]⟩⟩
    rw [Finset.sum_eq_single S₀ (fun S hS h => hoff S hS h) (fun h => absurd hne h), term_bas]
    have hcanon := FreeGr.map_comp_canon_reg (Equiv.refl _) S₀ hS₀ (Reg.std (corolla c))
      (Reg.std (corolla g))
    rw [SetOperad.map_refl] at hcanon
    have hx₀ : SetOperad.map (splitEquiv S₀).symm x₀
        = SetOperad.comp none
            (SetOperad.map (GrOperad.canonOut (Equiv.refl _) S₀ hS₀) (Reg.std (corolla c)))
            (SetOperad.map (GrOperad.canonIn (Equiv.refl _) S₀ hS₀) (Reg.std (corolla g))) := by
      change SetOperad.map _ (SetOperad.comp r (Reg.std (corolla c)) (Reg.std (corolla g))) = _
      rw [hcanon, SetOperad.map_symm_map]
    set pa := SetOperad.map (GrOperad.canonOut (Equiv.refl _) S₀ hS₀) (Reg.std (corolla c))
    set pb := SetOperad.map (GrOperad.canonIn (Equiv.refl _) S₀ hS₀) (Reg.std (corolla g))
    have hpa : nVert pa = 1 := by
      rw [nVert, FreeReg.cntR_map]
      exact nVert_std c
    have hpb : nVert pb = 1 := by
      rw [nVert, FreeReg.cntR_map]
      exact nVert_std g
    obtain ⟨b₀⟩ : Nonempty (SIn S₀) := ⟨⟨Sum.inr ⟨0, by omega⟩, by simp [S₀]⟩⟩
    rw [hx₀, Finset.sum_eq_single (pa, pb) ?_ ?_]
    · have h1 : Tree.apar (grGenPar R (BarGen I)) (treeOf pa) (pa.1.rank none) = false :=
        aparF_leaves _ k _
      have h2 : Tree.tpar (grGenPar R (BarGen I)) (treeOf pa) = c.1.2 := tpar_corolla' c
      have h3 : piL I _ ((𝒥).proj _ (SgnLin.bas (treeSgn (grGenPar R (BarGen I))) R pa))
          = GrOperad.map (R := R) (GrOperad.canonOut (Equiv.refl _) S₀ hS₀) c.val := by
        rw [← SgnLin.map_bas, piL_proj_map]
        exact congrArg _ (piL_proj_gen c)
      have h4 : piL I _ ((𝒥).proj _ (SgnLin.bas (treeSgn (grGenPar R (BarGen I))) R pb))
          = GrOperad.map (R := R) (GrOperad.canonIn (Equiv.refl _) S₀ hS₀) g.val := by
        rw [← SgnLin.map_bas, piL_proj_map]
        exact congrArg _ (piL_proj_gen g)
      rw [h1, h2, h3, h4, Bool.and_false, σ_false, one_smul, LinearMap.map_smul₂, map_smul,
        ← GrOperad.map_comp_canon, GrOperad.map_refl]
    · intro pq hpq hne
      by_cases h1 : nVert pq.1 = 1
      · by_cases h2 : nVert pq.2 = 1
        · have hu := FreeGr.fact_corolla_unique b₀ h1 h2 hpa hpb (FreeGr.mem_fib.1 hpq)
          exact absurd (Prod.ext hu.1 hu.2) hne
        · rw [piL_proj_bas_of_ne _ h2, map_zero, smul_zero]
      · rw [piL_proj_bas_of_ne _ h1, smul_zero, LinearMap.map_zero₂, smul_zero]
    · intro h
      exact absurd ((FreeGr.mem_fib (pq := (pa, pb))).2 rfl) h

/-- **A tree with two vertices is a relabelled composite of two corollas.** -/
lemma exists_corollas {A : Type} [Fintype A] [DecidableEq A] (t : Reg (TreeOfArity (BarT I)) A)
    (ht : nVert t = 2) :
    ∃ (k l : ℕ) (c : BarT I k) (g : BarT I l) (r : Fin k) (e : Without (Fin k) r ⊕ Fin l ≃ A),
      SetOperad.map e (SetOperad.comp r (Reg.std (corolla c)) (Reg.std (corolla g))) = t := by
  rw [nVert_eq] at ht
  obtain ⟨s', p, l, g, hp, hw, hs⟩ := exists_graft_corolla (t := treeOf t) (by omega)
  obtain ⟨k, c, hc⟩ := eq_corolla_of_weight (t := s') (by omega)
  subst hc
  have hpk : p < k := by
    have hk : (Tree.node c (TreeOfArity.leaves k)).arity = k := (corolla c).2
    rwa [hk] at hp
  refine ⟨k, l, c, g, ⟨p, hpk⟩, ?_⟩
  refine FreeGr.exists_map_eq ?_
  rw [treeOf_comp, hs]
  show (corolla c).1.graft ((LinOrd.std k).rank ⟨p, hpk⟩) (corolla g).1 = _
  rw [LinOrd.rank_std]
  rfl

lemma star_piF_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) (y : FreeGr R (grGenPar R (BarGen I)) A) :
    ConvOp.toLin ((GrOperad.Inv.star R _ (piF I) (piF I)).1 B) (GrOperad.map (R := R) e y)
      = GrOperad.map (R := R) (P := P) e
          (ConvOp.toLin ((GrOperad.Inv.star R _ (piF I) (piF I)).1 A) y) := by
  rw [← GrOperad.Inv.map_apply (GrOperad.Inv.star R _ (piF I) (piF I)) e]
  show GrOperad.map (R := R) e (ConvOp.toLin _ (GrOperad.map (R := R) e.symm
    (GrOperad.map (R := R) e y))) = _
  rw [map_symm_map]
  rfl

lemma piL_barD_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) (y : FreeGr R (grGenPar R (BarGen I)) A) :
    piL I B ((𝒥).proj B (barD (barMerge I) (grGenPar R (BarGen I)) R B
        (GrOperad.map (R := R) e y)))
      = GrOperad.map (R := R) e
          (piL I A ((𝒥).proj A (barD (barMerge I) (grGenPar R (BarGen I)) R A y))) := by
  rw [← map_barD, piL_proj_map]

/-- **The convolution square of the universal twisting morphism is minus the universal twisting
morphism after the bar differential**, on the trees decorated by homogeneous elements. -/
theorem star_piF_eq (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0) {A : Type} [Fintype A] [DecidableEq A]
    (y : FreeGr R (grGenPar R (BarGen I)) A) :
    ConvOp.toLin ((GrOperad.Inv.star R _ (piF I) (piF I)).1 A) y
      = -piL I A ((𝒥).proj A (barD (barMerge I) (grGenPar R (BarGen I)) R A y)) := by
  induction y using FreeGr.induction_bas with
  | zero =>
    rw [map_zero, map_zero, map_zero, map_zero, neg_zero]
    rfl
  | add x y hx hy =>
    rw [map_add, hx, hy, map_add, map_add, map_add, neg_add]
    rfl
  | bas a t =>
    rw [map_smul, map_smul, map_smul, map_smul, ← smul_neg]
    congr 1
    by_cases ht : nVert t = 2
    · obtain ⟨k, l, c, g, r, e, rfl⟩ := exists_corollas t ht
      have e1 : SgnLin.bas (treeSgn (grGenPar R (BarGen I))) R
          (SetOperad.map e (SetOperad.comp r (Reg.std (corolla c)) (Reg.std (corolla g))))
          = GrOperad.map (R := R) e (SgnLin.bas (treeSgn (grGenPar R (BarGen I))) R
              (SetOperad.comp r (Reg.std (corolla c)) (Reg.std (corolla g)))) :=
        (SgnLin.map_bas e _).symm
      have e2 := piL_barD_map (I := I) e (SgnLin.bas (treeSgn (grGenPar R (BarGen I))) R
        (SetOperad.comp r (Reg.std (corolla c)) (Reg.std (corolla g))))
      rw [piL_barD_corollas c g r] at e2
      rw [e1, star_piF_map e, star_piF_corollas hI0 c g r, e2, map_smul, map_smul, ← neg_smul]
      congr 1
      generalize c.1.2 = b
      cases b <;> simp
    · rw [star_piF_bas_of_ne t ht, piL_barD_bas_of_ne t ht, neg_zero]
      rfl

variable (I) in
/-- **The Maurer–Cartan equation of the universal twisting morphism**: `π ∘ d + π ⋆ π = 0`,
`P` having the zero differential. -/
theorem mc_pi (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0) :
    GrOperad.Inv.appDer (ConvOp.postDer (C := BarCoop I)
        (DGOperad.toDer (R := R) (P := ZeroDG R P))) (pi I)
      - GrOperad.Inv.appDer (ConvOp.preDer (C := BarCoop I) (P := ZeroDG R P)) (pi I)
      + GrOperad.Inv.star R _ (pi I) (pi I) = 0 := by
  refine Subtype.ext (funext fun A => funext fun _ => funext fun _ => ConvOp.ext fun x => ?_)
  obtain ⟨y, rfl⟩ := (𝒥).proj_surjective A x
  have hpi : GrOperad.tw (R := R) true ((pi I).1 A) = -(pi I).1 A := by
    rw [GrOperad.tw_hom true (isPar_pi A), Bool.and_self, σ_true, neg_one_smul]
  show ConvOp.toLin ((GrOperad.Inv.appDer (ConvOp.postDer (C := BarCoop I)
        (DGOperad.toDer (R := R) (P := ZeroDG R P))) (pi I)).1 A) ((𝒥).proj A y)
      - ConvOp.toLin (GrOperad.tw (R := R) true ((pi I).1 A))
          (DGCooperad.d (R := R) (C := BarCoop I) ((𝒥).proj A y))
      + ConvOp.toLin ((GrOperad.Inv.star R _ (pi I) (pi I)).1 A) ((𝒥).proj A y) = 0
  rw [ConvOp.appDer_postDer_apply, hpi, star_proj, star_piF_eq hI0]
  show (0 : P A) - (-(piL I A ((𝒥).proj A (barD (barMerge I) _ R A y))))
    + -piL I A ((𝒥).proj A (barD (barMerge I) _ R A y)) = 0
  abel

variable (I) in
/-- **The universal twisting morphism** `π : B(P, I) → P`, a twisting morphism, `I` having no
operations without inputs. -/
noncomputable def twisting (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0) :
    TwistingDG R (BarCoop I) (ZeroDG R P) :=
  ⟨pi I, isPar_pi, killsUnit_pi, mc_pi I hI0⟩

variable (I) in
/-- **The counit of the bar–cobar adjunction**: the morphism of dg operads `ΩB(P, I) → P`, by the
cobar adjunction. -/
noncomputable def counit (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0) :
    CobarDGHom R (BarCoop I) (ZeroDG R P) :=
  CobarDG.homEquiv.symm (twisting I hI0)

/-- The counit `ΩB(P, I) → P` desuspends the cogenerators. -/
lemma counit_ιL (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0) {A : Type} [Fintype A] [DecidableEq A]
    (x : BarCoop I A) : (counit I hI0).1.app A (Cobar.ιL R (BarCoop I) A x) = piL I A x :=
  Cobar.homOf_ιL _ _ _ x

end Bar

end MC

/-! ## Morphisms into the bar construction -/

section ToBar

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {I : GrOperadIdeal R P}
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [DGCooperad R C]
  [GrCooperad.Coaug R C]

namespace Bar

/-- The composite `π ∘ f` of a morphism into the bar construction with the universal twisting
morphism. -/
noncomputable def twOfHom (f : DGCooperadHom R C (BarCoop I)) :
    GrOperad.Inv R (ConvOp R C (ZeroDG R P)) :=
  GrOperad.Inv.appHom (ConvOp.preHom (P := ZeroDG R P) f.toGrCooperadHom) (pi I)

omit [GrCooperad.Coaug R C] in
lemma twOfHom_apply (f : DGCooperadHom R C (BarCoop I)) {A : Type} [Fintype A] [DecidableEq A]
    (x : C A) : ConvOp.toLin ((twOfHom f).1 A) x = piL I A (f.app A x) := rfl

variable (I) in
/-- **Morphisms of dg cooperads into the bar construction preserving the coaugmentations are
twisting morphisms after the universal twisting morphism**: `π ∘ f` satisfies the Maurer–Cartan
equation, `f` commuting with the decompositions and the differentials. -/
noncomputable def twistingOfHom (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0)
    (f : DGCooperadHom R C (BarCoop I))
    (hf : f.app Unit (GrCooperad.Coaug.one (R := R)) = GrCooperad.Coaug.one (R := R)) :
    TwistingDG R C (ZeroDG R P) := by
  refine ⟨twOfHom f, fun A _ _ => ?_, fun A _ _ x hx => ?_, ?_⟩
  · show ConvOp.parC true ((ConvOp.preHom (P := ZeroDG R P) f.toGrCooperadHom).app A
      ((pi I).1 A)) = _
    rw [← ConvOp.par_def, ← (ConvOp.preHom (P := ZeroDG R P) f.toGrCooperadHom).app_par,
      isPar_pi (I := I) A]
    rfl
  · rw [twOfHom_apply]
    refine killsUnit_pi (I := I) A (f.app A x) ?_
    refine Submodule.span_induction
      (p := fun x _ => f.app A x ∈ GrCooperad.unitSpan R (BarCoop I) A) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨e, rfl⟩
      beta_reduce
      rw [f.app_map, hf]
      exact GrCooperad.map_one_mem e
    · beta_reduce
      rw [map_zero]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      beta_reduce at hx hy ⊢
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    · intro a x _ hx
      beta_reduce at hx ⊢
      rw [map_smul]
      exact Submodule.smul_mem _ a hx
  · refine Subtype.ext (funext fun A => funext fun _ => funext fun _ => ConvOp.ext fun x => ?_)
    have hmc := congrArg (fun q : GrOperad.Inv R (ConvOp R (BarCoop I) (ZeroDG R P)) =>
      ConvOp.toLin (q.1 A) (f.app A x)) (mc_pi I hI0)
    have h2 : GrOperad.tw (R := R) true ((twOfHom f).1 A)
        = (ConvOp.preHom (P := ZeroDG R P) f.toGrCooperadHom).app A
            (GrOperad.tw (R := R) true ((pi I).1 A)) :=
      ((ConvOp.preHom (P := ZeroDG R P) f.toGrCooperadHom).app_tw true _).symm
    have h3 : GrOperad.Inv.star R _ (twOfHom f) (twOfHom f)
        = GrOperad.Inv.appHom (ConvOp.preHom (P := ZeroDG R P) f.toGrCooperadHom)
            (GrOperad.Inv.star R _ (pi I) (pi I)) :=
      (GrOperad.Inv.appHom_star _ _ _).symm
    show ConvOp.toLin ((GrOperad.Inv.appDer (ConvOp.postDer (C := C)
          (DGOperad.toDer (R := R) (P := ZeroDG R P))) (twOfHom f)).1 A) x
        - ConvOp.toLin (GrOperad.tw (R := R) true ((twOfHom f).1 A))
            (DGCooperad.d (R := R) (C := C) x)
        + ConvOp.toLin ((GrOperad.Inv.star R _ (twOfHom f) (twOfHom f)).1 A) x = 0
    rw [h2, h3, ConvOp.appDer_postDer_apply]
    show (0 : ZeroDG R P A) - ConvOp.toLin (GrOperad.tw (R := R) true ((pi I).1 A))
        (f.app A (DGCooperad.d (R := R) (C := C) x))
      + ConvOp.toLin ((GrOperad.Inv.star R _ (pi I) (pi I)).1 A) (f.app A x) = 0
    rw [f.app_d]
    exact hmc

end Bar

end ToBar

end Operad
