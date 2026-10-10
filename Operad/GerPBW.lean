/-
# The Gerstenhaber operad has at most `n!` operations of arity `n`

Work in progress.
-/
import Operad.PoisPBW
import Operad.GerOperad

universe u

namespace Operad

namespace GerDim

open STree PoisDim GerBV

/-! ## Planar trees of shuffle trees -/

/-- The Gerstenhaber generator of a Poisson generator. -/
def gg : PoisOp → GerGen 2
  | .mul => .mul
  | .bracket => .br

/-- **The planar tree** of a shuffle tree: the inputs of a transposed vertex are exchanged. -/
def pl : STree PE → Tree GerGen
  | leaf _ => .leaf
  | node (BinGen.op g, σ) c =>
    if σ = 1 then .node (gg g) (.cons (pl (c 0)) (.cons (pl (c 1)) .nil))
    else .node (gg g) (.cons (pl (c 1)) (.cons (pl (c 0)) .nil))

/-- **The planar word**: the leaves in the planar order. -/
def pw : STree PE → List ℕ
  | leaf a => [a]
  | node (BinGen.op _, σ) c => if σ = 1 then pw (c 0) ++ pw (c 1) else pw (c 1) ++ pw (c 0)

lemma pl_ndσ (g : PoisOp) (σ : Equiv.Perm (Fin 2)) (x y : STree PE) :
    pl (ndσ g σ x y) = if σ = 1 then .node (gg g) (.cons (pl x) (.cons (pl y) .nil))
      else .node (gg g) (.cons (pl y) (.cons (pl x) .nil)) := rfl

lemma pw_ndσ (g : PoisOp) (σ : Equiv.Perm (Fin 2)) (x y : STree PE) :
    pw (ndσ g σ x y) = if σ = 1 then pw x ++ pw y else pw y ++ pw x := rfl

/-- The planar tree has as many leaves as the planar word. -/
theorem arity_pl (t : STree PE) : (pl t).arity = (pw t).length := by
  induction t with
  | leaf a => rfl
  | node e c ih =>
    obtain ⟨⟨g⟩, σ⟩ := e
    rw [node_eq_ndσ, pl_ndσ, pw_ndσ]
    split_ifs
    · simp [ih 0, ih 1]
    · simp [ih 0, ih 1, add_comm]

/-- **The planar word is an ordering of the leaves.** -/
theorem coe_pw (t : STree PE) : (pw t : Multiset ℕ) = t.labels := by
  induction t with
  | leaf a => rfl
  | node e c ih =>
    obtain ⟨⟨g⟩, σ⟩ := e
    rw [node_eq_ndσ, labels_ndσ, ← ih 0, ← ih 1, pw_ndσ]
    split_ifs
    · rw [← Multiset.coe_add]
    · rw [← Multiset.coe_add, add_comm]

/-- **The planar word of a substitution.** -/
theorem pw_subst (t : STree PE) (xs : ℕ → STree PE) :
    pw (t.subst xs) = (pw t).flatMap fun a => pw (xs a) := by
  induction t with
  | leaf a => simp [pw]
  | node e c ih =>
    obtain ⟨⟨g⟩, σ⟩ := e
    rw [node_eq_ndσ, subst_ndσ, pw_ndσ, pw_ndσ]
    split_ifs <;> rw [List.flatMap_append, ih 0, ih 1]

lemma subst_update_of_notMem {t : STree PE} {a : ℕ} (h : a ∉ t.labels) (u : STree PE) :
    t.subst (Function.update leaf a u) = t := by
  conv_rhs => rw [← subst_leaf t]
  refine subst_congr _ fun b hb => ?_
  rw [Function.update_of_ne (fun e => h (by rw [← e]; exact hb))]

/-- **The planar tree of a substitution at one leaf** is a graft. -/
theorem pl_subst_update (s : STree PE) {a : ℕ} (ha : a ∈ pw s) (hn : (pw s).Nodup)
    (u : STree PE) :
    pl (s.subst (Function.update leaf a u)) = (pl s).graft ((pw s).idxOf a) (pl u) := by
  induction s with
  | leaf b =>
    obtain rfl : a = b := by simpa [pw] using ha
    simp [pl, pw]
  | node e c ih =>
    obtain ⟨⟨g⟩, σ⟩ := e
    rw [node_eq_ndσ, subst_ndσ, pl_ndσ, pl_ndσ]
    rw [node_eq_ndσ, pw_ndσ] at ha hn
    have hmem : ∀ i, a ∈ pw (c i) ↔ a ∈ (c i).labels := fun i => by
      rw [← Multiset.mem_coe, coe_pw]
    split_ifs at ha hn ⊢ with hσ
    · rw [pw_ndσ, if_pos hσ]
      rcases List.mem_append.1 ha with h | h
      · have h' : a ∉ (c 1).labels := fun h' =>
          List.disjoint_of_nodup_append hn h ((hmem 1).2 h')
        rw [subst_update_of_notMem h', ih 0 h (List.Nodup.of_append_left hn),
          List.idxOf_append_of_mem h, Tree.graft_node, Tree.graftF_cons_of_lt _
            (by rw [arity_pl]; exact List.idxOf_lt_length_of_mem h)]
      · have h' : a ∉ (c 0).labels := fun h' =>
          List.disjoint_of_nodup_append hn ((hmem 0).2 h') h
        have h'' : a ∉ pw (c 0) := fun h'' => h' ((hmem 0).1 h'')
        rw [subst_update_of_notMem h', ih 1 h (List.Nodup.of_append_right hn),
          List.idxOf_append_of_notMem h'', Tree.graft_node, Tree.graftF_cons_of_ge _
            (by rw [arity_pl]; omega), arity_pl, Nat.add_sub_cancel_left,
          Tree.graftF_cons_of_lt _ (by rw [arity_pl]; exact List.idxOf_lt_length_of_mem h)]
    · rw [pw_ndσ, if_neg hσ]
      rcases List.mem_append.1 ha with h | h
      · have h' : a ∉ (c 0).labels := fun h' =>
          List.disjoint_of_nodup_append hn h ((hmem 0).2 h')
        rw [subst_update_of_notMem h', ih 1 h (List.Nodup.of_append_left hn),
          List.idxOf_append_of_mem h, Tree.graft_node, Tree.graftF_cons_of_lt _
            (by rw [arity_pl]; exact List.idxOf_lt_length_of_mem h)]
      · have h' : a ∉ (c 1).labels := fun h' =>
          List.disjoint_of_nodup_append hn ((hmem 1).2 h') h
        have h'' : a ∉ pw (c 1) := fun h'' => h' ((hmem 1).1 h'')
        rw [subst_update_of_notMem h', ih 0 h (List.Nodup.of_append_right hn),
          List.idxOf_append_of_notMem h'', Tree.graft_node, Tree.graftF_cons_of_ge _
            (by rw [arity_pl]; omega), arity_pl, Nat.add_sub_cancel_left,
          Tree.graftF_cons_of_lt _ (by rw [arity_pl]; exact List.idxOf_lt_length_of_mem h)]

/-! ## Orders from words -/

/-- **The ranking of a finite set along a word listing it once.** -/
noncomputable def rk (l : List ℕ) {B : Finset ℕ} (h : l.Nodup ∧ ∀ a, a ∈ B ↔ a ∈ l) :
    ↥B ≃ Fin l.length :=
  Equiv.ofBijective (fun b => ⟨l.idxOf b.1, List.idxOf_lt_length_of_mem ((h.2 _).1 b.2)⟩) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun b b' e => Subtype.ext ((List.idxOf_inj ((h.2 _).1 b.2)).1
      (congrArg Fin.val e)), ?_⟩
    rw [Fintype.card_fin, Fintype.card_coe, ← List.toFinset_card_of_nodup h.1]
    congr 1
    ext a
    rw [h.2, List.mem_toFinset])

/-- **The linear order of a word.** -/
noncomputable def ordOf (l : List ℕ) {B : Finset ℕ} (h : l.Nodup ∧ ∀ a, a ∈ B ↔ a ∈ l) :
    Sym.LinOrd ↥B :=
  Sym.LinOrd.ofRank (rk l h)

lemma ordOf_lt (l : List ℕ) {B : Finset ℕ} (h : l.Nodup ∧ ∀ a, a ∈ B ↔ a ∈ l) (a b : ↥B) :
    (ordOf l h).lt a b ↔ l.idxOf a.1 < l.idxOf b.1 := Iff.rfl

lemma rank_ordOf (l : List ℕ) {B : Finset ℕ} (h : l.Nodup ∧ ∀ a, a ∈ B ↔ a ∈ l) (a : ↥B) :
    (ordOf l h).rank a = l.idxOf a.1 :=
  Sym.LinOrd.rank_ofRank _ a

lemma card_of_word {l : List ℕ} {B : Finset ℕ} (h : l.Nodup ∧ ∀ a, a ∈ B ↔ a ∈ l) :
    l.length = Fintype.card ↥B := by
  rw [Fintype.card_coe, ← List.toFinset_card_of_nodup h.1]
  congr 1
  ext a
  rw [h.2, List.mem_toFinset]

/-! ## Unsorting -/

/-- **The planar operation of a shuffle tree** with leaves `B`: its planar tree, the leaves ordered
by the planar word. -/
noncomputable def uv (t : STree PE) (B : Finset ℕ) (h : (pw t).Nodup ∧ ∀ a, a ∈ B ↔ a ∈ pw t) :
    Reg (TreeOfArity GerGen) ↥B :=
  (ordOf (pw t) h, ⟨TreeOfArity.toArr (pl t), by
    show (pl t).arity = _
    rw [arity_pl, card_of_word h]⟩)

lemma treeOf_uv (t : STree PE) (B : Finset ℕ) (h : (pw t).Nodup ∧ ∀ a, a ∈ B ↔ a ∈ pw t) :
    FreeGr.treeOf (uv t B h) = pl t := rfl

/-! ## Grafting -/

section Join

variable {B U C : Finset ℕ} {a : ℕ} (ha : a ∈ B) (hd : Disjoint (B.erase a) U)
  (hC : ∀ x, x ∈ C ↔ x ∈ B.erase a ∨ x ∈ U)

lemma mem_erase_of_without (x : Without ↥B ⟨a, ha⟩) : x.1.1 ∈ B.erase a :=
  Finset.mem_erase.2 ⟨fun e => x.2 (Subtype.ext e), x.1.2⟩

/-- **Joining the leaves** of a substitution at one leaf. -/
def joinEquiv : Without ↥B ⟨a, ha⟩ ⊕ ↥U ≃ ↥C where
  toFun
    | .inl x => ⟨x.1.1, (hC _).2 (Or.inl (mem_erase_of_without ha x))⟩
    | .inr y => ⟨y.1, (hC _).2 (Or.inr y.2)⟩
  invFun c := if h : c.1 ∈ U then .inr ⟨c.1, h⟩ else
    .inl ⟨⟨c.1, (Finset.mem_erase.1 (((hC _).1 c.2).resolve_right h)).2⟩, fun e =>
      (Finset.mem_erase.1 (((hC _).1 c.2).resolve_right h)).1 (congrArg Subtype.val e)⟩
  left_inv u := by
    rcases u with x | y
    · have hx : x.1.1 ∉ U := Finset.disjoint_left.1 hd (mem_erase_of_without ha x)
      show (if h : x.1.1 ∈ U then _ else _) = _
      rw [dif_neg hx]
    · show (if h : y.1 ∈ U then _ else _) = _
      rw [dif_pos y.2]
  right_inv c := by
    by_cases h : c.1 ∈ U
    · show (match (if h : c.1 ∈ U then _ else _ : Without ↥B ⟨a, ha⟩ ⊕ ↥U) with
        | .inl x => (⟨x.1.1, _⟩ : ↥C) | .inr y => ⟨y.1, _⟩) = c
      rw [dif_pos h]
    · show (match (if h : c.1 ∈ U then _ else _ : Without ↥B ⟨a, ha⟩ ⊕ ↥U) with
        | .inl x => (⟨x.1.1, _⟩ : ↥C) | .inr y => ⟨y.1, _⟩) = c
      rw [dif_neg h]

lemma joinEquiv_symm_inr (c : ↥C) (h : c.1 ∈ U) :
    (joinEquiv ha hd hC).symm c = .inr ⟨c.1, h⟩ := dif_pos h

lemma joinEquiv_symm_inl (c : ↥C) (h : c.1 ∉ U) :
    ∃ x, (joinEquiv ha hd hC).symm c = .inl x ∧ x.1.1 = c.1 := ⟨_, dif_neg h, rfl⟩

end Join

lemma pw_subst_update_eq {s : STree PE} {a : ℕ} {l1 l2 : List ℕ} (h : pw s = l1 ++ a :: l2)
    (hn : (pw s).Nodup) (u : STree PE) :
    pw (s.subst (Function.update leaf a u)) = l1 ++ pw u ++ l2 := by
  have key : ∀ l : List ℕ, a ∉ l → (l.flatMap fun b => pw (Function.update leaf a u b)) = l := by
    intro l hl
    induction l with
    | nil => rfl
    | cons b l ih =>
      rw [List.flatMap_cons,
        Function.update_of_ne (fun e => hl (by rw [← e]; exact List.mem_cons_self)),
        ih (fun h => hl (List.mem_cons_of_mem _ h))]
      rfl
  rw [h] at hn
  have h1 : a ∉ l1 := fun h1 => List.disjoint_of_nodup_append hn h1 List.mem_cons_self
  have h2 : a ∉ l2 := (List.nodup_cons.1 hn.of_append_right).1
  rw [pw_subst, h, List.flatMap_append, List.flatMap_cons, Function.update_self, key l1 h1,
    key l2 h2, List.append_assoc]

/-- **Unsorting a substitution at one leaf** is the composite of the planar operations. -/
theorem uv_subst_update {s u : STree PE} {B U C : Finset ℕ} {a : ℕ}
    (hs : (pw s).Nodup ∧ ∀ x, x ∈ B ↔ x ∈ pw s) (hu : (pw u).Nodup ∧ ∀ x, x ∈ U ↔ x ∈ pw u)
    (ha : a ∈ B) (hd : Disjoint (B.erase a) U) (hC : ∀ x, x ∈ C ↔ x ∈ B.erase a ∨ x ∈ U)
    (h' : (pw (s.subst (Function.update leaf a u))).Nodup ∧
      ∀ x, x ∈ C ↔ x ∈ pw (s.subst (Function.update leaf a u))) :
    uv (s.subst (Function.update leaf a u)) C h' =
      SetOperad.map (joinEquiv ha hd hC)
        (SetOperad.comp (⟨a, ha⟩ : ↥B) (uv s B hs) (uv u U hu)) := by
  obtain ⟨l1, l2, hl⟩ := List.append_of_mem ((hs.2 a).1 ha)
  have hw := pw_subst_update_eq hl hs.1 u
  have hn := hs.1
  rw [hl] at hn
  have ha1 : a ∉ l1 := fun h1 => List.disjoint_of_nodup_append hn h1 List.mem_cons_self
  have hidx_a : (pw s).idxOf a = l1.length := by
    rw [hl, List.idxOf_append_of_notMem ha1, List.idxOf_cons_self, Nat.add_zero]
  refine Reg.ext ?_ ?_
  · -- the orders
    have F : ∀ c : ↥C, (c.1 ∈ U ∧ (pw (s.subst (Function.update leaf a u))).idxOf c.1 =
          l1.length + (pw u).idxOf c.1 ∧ (pw u).idxOf c.1 < (pw u).length) ∨
        (c.1 ∉ U ∧ (((pw s).idxOf c.1 < l1.length ∧
          (pw (s.subst (Function.update leaf a u))).idxOf c.1 = (pw s).idxOf c.1) ∨
          (l1.length < (pw s).idxOf c.1 ∧
            (pw (s.subst (Function.update leaf a u))).idxOf c.1 + 1 =
              (pw s).idxOf c.1 + (pw u).length))) := fun c => by
      rw [hw, hl]
      by_cases hcU : c.1 ∈ U
      · have hcu : c.1 ∈ pw u := (hu.2 _).1 hcU
        have hc1 : c.1 ∉ l1 := fun h1 => Finset.disjoint_left.1 hd (Finset.mem_erase.2
          ⟨fun e => ha1 (e ▸ h1), (hs.2 _).2 (by rw [hl]; exact List.mem_append_left _ h1)⟩) hcU
        refine Or.inl ⟨hcU, ?_, List.idxOf_lt_length_of_mem hcu⟩
        rw [List.append_assoc, List.idxOf_append_of_notMem hc1, List.idxOf_append_of_mem hcu]
      · refine Or.inr ⟨hcU, ?_⟩
        have hcB := ((hC _).1 c.2).resolve_right hcU
        obtain ⟨hca, hcB⟩ := Finset.mem_erase.1 hcB
        have hcs : c.1 ∈ l1 ++ a :: l2 := by rw [← hl]; exact (hs.2 _).1 hcB
        have hcu : c.1 ∉ pw u := fun h => hcU ((hu.2 _).2 h)
        rcases List.mem_append.1 hcs with h1 | h2
        · refine Or.inl ⟨?_, ?_⟩
          · rw [List.idxOf_append_of_mem h1]
            exact List.idxOf_lt_length_of_mem h1
          · rw [List.append_assoc, List.idxOf_append_of_mem h1, List.idxOf_append_of_mem h1]
        · have h2' : c.1 ∈ l2 := (List.mem_cons.1 h2).resolve_left hca
          have hc1 : c.1 ∉ l1 := fun h1 => List.disjoint_of_nodup_append hn h1 h2
          refine Or.inr ⟨?_, ?_⟩
          · rw [List.idxOf_append_of_notMem hc1, List.idxOf_cons_ne _ (Ne.symm hca)]
            omega
          · rw [List.append_assoc, List.idxOf_append_of_notMem hc1,
              List.idxOf_append_of_notMem hcu, List.idxOf_append_of_notMem hc1,
              List.idxOf_cons_ne _ (Ne.symm hca)]
            omega
    refine Sym.LinOrd.ext fun x y => ?_
    show (ordOf _ h').lt x y ↔ (Sym.LinOrd.map (joinEquiv ha hd hC)
      (Sym.LinOrd.comp ⟨a, ha⟩ (ordOf (pw s) hs) (ordOf (pw u) hu))).lt x y
    rw [Sym.LinOrd.map_lt, Sym.LinOrd.comp_lt, ordOf_lt]
    rcases F x with ⟨hxU, hx1, hx2⟩ | ⟨hxU, hx⟩ <;> rcases F y with ⟨hyU, hy1, hy2⟩ | ⟨hyU, hy⟩
    · rw [joinEquiv_symm_inr ha hd hC x hxU, joinEquiv_symm_inr ha hd hC y hyU,
        Sym.LinOrd.compLt_inr_inr, ordOf_lt]
      dsimp only
      omega
    · obtain ⟨y', hy', hyy⟩ := joinEquiv_symm_inl ha hd hC y hyU
      rw [joinEquiv_symm_inr ha hd hC x hxU, hy', Sym.LinOrd.compLt_inr_inl, ordOf_lt, hyy,
        hidx_a]
      omega
    · obtain ⟨x', hx', hxx⟩ := joinEquiv_symm_inl ha hd hC x hxU
      rw [joinEquiv_symm_inr ha hd hC y hyU, hx', Sym.LinOrd.compLt_inl_inr, ordOf_lt, hxx,
        hidx_a]
      omega
    · obtain ⟨x', hx', hxx⟩ := joinEquiv_symm_inl ha hd hC x hxU
      obtain ⟨y', hy', hyy⟩ := joinEquiv_symm_inl ha hd hC y hyU
      rw [hx', hy', Sym.LinOrd.compLt_inl_inl, ordOf_lt, hxx, hyy]
      omega
  · -- the trees
    refine TreeOfArity.arr_ext ?_
    show pl _ = (NSSetOperad.Arr.comp (TreeOfArity.toArr (pl s)) ((ordOf (pw s) hs).rank ⟨a, ha⟩)
      (TreeOfArity.toArr (pl u))).2.1
    rw [TreeOfArity.arr_comp_tree _ _ (by
        show _ < (pl s).arity
        rw [rank_ordOf, arity_pl]
        exact List.idxOf_lt_length_of_mem ((hs.2 a).1 ha)), rank_ordOf,
      pl_subst_update s ((hs.2 a).1 ha) hs.1]
    rfl

/-! ## Operations realized up to units -/

section Realize

variable (R : Type u) [CommRing R] {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type}
  [SetOperad S] (δ : SetOperadHom S SgnD)

/-- **A function realized by the twisted linearization**, up to units: a linear map preserving
every ideal and sending each operation to a unit multiple of its image. -/
def Realizes {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (F : S A → S B) : Prop :=
  ∃ L : SgnLin R δ A →ₗ[R] SgnLin R δ B,
    (∀ I : GrOperadIdeal R (SgnLin R δ), ∀ x ∈ I.sub A, L x ∈ I.sub B) ∧
      ∀ s, ∃ c : R, IsUnit c ∧ L (Finsupp.single s 1) = Finsupp.single (F s) c

variable {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype D]
  [DecidableEq D]

lemma realizes_id : Realizes R δ (id : S A → S A) :=
  ⟨LinearMap.id, fun _ _ hx => hx, fun _ => ⟨1, isUnit_one, rfl⟩⟩

variable {R δ} in
lemma Realizes.comp {G : S B → S D} {F : S A → S B} (hG : Realizes R δ G)
    (hF : Realizes R δ F) : Realizes R δ (G ∘ F) := by
  obtain ⟨LG, hG1, hG2⟩ := hG
  obtain ⟨LF, hF1, hF2⟩ := hF
  refine ⟨LG ∘ₗ LF, fun I x hx => hG1 I _ (hF1 I x hx), fun s => ?_⟩
  obtain ⟨c, hc, h⟩ := hF2 s
  obtain ⟨d, hd, h'⟩ := hG2 (F s)
  refine ⟨c * d, hc.mul hd, ?_⟩
  rw [LinearMap.comp_apply, h]
  calc LG (Finsupp.single (F s) c) = LG (c • Finsupp.single (F s) 1) :=
        congrArg LG (Finsupp.smul_single_one _ _).symm
    _ = c • LG (Finsupp.single (F s) 1) := LG.map_smul c _
    _ = _ := by rw [h']; exact Finsupp.smul_single c _ d

lemma realizes_map (e : A ≃ B) : Realizes R δ (SetOperad.map (S := S) e) :=
  ⟨GrOperad.map (R := R) e, fun I _ hx => I.map_mem e hx, fun s =>
    ⟨1, isUnit_one, Lin.mapL_single e s 1⟩⟩

lemma isUnit_σ (b : Bool) : IsUnit (σ R b) := IsUnit.of_mul_eq_one _ (σ_mul_self R b)

lemma realizes_comp_left (i : A) (y : S B) :
    Realizes R δ (fun x : S A => SetOperad.comp i x y) :=
  ⟨(SgnLin.compT R δ i).flip (Finsupp.single y 1), fun I x hx => I.comp_mem_left i _ hx,
    fun s => ⟨_, (isUnit_σ R _).mul (by rw [mul_one]; exact isUnit_one),
      SgnLin.compT_single i s y 1 1⟩⟩

lemma realizes_comp_right (i : A) (x : S A) :
    Realizes R δ (fun y : S B => SetOperad.comp i x y) :=
  ⟨SgnLin.compT R δ i (Finsupp.single x 1), fun I y hy => I.comp_mem_right i _ hy,
    fun s => ⟨_, (isUnit_σ R _).mul (by rw [mul_one]; exact isUnit_one),
      SgnLin.compT_single i x s 1 1⟩⟩

end Realize

/-! ## Relabelling and transport of the leaves -/

lemma pl_relabel (t : STree PE) (h : ℕ → ℕ) : pl (t.relabel h) = pl t := by
  induction t with
  | leaf a => rfl
  | node e c ih =>
    obtain ⟨⟨g⟩, σ⟩ := e
    simp only [STree.relabel] at ih ⊢
    rw [node_eq_ndσ, subst_ndσ, pl_ndσ, pl_ndσ, ih 0, ih 1]

lemma pw_relabel (t : STree PE) (h : ℕ → ℕ) : pw (t.relabel h) = (pw t).map h := by
  rw [STree.relabel, pw_subst]
  induction pw t with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, ih]; rfl

lemma idxOf_map_of_injOn {l : List ℕ} {h : ℕ → ℕ} (hi : ∀ x ∈ l, ∀ y ∈ l, h x = h y → x = y)
    {a : ℕ} (ha : a ∈ l) : (l.map h).idxOf (h a) = l.idxOf a := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    by_cases hb : b = a
    · subst hb
      rw [List.map_cons, List.idxOf_cons_self, List.idxOf_cons_self]
    · have hab : h b ≠ h a := fun e => hb (hi b List.mem_cons_self a ha e)
      rw [List.map_cons, List.idxOf_cons_ne _ hab, List.idxOf_cons_ne _ hb,
        ih (fun x hx y hy => hi x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
          ((List.mem_cons.1 ha).resolve_left (Ne.symm hb))]

/-- **Relabelling the leaves** along a function injective on them. -/
noncomputable def relEquiv (A : Finset ℕ) (h : ℕ → ℕ) (hi : Set.InjOn h ↑A) :
    ↥A ≃ ↥(A.image h) :=
  Equiv.ofBijective (fun a => ⟨h a.1, Finset.mem_image_of_mem h a.2⟩)
    ⟨fun a b e => Subtype.ext (hi a.2 b.2 (congrArg Subtype.val e)), fun c => by
      obtain ⟨a, ha, e⟩ := Finset.mem_image.1 c.2
      exact ⟨⟨a, ha⟩, Subtype.ext e⟩⟩

lemma relEquiv_apply (A : Finset ℕ) (h : ℕ → ℕ) (hi : Set.InjOn h ↑A) (a : ↥A) :
    (relEquiv A h hi a).1 = h a.1 := rfl

/-- **Unsorting a relabelled tree** relabels the planar operation. -/
theorem uv_relabel {t : STree PE} {A : Finset ℕ} {h : ℕ → ℕ} (hi : Set.InjOn h ↑A)
    (ht : (pw t).Nodup ∧ ∀ x, x ∈ A ↔ x ∈ pw t)
    (h' : (pw (t.relabel h)).Nodup ∧ ∀ x, x ∈ A.image h ↔ x ∈ pw (t.relabel h)) :
    uv (t.relabel h) (A.image h) h' = SetOperad.map (relEquiv A h hi) (uv t A ht) := by
  refine Reg.ext ?_ ?_
  · refine Sym.LinOrd.ext fun x y => ?_
    show (ordOf _ h').lt x y ↔ (Sym.LinOrd.map (relEquiv A h hi) (ordOf (pw t) ht)).lt x y
    rw [Sym.LinOrd.map_lt, ordOf_lt, ordOf_lt]
    have hinj : ∀ u ∈ pw t, ∀ v ∈ pw t, h u = h v → u = v := fun u hu v hv e =>
      hi ((ht.2 u).2 hu) ((ht.2 v).2 hv) e
    have hx : x.1 = h ((relEquiv A h hi).symm x).1 := by
      rw [← relEquiv_apply A h hi, Equiv.apply_symm_apply]
    have hy : y.1 = h ((relEquiv A h hi).symm y).1 := by
      rw [← relEquiv_apply A h hi, Equiv.apply_symm_apply]
    rw [pw_relabel, hx, hy, idxOf_map_of_injOn hinj ((ht.2 _).1 (Subtype.property _)),
      idxOf_map_of_injOn hinj ((ht.2 _).1 (Subtype.property _))]
  · refine TreeOfArity.arr_ext ?_
    exact pl_relabel t h

/-- **Unsorting along an equality of leaf sets.** -/
theorem uv_cast {t : STree PE} {B B' : Finset ℕ} (hB : ∀ x, x ∈ B ↔ x ∈ B')
    (ht : (pw t).Nodup ∧ ∀ x, x ∈ B ↔ x ∈ pw t) (h' : (pw t).Nodup ∧ ∀ x, x ∈ B' ↔ x ∈ pw t) :
    uv t B' h' = SetOperad.map (Equiv.subtypeEquivRight hB) (uv t B ht) :=
  Reg.ext (Sym.LinOrd.ext fun _ _ => Iff.rfl) rfl

lemma uv_congr {t t' : STree PE} (e : t = t') {B : Finset ℕ}
    (h : (pw t).Nodup ∧ ∀ x, x ∈ B ↔ x ∈ pw t) (h' : (pw t').Nodup ∧ ∀ x, x ∈ B ↔ x ∈ pw t') :
    uv t B h = uv t' B h' := by
  subst e
  rfl

lemma okV {t : STree PE} (hv : Valid t) {B : Finset ℕ} (hB : lset t = B) :
    (pw t).Nodup ∧ ∀ x, x ∈ B ↔ x ∈ pw t :=
  ⟨by rw [← Multiset.coe_nodup, coe_pw]; exact hv.nodup, fun x => by
    rw [← hB, mem_lset, ← coe_pw, Multiset.mem_coe]⟩

/-! ## Substituting at several leaves -/

variable (R : Type u) [CommRing R]

/-- **Unsorting a substitution at several leaves** is a fixed realized function of the unsorted
tree. -/
theorem uv_subst_on {A : Finset ℕ} {ys : ℕ → STree PE} (hys : ∀ b ∈ A, Valid (ys b))
    (hfirst : ∀ b ∈ A, (ys b).first = b)
    (hdisj : ∀ b ∈ A, ∀ b' ∈ A, b ≠ b' → Disjoint (lset (ys b)) (lset (ys b'))) :
    ∀ S ⊆ A, ∃ Θ : Reg (TreeOfArity GerGen) ↥A →
        Reg (TreeOfArity GerGen) ↥(A.biUnion fun b => lset (substOn S ys b)),
      Realizes R (FreeGr.treeSgn gerPar) Θ ∧
      ∀ s : STree PE, Valid s → lset s = A → ∀ h h',
        uv (s.subst (substOn S ys)) _ h' = Θ (uv s A h) := by
  intro S hS
  induction S using Finset.induction_on with
  | empty =>
    have h0 : substOn (∅ : Finset ℕ) ys = leaf := funext fun b => substOn_of_notMem
      (Finset.notMem_empty b)
    have hA : ∀ x, x ∈ A ↔ x ∈ A.biUnion fun b => lset (substOn ∅ ys b) := fun x => by
      rw [h0]
      simp
    refine ⟨SetOperad.map (Equiv.subtypeEquivRight hA), realizes_map R _ _,
      fun s _ _ h h' => ?_⟩
    have e : s.subst (substOn ∅ ys) = s := by rw [h0, subst_leaf]
    rw [uv_congr e h' (by rw [e] at h'; exact h'), uv_cast hA h]
  | insert b S hb ih =>
    have hbA : b ∈ A := hS (Finset.mem_insert_self b S)
    obtain ⟨Θ, hΘr, hΘ⟩ := ih ((Finset.subset_insert b S).trans hS)
    -- the leaves of the substituted inputs
    have hmem : ∀ c ∈ A, c ∈ lset (ys c) := fun c hc => by
      have := first_mem (hys c hc).shuffle
      rw [hfirst c hc] at this
      exact mem_lset.2 this
    have hnot : ∀ c ∈ A, c ≠ b → b ∉ lset (ys c) := fun c hc hcb h =>
      Finset.disjoint_left.1 (hdisj c hc b hbA hcb) h (hmem b hbA)
    have hbL : b ∈ A.biUnion fun c => lset (substOn S ys c) := Finset.mem_biUnion.2 ⟨b, hbA, by
      rw [substOn_of_notMem hb, lset_leaf]
      exact Finset.mem_singleton_self b⟩
    have hdL : Disjoint ((A.biUnion fun c => lset (substOn S ys c)).erase b) (lset (ys b)) := by
      refine Finset.disjoint_left.2 fun n hn hn' => ?_
      obtain ⟨hnb, hn⟩ := Finset.mem_erase.1 hn
      obtain ⟨c, hc, hnc⟩ := Finset.mem_biUnion.1 hn
      by_cases hcS : c ∈ S
      · rw [substOn_of_mem hcS] at hnc
        exact Finset.disjoint_left.1 (hdisj c hc b hbA fun h => hb (h ▸ hcS)) hnc hn'
      · rw [substOn_of_notMem hcS, lset_leaf, Finset.mem_singleton] at hnc
        rw [hnc] at hnb hn'
        exact Finset.disjoint_left.1 (hdisj c hc b hbA hnb) (hmem c hc) hn'
    have hL' : (A.biUnion fun c => lset (substOn S ys c)).erase b ∪ lset (ys b) =
        A.biUnion fun c => lset (substOn (insert b S) ys c) := by
      ext n
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_biUnion]
      constructor
      · rintro (⟨hnb, c, hc, hn⟩ | hn)
        · refine ⟨c, hc, ?_⟩
          by_cases hcS : c ∈ S
          · rwa [substOn_of_mem (Finset.mem_insert_of_mem hcS), ← substOn_of_mem (ys := ys) hcS]
          · rw [substOn_of_notMem hcS, lset_leaf, Finset.mem_singleton] at hn
            have hc' : c ∉ insert b S := by
              rw [Finset.mem_insert, not_or]
              exact ⟨fun h => hnb (hn.trans h), hcS⟩
            rw [substOn_of_notMem hc', lset_leaf, hn]
            exact Finset.mem_singleton_self c
        · exact ⟨b, hbA, by rwa [substOn_of_mem (Finset.mem_insert_self b S)]⟩
      · rintro ⟨c, hc, hn⟩
        by_cases hcb : c = b
        · rw [hcb, substOn_of_mem (Finset.mem_insert_self b S)] at hn
          exact Or.inr hn
        · by_cases hcS : c ∈ S
          · rw [substOn_of_mem (Finset.mem_insert_of_mem hcS)] at hn
            refine Or.inl ⟨fun h => hnot c hc hcb (h ▸ hn), c, hc, ?_⟩
            rwa [substOn_of_mem hcS]
          · have hc' : c ∉ insert b S := by
              rw [Finset.mem_insert, not_or]
              exact ⟨hcb, hcS⟩
            rw [substOn_of_notMem hc', lset_leaf, Finset.mem_singleton] at hn
            refine Or.inl ⟨by rw [hn]; exact hcb, c, hc, ?_⟩
            rw [substOn_of_notMem hcS, lset_leaf, hn]
            exact Finset.mem_singleton_self c
    have hC : ∀ x, x ∈ A.biUnion (fun c => lset (substOn (insert b S) ys c)) ↔
        x ∈ (A.biUnion fun c => lset (substOn S ys c)).erase b ∨ x ∈ lset (ys b) := fun x => by
      rw [← hL', Finset.mem_union]
    have hyb := okV (hys b hbA) rfl
    refine ⟨SetOperad.map (joinEquiv hbL hdL hC) ∘
      (fun z => SetOperad.comp (⟨b, hbL⟩ : ↥(A.biUnion fun c => lset (substOn S ys c))) z
        (uv (ys b) (lset (ys b)) hyb)) ∘ Θ,
      (realizes_map R _ _).comp ((realizes_comp_left R _ _ _).comp hΘr), fun s hs hsA h h' => ?_⟩
    have hsub : ∀ c ∈ lset s, Valid (substOn S ys c) := fun c hc => by
      by_cases hcS : c ∈ S
      · rw [substOn_of_mem hcS]
        exact hys c (hsA ▸ hc)
      · rw [substOn_of_notMem hcS]
        exact valid_leaf c
    have hsubf : ∀ c ∈ lset s, (substOn S ys c).first = c := fun c hc => by
      by_cases hcS : c ∈ S
      · rw [substOn_of_mem hcS]
        exact hfirst c (hsA ▸ hc)
      · rw [substOn_of_notMem hcS, first_leaf]
    have hsubd : ∀ c ∈ lset s, ∀ c' ∈ lset s, c ≠ c' →
        Disjoint (lset (substOn S ys c)) (lset (substOn S ys c')) := by
      intro c hc c' hc' hcc'
      rw [hsA] at hc hc'
      by_cases hcS : c ∈ S <;> by_cases hc'S : c' ∈ S
      · rw [substOn_of_mem hcS, substOn_of_mem hc'S]
        exact hdisj c hc c' hc' hcc'
      · rw [substOn_of_mem hcS, substOn_of_notMem hc'S, lset_leaf, Finset.disjoint_singleton_right]
        exact Finset.disjoint_left.1 (hdisj c' hc' c hc (Ne.symm hcc')) (hmem c' hc')
      · rw [substOn_of_notMem hcS, substOn_of_mem hc'S, lset_leaf, Finset.disjoint_singleton_left]
        exact Finset.disjoint_left.1 (hdisj c hc c' hc' hcc') (hmem c hc)
      · rw [substOn_of_notMem hcS, substOn_of_notMem hc'S, lset_leaf, lset_leaf,
          Finset.disjoint_singleton]
        exact hcc'
    have hv₁ : Valid (s.subst (substOn S ys)) := hs.subst hsub hsubf hsubd
    have hl₁ : lset (s.subst (substOn S ys)) = A.biUnion fun c => lset (substOn S ys c) := by
      rw [lset_subst, hsA]
    have hsplit : s.subst (substOn (insert b S) ys) =
        (s.subst (substOn S ys)).subst (Function.update leaf b (ys b)) := by
      rw [subst_subst]
      refine subst_congr _ fun c hc => ?_
      show substOn (insert b S) ys c = (substOn S ys c).subst (Function.update leaf b (ys b))
      have hcA : c ∈ A := hsA ▸ mem_lset.2 hc
      by_cases hcb : c = b
      · rw [hcb, substOn_of_mem (Finset.mem_insert_self b S), substOn_of_notMem hb, subst_leaf',
          Function.update_self]
      · by_cases hcS : c ∈ S
        · rw [substOn_of_mem (Finset.mem_insert_of_mem hcS), substOn_of_mem hcS]
          conv_lhs => rw [← subst_leaf (ys c)]
          refine subst_congr _ fun n hn => (Function.update_of_ne ?_ _ _).symm
          rintro rfl
          exact hnot c hcA hcb (mem_lset.2 hn)
        · have hc' : c ∉ insert b S := by
            rw [Finset.mem_insert, not_or]
            exact ⟨hcb, hcS⟩
          rw [substOn_of_notMem hc', substOn_of_notMem hcS, subst_leaf',
            Function.update_of_ne hcb]
    have hb₁ : b ∈ lset (s.subst (substOn S ys)) := hl₁ ▸ hbL
    have hd₁ : Disjoint ((lset (s.subst (substOn S ys))).erase b) (lset (ys b)) := hl₁ ▸ hdL
    have h₁ := okV hv₁ hl₁
    rw [uv_congr hsplit h' (by rw [hsplit] at h'; exact h'),
      uv_subst_update h₁ hyb hbL hdL hC, hΘ s hs hsA h h₁]
    rfl

/-! ## Contexts -/

/-- **Unsorting respects contexts**: for a context `f` from the monomials on `A` to those on `B`,
the planar operation of `f g` is a fixed realized function of that of `g`. -/
theorem uv_ctx {A B : Finset ℕ} {f : SMono PE A → SMono PE B} (hf : IsSCtx f) (g₀ : SMono PE A) :
    ∃ F : Reg (TreeOfArity GerGen) ↥A → Reg (TreeOfArity GerGen) ↥B,
      Realizes R (FreeGr.treeSgn gerPar) F ∧
      ∀ g : SMono PE A, ∀ h h', uv (f g).1 B h' = F (uv g.1 A h) := by
  obtain ⟨T, p, xs, hp, hxs, hfx⟩ := hf
  -- the inputs are valid, with disjoint leaves
  have hU : ∀ g : SMono PE A, (g.1.subst xs).labels ≤ B.val := fun g => by
    rw [← (f g).labels_eq, hfx g]
    exact labels_get?_le (get?_replace hp _)
  have hnd := Multiset.nodup_of_le (hU g₀) B.nodup
  rw [labels_subst, g₀.labels_eq] at hnd
  have hvx : ∀ a ∈ A, Valid (xs a) := fun a ha =>
    ⟨hxs.shuffle a ha, (Multiset.nodup_bind.1 hnd).1 a ha⟩
  have hdx : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → Disjoint (lset (xs a)) (lset (xs a')) :=
    fun a ha a' ha' h => disjoint_lset_of_nodup_bind hnd ha ha' h
  -- the inputs moved to their least leaves
  set h : ℕ → ℕ := fun a => (xs a).first with hh
  have hmono : StrictMonoOn h ↑A := hxs.mono
  set ys := atFirst A xs with hys_def
  have hys : ∀ a ∈ A, ys (h a) = xs a := fun a ha => atFirst_first hmono.injOn ha
  set A' := A.image h with hA'
  have hysv : ∀ c ∈ A', Valid (ys c) := fun c hc => by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hc
    rw [hys a ha]
    exact hvx a ha
  have hysf : ∀ c ∈ A', (ys c).first = c := fun c hc => by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hc
    rw [hys a ha]
  have hysd : ∀ c ∈ A', ∀ c' ∈ A', c ≠ c' → Disjoint (lset (ys c)) (lset (ys c')) := by
    intro c hc c' hc' hcc'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 hc'
    rw [hys a ha, hys a' ha']
    exact hdx a ha a' ha' fun e => hcc' (congrArg h e)
  obtain ⟨Θ, hΘr, hΘ⟩ := uv_subst_on R hysv hysf hysd A' (Finset.Subset.refl _)
  have hsubst : ∀ g : SMono PE A, (g.1.relabel h).subst (substOn A' ys) = g.1.subst xs :=
    fun g => by
      rw [relabel_subst]
      refine subst_congr _ fun a ha => ?_
      have haA : a ∈ A := g.mem_labels.1 ha
      rw [substOn_of_mem (Finset.mem_image_of_mem h haA), hys a haA]
  have hlr : ∀ g : SMono PE A, lset (g.1.relabel h) = A' := fun g => by
    rw [lset_relabel, lset_smono]
  have hfg : ∀ g : SMono PE A, StrictMonoOn h ↑(lset g.1) := fun g => by
    rw [lset_smono]
    exact hmono
  have hLg : ∀ g : SMono PE A, lset (g.1.subst xs) = A'.biUnion fun c => lset (substOn A' ys c) :=
    fun g => by
    rw [← hsubst g, lset_subst, hlr g]
  have hinj : Set.InjOn h ↑A := hmono.injOn
  have hin : ∀ g : SMono PE A, ∀ hg hu,
      Θ (SetOperad.map (relEquiv A h hinj) (uv g.1 A hg)) =
        uv (g.1.subst xs) (A'.biUnion fun c => lset (substOn A' ys c)) hu := fun g hg hu => by
    have hr := okV (g.valid.relabel (hfg g)) (hlr g)
    rw [← uv_relabel hinj hg hr, ← hΘ (g.1.relabel h) (g.valid.relabel (hfg g)) (hlr g) hr
      (by rw [hsubst g]; exact hu)]
    exact uv_congr (hsubst g) _ _
  -- the outer part: grafting the substituted subtree at its least leaf
  obtain ⟨b, hb⟩ : ∃ b, (g₀.1.subst xs).first = b := ⟨_, rfl⟩
  obtain ⟨T', hT'⟩ : ∃ T', T.replace p (leaf b) = T' := ⟨_, rfl⟩
  have hUfirst : ∀ g : SMono PE A, (g.1.subst xs).first = b := fun g => by
    rw [← hb, first_subst g.isShuffle, first_subst g₀.isShuffle, g.first_eq g₀]
  have hUl : ∀ g : SMono PE A, (g.1.subst xs).labels = (g₀.1.subst xs).labels := fun g => by
    rw [labels_subst, labels_subst, g.labels_eq, g₀.labels_eq]
  have hUv : ∀ g : SMono PE A, Valid (g.1.subst xs) := fun g =>
    ⟨isShuffle_get? (p := p) (f g).isShuffle (by rw [hfx g]; exact get?_replace hp _),
      Multiset.nodup_of_le (hU g) B.nodup⟩
  have hW : (T.replace p (g₀.1.subst xs)).replace p (leaf b) = T' := by
    rw [replace_replace, hT']
  have hlab := labels_replace (get?_replace hp (g₀.1.subst xs)) (leaf b)
  rw [hW, ← hfx g₀, (f g₀).labels_eq, labels_leaf] at hlab
  have hbU : b ∈ (g₀.1.subst xs).labels := hb ▸ first_mem (hUv g₀).shuffle
  obtain ⟨U', hU'⟩ := Multiset.exists_cons_of_mem hbU
  have hTU : T'.labels + U' = B.val := by
    have : b ::ₘ (T'.labels + U') = b ::ₘ B.val := by
      rw [← Multiset.add_cons, ← hU', hlab, ← Multiset.singleton_add, add_comm]
    exact (Multiset.cons_inj_right b).1 this
  have hBnd := B.nodup
  rw [← hTU, Multiset.nodup_add] at hBnd
  obtain ⟨hT'nd, -, hT'U'⟩ := hBnd
  have hT'get : T'.get? p = some (leaf b) := hT' ▸ get?_replace hp (leaf b)
  have hbT : b ∈ lset T' := mem_lset.2 (mem_labels_of_get? hT'get)
  have hT'v : Valid T' := ⟨by
    rw [← hW]
    exact isShuffle_replace (by rw [← hfx g₀]; exact (f g₀).isShuffle) (get?_replace hp _)
      (isShuffle_leaf b) ((first_leaf b).trans hb.symm), hT'nd⟩
  have hdT : ∀ g : SMono PE A, Disjoint ((lset T').erase b) (lset (g.1.subst xs)) := fun g => by
    refine Finset.disjoint_left.2 fun n hn hn' => ?_
    obtain ⟨hnb, hn⟩ := Finset.mem_erase.1 hn
    rw [mem_lset, hUl g, hU', Multiset.mem_cons] at hn'
    exact Multiset.disjoint_left.1 hT'U' (mem_lset.1 hn) (hn'.resolve_left hnb)
  have hsplit : ∀ g : SMono PE A,
      (f g).1 = T'.subst (Function.update leaf b (g.1.subst xs)) := fun g => by
    rw [subst_update hT'nd hT'get, subst_leaf, ← hT', replace_replace, hfx g]
  have hB : (lset T').erase b ∪ (A'.biUnion fun c => lset (substOn A' ys c)) = B := by
    rw [← hLg g₀, ← lset_subst_update hbT, ← hsplit g₀, lset_smono]
  have hC : ∀ x, x ∈ B ↔
      x ∈ (lset T').erase b ∨ x ∈ A'.biUnion fun c => lset (substOn A' ys c) := fun x => by
    rw [← hB, Finset.mem_union]
  have hdT' : Disjoint ((lset T').erase b) (A'.biUnion fun c => lset (substOn A' ys c)) :=
    hLg g₀ ▸ hdT g₀
  have hT'ok := okV hT'v rfl
  refine ⟨SetOperad.map (joinEquiv hbT hdT' hC) ∘
      (fun z => SetOperad.comp (⟨b, hbT⟩ : ↥(lset T')) (uv T' (lset T') hT'ok) z) ∘ Θ ∘
        SetOperad.map (relEquiv A h hinj),
    (realizes_map R _ _).comp ((realizes_comp_right R _ _ _).comp (hΘr.comp
      (realizes_map R _ _))), fun g hg h' => ?_⟩
  have hu := okV (hUv g) (hLg g)
  rw [uv_congr (hsplit g) h' (by rw [hsplit g] at h'; exact h'),
    uv_subst_update hT'ok hu hbT hdT' hC, ← hin g hg hu]
  rfl

/-! ## Sorting planar trees -/

/-- **Sorting a tree**: the children of each vertex ordered by their least leaves, the vertex
transposed when they are exchanged. -/
def sortT : STree PE → STree PE
  | leaf a => leaf a
  | node (BinGen.op g, σ) c =>
    if (sortT (c 0)).first < (sortT (c 1)).first then ndσ g σ (sortT (c 0)) (sortT (c 1))
    else ndσ g (σ * Equiv.swap 0 1) (sortT (c 1)) (sortT (c 0))

lemma sortT_ndσ (g : PoisOp) (σ : Equiv.Perm (Fin 2)) (x y : STree PE) :
    sortT (ndσ g σ x y) = if (sortT x).first < (sortT y).first then ndσ g σ (sortT x) (sortT y)
      else ndσ g (σ * Equiv.swap 0 1) (sortT y) (sortT x) := rfl

lemma swap_mul_ne_one : (1 : Equiv.Perm (Fin 2)) * Equiv.swap 0 1 ≠ 1 := by decide

lemma swap_mul_swap : (Equiv.swap (0 : Fin 2) 1) * Equiv.swap 0 1 = 1 := by decide

/-- Sorting keeps the planar tree. -/
theorem pl_sortT (t : STree PE) : pl (sortT t) = pl t := by
  induction t with
  | leaf a => rfl
  | node e c ih =>
    obtain ⟨⟨g⟩, σ⟩ := e
    rw [node_eq_ndσ, sortT_ndσ]
    split_ifs
    · rw [pl_ndσ, pl_ndσ, ih 0, ih 1]
    · rcases perm2 σ with rfl | rfl
      · rw [pl_ndσ, pl_ndσ, if_neg swap_mul_ne_one, if_pos rfl, ih 0, ih 1]
      · rw [pl_ndσ, pl_ndσ, swap_mul_swap, if_pos rfl, if_neg swap_ne_one, ih 0, ih 1]

/-- Sorting keeps the planar word. -/
theorem pw_sortT (t : STree PE) : pw (sortT t) = pw t := by
  induction t with
  | leaf a => rfl
  | node e c ih =>
    obtain ⟨⟨g⟩, σ⟩ := e
    rw [node_eq_ndσ, sortT_ndσ]
    split_ifs
    · rw [pw_ndσ, pw_ndσ, ih 0, ih 1]
    · rcases perm2 σ with rfl | rfl
      · rw [pw_ndσ, pw_ndσ, if_neg swap_mul_ne_one, if_pos rfl, ih 0, ih 1]
      · rw [pw_ndσ, pw_ndσ, swap_mul_swap, if_pos rfl, if_neg swap_ne_one, ih 0, ih 1]

lemma labels_sortT (t : STree PE) : (sortT t).labels = t.labels := by
  rw [← coe_pw, ← coe_pw, pw_sortT]

lemma isShuffle_ndσ_of {g : PoisOp} {σ : Equiv.Perm (Fin 2)} {x y : STree PE}
    (hx : x.IsShuffle) (hy : y.IsShuffle) (hxy : x.first < y.first) :
    (ndσ g σ x y).IsShuffle := by
  refine ⟨by norm_num, fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i
    · exact hx
    · exact hy
  · fin_cases i <;> fin_cases j <;> simp_all

/-- **A sorted tree with distinct leaves is a shuffle tree.** -/
theorem isShuffle_sortT (t : STree PE) (hn : t.labels.Nodup) : (sortT t).IsShuffle := by
  induction t with
  | leaf a => trivial
  | node e c ih =>
    obtain ⟨⟨g⟩, σ⟩ := e
    rw [node_eq_ndσ] at hn ⊢
    rw [sortT_ndσ]
    rw [labels_ndσ] at hn
    obtain ⟨h0, h1, hd⟩ := Multiset.nodup_add.1 hn
    have s0 := ih 0 h0
    have s1 := ih 1 h1
    have hne : (sortT (c 0)).first ≠ (sortT (c 1)).first := fun e => by
      have m0 := first_mem s0
      have m1 := first_mem s1
      rw [labels_sortT] at m0 m1
      exact Multiset.disjoint_left.1 hd m0 (e ▸ m1)
    split_ifs with h
    · exact isShuffle_ndσ_of s0 s1 h
    · exact isShuffle_ndσ_of s1 s0 (lt_of_le_of_ne (not_lt.1 h) (Ne.symm hne))

/-! ## Planting planar trees -/

/-- The Poisson generator of a Gerstenhaber generator. -/
def pg : GerGen 2 → PoisOp
  | .mul => .mul
  | .br => .bracket

lemma gg_pg (e : GerGen 2) : gg (pg e) = e := by cases e <;> rfl

/-- **Planting a planar tree**: its leaves labelled by a word, its vertices untransposed. -/
def plant : Tree GerGen → List ℕ → STree PE
  | .leaf, w => leaf (w.headD 0)
  | .node e (.cons X (.cons Y .nil)), w =>
    ndσ (pg e) 1 (plant X (w.take X.arity)) (plant Y (w.drop X.arity))

theorem pl_plant : ∀ (X : Tree GerGen) (w : List ℕ), pl (plant X w) = X
  | .leaf, _ => rfl
  | .node e (.cons X (.cons Y .nil)), w => by
    rw [plant, pl_ndσ, if_pos rfl, pl_plant X, pl_plant Y, gg_pg]

theorem pw_plant : ∀ (X : Tree GerGen) (w : List ℕ), w.length = X.arity → pw (plant X w) = w
  | .leaf, w, h => by
    obtain ⟨a, rfl⟩ : ∃ a, w = [a] := List.length_eq_one_iff.1 h
    rfl
  | .node e (.cons X (.cons Y .nil)), w, h => by
    simp only [Tree.arity_node, Tree.arityF_cons, Tree.arityF_nil, Nat.add_zero] at h
    rw [plant, pw_ndσ, if_pos rfl, pw_plant X _ (by rw [List.length_take]; omega),
      pw_plant Y _ (by rw [List.length_drop]; omega), List.take_append_drop]

/-- **Every planar operation is the unsorting of a shuffle monomial.** -/
theorem uv_surjective (B : Finset ℕ) (x : Reg (TreeOfArity GerGen) ↥B) :
    ∃ m : SMono PE B, ∀ h, uv m.1 B h = x := by
  obtain ⟨L, ⟨⟨n, X, hX⟩, hn⟩⟩ := x
  simp only at hn
  set w : List ℕ := List.ofFn fun k : Fin (Fintype.card ↥B) => (L.toRank.symm k).1 with hw
  have hwn : w.Nodup := List.nodup_ofFn.2 fun k k' e =>
    L.toRank.symm.injective (Subtype.ext e)
  have hwm : ∀ a, a ∈ B ↔ a ∈ w := fun a => by
    rw [hw, List.mem_ofFn]
    exact ⟨fun ha => ⟨L.toRank ⟨a, ha⟩, by rw [Equiv.symm_apply_apply]⟩,
      fun ⟨k, e⟩ => e ▸ (L.toRank.symm k).2⟩
  have hwl : w.length = X.arity := by rw [hw, List.length_ofFn, hX, hn]
  have hpw : pw (sortT (plant X w)) = w := by rw [pw_sortT, pw_plant X w hwl]
  have hlab : (sortT (plant X w)).labels = B.val := by
    rw [← coe_pw, hpw]
    have : B = w.toFinset := Finset.ext fun a => by rw [hwm, List.mem_toFinset]
    rw [this, List.toFinset_val, List.Nodup.dedup hwn]
  have hsh : (sortT (plant X w)).IsShuffle := isShuffle_sortT _ (by
    rw [← coe_pw, pw_plant X w hwl]; exact Multiset.coe_nodup.2 hwn)
  refine ⟨⟨sortT (plant X w), hsh, hlab⟩, fun h => Reg.ext ?_ ?_⟩
  · refine Sym.LinOrd.ext fun a b => ?_
    show (ordOf _ h).lt a b ↔ L.lt a b
    have key : ∀ c : ↥B, w.idxOf c.1 = L.rank c := fun c => by
      have hc : L.rank c < w.length := by rw [hw, List.length_ofFn]; exact L.rank_lt_card c
      have e : w.get ⟨L.rank c, hc⟩ = c.1 := by
        have e0 : w.get ⟨L.rank c, hc⟩ = (L.toRank.symm ⟨L.rank c, L.rank_lt_card c⟩).1 := by
          simp only [w, List.get_eq_getElem, List.getElem_ofFn]
        rw [e0, show (⟨L.rank c, _⟩ : Fin (Fintype.card ↥B)) = L.toRank c from
          Fin.ext (Sym.LinOrd.toRank_apply L c).symm, Equiv.symm_apply_apply]
      rw [← e, List.get_idxOf hwn]
    rw [ordOf_lt, hpw, key, key, Sym.LinOrd.lt_iff_rank_lt]
  · refine TreeOfArity.arr_ext ?_
    show pl (sortT (plant X w)) = X
    rw [pl_sortT, pl_plant]

end GerDim

end Operad
