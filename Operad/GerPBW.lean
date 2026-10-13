/-
# The Gerstenhaber operad has at most `n!` operations of arity `n`

The free graded operad on the Gerstenhaber generators is the twisted linearization of planar
labelled trees: a basis vector is a planar tree with a linear order of its leaves, compositions
carrying Koszul signs. We transport the rewriting system of the Poisson operad
(`Operad.PoisDim.rules`) to it, up to units.

* **Unsorting** (`GerDim.uv`): a shuffle monomial of `Pois` gives a planar tree (`GerDim.pl`),
  the inputs of a transposed vertex exchanged, with the order of its planar word (`GerDim.pw`).
  Substitution at a leaf is grafting (`GerDim.uv_subst_update`), and every basis vector is unsorted
  from a shuffle monomial (`GerDim.uv_surjective`), by sorting and planting.
* **Realizations** (`GerDim.Realizes`): linear maps preserving all graded operad ideals and sending
  basis vectors to unit multiples of basis vectors. Relabellings and compositions are realizations,
  and so is every shuffle context, on the unsorted monomials (`GerDim.uv_ctx`).
* **Certificates in arity three** (`GerDim.cert`): for each rule of `Pois`, an element of the ideal
  of `Ger` whose leading term is a unit multiple of the unsorted leading monomial, the rest being
  unsorted smaller monomials.
* **Spanning** (`GerDim.span_vG`): by well-founded induction on the order of `Pois`, the classes
  of the unsorted normal monomials span `Ger`, so `dim Ger(n) ≤ n!`
  (`GerDim.finite_finrank_le`).
-/
import Operad.PoisPBW
import Operad.GerOperad

universe u

namespace Operad

namespace GerDim

open STree PoisDim GerBV
open Sym (insertEquiv)

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

/-! ## Operations of arity two and three -/

/-- The planar corolla. -/
abbrev cg (e : GerGen 2) : Tree GerGen := .node e (.cons .leaf (.cons .leaf .nil))

/-- `g (h (-, -), -)`. -/
abbrev tLp (g h : GerGen 2) : Tree GerGen := .node g (.cons (cg h) (.cons .leaf .nil))

/-- `g (-, h (-, -))`. -/
abbrev tRp (g h : GerGen 2) : Tree GerGen := .node g (.cons .leaf (.cons (cg h) .nil))

/-- An operation with two inputs, read in the order `π`. -/
def op2 (e : GerGen 2) (π : Equiv.Perm (Fin 2)) : Reg (TreeOfArity GerGen) (Fin 2) :=
  (Sym.LinOrd.map π (Sym.LinOrd.std 2), ⟨TreeOfArity.toArr (cg e), by
    show (cg e).arity = _
    rw [Fintype.card_fin]
    rfl⟩)

/-- An operation with three inputs, read in the order `π`. -/
def op3 (T : Tree GerGen) (hT : T.arity = 3) (π : Equiv.Perm (Fin 3)) :
    Reg (TreeOfArity GerGen) (Fin 3) :=
  (Sym.LinOrd.map π (Sym.LinOrd.std 3), ⟨TreeOfArity.toArr T, by
    show T.arity = _
    rw [Fintype.card_fin]
    exact hT⟩)

/-- The permutation `0 ↦ 1, 1 ↦ 0, 2 ↦ 2`. -/
def c102 : Equiv.Perm (Fin 3) := ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩
/-- The permutation `0 ↦ 0, 1 ↦ 2, 2 ↦ 1`. -/
def c021 : Equiv.Perm (Fin 3) := ⟨![0, 2, 1], ![0, 2, 1], by decide, by decide⟩
/-- The permutation `0 ↦ 2, 1 ↦ 0, 2 ↦ 1`. -/
def c201 : Equiv.Perm (Fin 3) := ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩

lemma std_corolla (e : GerGen 2) : Reg.std (TreeOfArity.corolla e) = op2 e 1 :=
  Reg.ext (Sym.LinOrd.ext fun _ _ => Iff.rfl) (TreeOfArity.arr_ext rfl)

lemma map_op2 (e : GerGen 2) (π τ : Equiv.Perm (Fin 2)) :
    SetOperad.map π (op2 e τ) = op2 e (π * τ) :=
  Reg.ext (Sym.LinOrd.ext fun _ _ => Iff.rfl) rfl

lemma map_op3 (T : Tree GerGen) (hT : T.arity = 3) (π τ : Equiv.Perm (Fin 3)) :
    SetOperad.map π (op3 T hT τ) = op3 T hT (π * τ) :=
  Reg.ext (Sym.LinOrd.ext fun _ _ => Iff.rfl) rfl

lemma s01 (g h : GerGen 2) (τ : Equiv.Perm (Fin 2)) (hτ : τ = 1 ∨ τ = Equiv.swap 0 1) :
    SetOperad.map (insertEquiv 0 1 2) (SetOperad.comp (⟨0, by omega⟩ : Fin (0 + 1 + 1))
      (op2 g 1) (op2 h τ)) = op3 (tLp g h) rfl (if τ = 1 then 1 else c102) := by
  refine Reg.ext ?_ (TreeOfArity.arr_ext ?_)
  · refine Sym.LinOrd.ext fun a b => ?_
    rcases hτ with rfl | rfl <;>
    fin_cases a <;> fin_cases b <;> simp [SetOperad.map, SetOperad.comp, Reg.mapR,
      Reg.compR, op2, op3, Sym.LinOrd.compLt, insertEquiv, c102] <;> decide
  · change (NSSetOperad.Arr.comp (TreeOfArity.toArr (cg g))
      ((Sym.LinOrd.map 1 (Sym.LinOrd.std 2)).rank (⟨0, by omega⟩ : Fin 2))
      (TreeOfArity.toArr (cg h))).2.1 = tLp g h
    rw [TreeOfArity.arr_comp_tree _ _ (by
      rw [Sym.LinOrd.rank_map, Sym.LinOrd.rank_std]; exact Fin.is_lt _),
      Sym.LinOrd.rank_map, Sym.LinOrd.rank_std]
    rfl

lemma s10 (g h : GerGen 2) (τ : Equiv.Perm (Fin 2)) (hτ : τ = 1 ∨ τ = Equiv.swap 0 1) :
    SetOperad.map (insertEquiv 1 0 2) (SetOperad.comp (⟨1, by omega⟩ : Fin (1 + 1 + 0))
      (op2 g 1) (op2 h τ)) = op3 (tRp g h) rfl (if τ = 1 then 1 else c021) := by
  refine Reg.ext ?_ (TreeOfArity.arr_ext ?_)
  · refine Sym.LinOrd.ext fun a b => ?_
    rcases hτ with rfl | rfl <;>
    fin_cases a <;> fin_cases b <;> simp [SetOperad.map, SetOperad.comp, Reg.mapR,
      Reg.compR, op2, op3, Sym.LinOrd.compLt, insertEquiv, c021] <;> decide
  · change (NSSetOperad.Arr.comp (TreeOfArity.toArr (cg g))
      ((Sym.LinOrd.map 1 (Sym.LinOrd.std 2)).rank (⟨1, by omega⟩ : Fin 2))
      (TreeOfArity.toArr (cg h))).2.1 = tRp g h
    rw [TreeOfArity.arr_comp_tree _ _ (by
      rw [Sym.LinOrd.rank_map, Sym.LinOrd.rank_std]; exact Fin.is_lt _),
      Sym.LinOrd.rank_map, Sym.LinOrd.rank_std]
    rfl

lemma s01_one (g h : GerGen 2) :
    SetOperad.map (insertEquiv 0 1 2) (SetOperad.comp (⟨0, by omega⟩ : Fin (0 + 1 + 1))
      (op2 g 1) (op2 h 1)) = op3 (tLp g h) rfl 1 := s01 g h 1 (Or.inl rfl)

lemma s10_one (g h : GerGen 2) :
    SetOperad.map (insertEquiv 1 0 2) (SetOperad.comp (⟨1, by omega⟩ : Fin (1 + 1 + 0))
      (op2 g 1) (op2 h 1)) = op3 (tRp g h) rfl 1 := s10 g h 1 (Or.inl rfl)

lemma s01_swap (g h : GerGen 2) :
    SetOperad.map (insertEquiv 0 1 2) (SetOperad.comp (⟨0, by omega⟩ : Fin (0 + 1 + 1))
      (op2 g 1) (op2 h (Equiv.swap 0 1))) = op3 (tLp g h) rfl c102 :=
  (s01 g h _ (Or.inr rfl)).trans (by rw [if_neg (by decide)])

lemma s10_swap (g h : GerGen 2) :
    SetOperad.map (insertEquiv 1 0 2) (SetOperad.comp (⟨1, by omega⟩ : Fin (1 + 1 + 0))
      (op2 g 1) (op2 h (Equiv.swap 0 1))) = op3 (tRp g h) rfl c021 :=
  (s10 g h _ (Or.inr rfl)).trans (by rw [if_neg (by decide)])

lemma s01_out (g h : GerGen 2) :
    SetOperad.map (insertEquiv 0 1 2) (SetOperad.comp (⟨0, by omega⟩ : Fin (0 + 1 + 1))
      (op2 g (Equiv.swap 0 1)) (op2 h 1)) = op3 (tRp g h) rfl c201 := by
  refine Reg.ext ?_ (TreeOfArity.arr_ext ?_)
  · refine Sym.LinOrd.ext fun a b => ?_
    fin_cases a <;> fin_cases b <;> simp [SetOperad.map, SetOperad.comp, Reg.mapR,
      Reg.compR, op2, op3, Sym.LinOrd.compLt, insertEquiv, c201] <;> decide
  · change (NSSetOperad.Arr.comp (TreeOfArity.toArr (cg g))
      ((Sym.LinOrd.map (Equiv.swap 0 1) (Sym.LinOrd.std 2)).rank (⟨0, by omega⟩ : Fin 2))
      (TreeOfArity.toArr (cg h))).2.1 = tRp g h
    rw [TreeOfArity.arr_comp_tree _ _ (by
      rw [Sym.LinOrd.rank_map, Sym.LinOrd.rank_std]; exact Fin.is_lt _),
      Sym.LinOrd.rank_map, Sym.LinOrd.rank_std]
    rfl

/-! ### In the free graded operad -/


lemma apar_cg (e : GerGen 2) (r : ℕ) : Tree.apar gerPar (cg e) r = false := by
  simp only [Tree.apar, Forest.aparF, Forest.tparF, Tree.tpar]
  split_ifs <;> rfl

/-- A basis element with two inputs. -/
noncomputable abbrev b2 (e : GerGen 2) (π : Equiv.Perm (Fin 2)) : FreeGr R gerPar (Fin 2) :=
  Finsupp.single (op2 e π) 1

/-- A basis element with three inputs. -/
noncomputable abbrev b3 (T : Tree GerGen) (hT : T.arity = 3) (π : Equiv.Perm (Fin 3)) :
    FreeGr R gerPar (Fin 3) :=
  Finsupp.single (op3 T hT π) 1

lemma gen_eq (e : GerGen 2) : (FreeGr.gen e : FreeGr R gerPar (Fin 2)) = b2 R e 1 := by
  rw [FreeGr.gen, SgnLin.bas, std_corolla]

lemma map_b2 (e : GerGen 2) (π τ : Equiv.Perm (Fin 2)) :
    GrOperad.map (R := R) π (b2 R e τ) = b2 R e (π * τ) := by
  rw [SgnLin.map_def, Lin.mapL_single, map_op2]

lemma map_b3 (T : Tree GerGen) (hT : T.arity = 3) (π τ : Equiv.Perm (Fin 3)) :
    GrOperad.map (R := R) π (b3 R T hT τ) = b3 R T hT (π * τ) := by
  rw [SgnLin.map_def, Lin.mapL_single, map_op3]

lemma nsc01_b2 (g h : GerGen 2) (π τ : Equiv.Perm (Fin 2)) :
    GrOperad.nsc R 0 1 (b2 R g π) (b2 R h τ) = Finsupp.single (SetOperad.map (insertEquiv 0 1 2)
      (SetOperad.comp (⟨0, by omega⟩ : Fin (0 + 1 + 1)) (op2 g π) (op2 h τ))) 1 := by
  rw [GrOperad.nsc, SgnLin.comp_def, SgnLin.compT_single, SgnLin.map_def, Lin.mapL_single]
  congr 1
  show σ R (_ && Tree.apar gerPar (cg g) _) * (1 * 1) = 1
  rw [apar_cg, Bool.and_false, σ_false, mul_one, mul_one]

lemma nsc10_b2 (g h : GerGen 2) (π τ : Equiv.Perm (Fin 2)) :
    GrOperad.nsc R 1 0 (b2 R g π) (b2 R h τ) = Finsupp.single (SetOperad.map (insertEquiv 1 0 2)
      (SetOperad.comp (⟨1, by omega⟩ : Fin (1 + 1 + 0)) (op2 g π) (op2 h τ))) 1 := by
  rw [GrOperad.nsc, SgnLin.comp_def, SgnLin.compT_single, SgnLin.map_def, Lin.mapL_single]
  congr 1
  show σ R (_ && Tree.apar gerPar (cg g) _) * (1 * 1) = 1
  rw [apar_cg, Bool.and_false, σ_false, mul_one, mul_one]

/-! ### The relations -/

/-- The ideal of the Gerstenhaber operad. -/
noncomputable abbrev JG : GrOperadIdeal R (FreeGr R gerPar) := GrOperadIdeal.span R (Ger.rel R)

lemma relOf_mem {n : ℕ} (r : Ger.Rel n) :
    Ger.relOf R (Ger.μ R) (Ger.β R) r ∈ (JG R).sub (Fin n) :=
  GrOperadIdeal.subset_span n ⟨r, rfl⟩

lemma μ_eq : Ger.μ R = b2 R .mul 1 := gen_eq R _
lemma β_eq : Ger.β R = b2 R .br 1 := gen_eq R _

lemma nsc_mem_left {a b n : ℕ} {x : FreeGr R gerPar (Fin (a + 1 + b))}
    (hx : x ∈ (JG R).sub _) (y : FreeGr R gerPar (Fin n)) :
    GrOperad.nsc R a b x y ∈ (JG R).sub _ :=
  (JG R).map_mem _ ((JG R).comp_mem_left _ y hx)

lemma nsc_mem_right {a b n : ℕ} (x : FreeGr R gerPar (Fin (a + 1 + b)))
    {y : FreeGr R gerPar (Fin n)} (hy : y ∈ (JG R).sub _) :
    GrOperad.nsc R a b x y ∈ (JG R).sub _ :=
  (JG R).map_mem _ ((JG R).comp_mem_right _ x hy)

lemma nsc_sub_right {a b n : ℕ} (x : FreeGr R gerPar (Fin (a + 1 + b)))
    (y y' : FreeGr R gerPar (Fin n)) :
    GrOperad.nsc R a b x (y - y') = GrOperad.nsc R a b x y - GrOperad.nsc R a b x y' := by
  simp only [GrOperad.nsc, map_sub]

lemma rel2_mem (e : GerGen 2) : b2 R e (Equiv.swap 0 1) - b2 R e 1 ∈ (JG R).sub (Fin 2) := by
  cases e
  · have := relOf_mem R Ger.Rel.comm
    rwa [Ger.relOf, μ_eq, map_b2, mul_one] at this
  · have := relOf_mem R Ger.Rel.symm
    rwa [Ger.relOf, β_eq, map_b2, mul_one] at this

lemma outer_mem (g h : GerGen 2) :
    b3 R (tRp g h) rfl c201 - b3 R (tLp g h) rfl 1 ∈ (JG R).sub (Fin 3) := by
  have := nsc_mem_left R (a := 0) (b := 1) (rel2_mem R g) (b2 R h 1)
  rwa [GrOperad.nsc_sub_left, nsc01_b2, nsc01_b2, s01_out, s01_one g h] at this

lemma innerL_mem (g h : GerGen 2) :
    b3 R (tLp g h) rfl c102 - b3 R (tLp g h) rfl 1 ∈ (JG R).sub (Fin 3) := by
  have := nsc_mem_right R (a := 0) (b := 1) (b2 R g 1) (rel2_mem R h)
  rwa [nsc_sub_right, nsc01_b2, nsc01_b2, s01_swap g h, s01_one g h] at this

lemma innerR_mem (g h : GerGen 2) :
    b3 R (tRp g h) rfl c021 - b3 R (tRp g h) rfl 1 ∈ (JG R).sub (Fin 3) := by
  have := nsc_mem_right R (a := 1) (b := 0) (b2 R g 1) (rel2_mem R h)
  rwa [nsc_sub_right, nsc10_b2, nsc10_b2, s10_swap g h, s10_one g h] at this

lemma swap_eq : Equiv.swap (0 : Fin 3) 1 * 1 = c102 := by decide

lemma assoc_mem : b3 R (tLp .mul .mul) rfl 1 - b3 R (tRp .mul .mul) rfl 1 ∈ (JG R).sub (Fin 3) := by
  have := relOf_mem R Ger.Rel.assoc
  rwa [Ger.relOf, μ_eq, nsc01_b2, nsc10_b2, s01_one _ _, s10_one _ _] at this

lemma leib_mem : b3 R (tRp .br .mul) rfl 1 - b3 R (tLp .mul .br) rfl 1 -
    b3 R (tRp .mul .br) rfl c102 ∈ (JG R).sub (Fin 3) := by
  have := relOf_mem R Ger.Rel.leibniz
  rwa [Ger.relOf, μ_eq, β_eq, nsc01_b2, nsc10_b2, nsc10_b2, s01_one _ _,
    s10_one _ _, s10_one _ _ , map_b3, swap_eq] at this

lemma jac_mem : b3 R (tLp .br .br) rfl 1 + b3 R (tRp .br .br) rfl 1 +
    b3 R (tRp .br .br) rfl c102 ∈ (JG R).sub (Fin 3) := by
  have := relOf_mem R Ger.Rel.jacobi
  rwa [Ger.relOf, β_eq, nsc01_b2, nsc10_b2, s01_one _ _,
    s10_one _ _ , map_b3, swap_eq] at this

/-! ### The certificates -/

lemma pm1 : c021 * c201 = c102 := by decide
lemma pm2 : c102 * c102 = 1 := by decide
lemma pm3 : c201 * c102 = c021 := by decide
lemma pm4 : c021 * c102 = c201 := by decide

lemma mapJ {x : FreeGr R gerPar (Fin 3)} (π : Equiv.Perm (Fin 3)) (hx : x ∈ (JG R).sub (Fin 3)) :
    GrOperad.map (R := R) π x ∈ (JG R).sub (Fin 3) :=
  (JG R).map_mem π hx

/-- **The Jacobi rule.** -/
lemma cert_jac : b3 R (tLp .br .br) rfl 1 + b3 R (tLp .br .br) rfl c021 +
    b3 R (tRp .br .br) rfl 1 ∈ (JG R).sub (Fin 3) := by
  have h2 := mapJ R c021 (outer_mem R .br .br)
  rw [map_sub, map_b3, map_b3, mul_one, pm1] at h2
  convert sub_mem (jac_mem R) h2 using 1
  abel

/-- **The Leibniz rule** at the root. -/
lemma cert_leib₁ : b3 R (tRp .br .mul) rfl 1 - b3 R (tLp .mul .br) rfl 1 -
    b3 R (tLp .mul .br) rfl c021 ∈ (JG R).sub (Fin 3) := by
  have h2 := mapJ R c021 (outer_mem R .mul .br)
  rw [map_sub, map_b3, map_b3, mul_one, pm1] at h2
  convert add_mem (leib_mem R) h2 using 1
  abel

/-- **The Leibniz rule** below, the inputs exchanged. -/
lemma cert_leib₂ : b3 R (tLp .br .mul) rfl c021 - b3 R (tLp .mul .br) rfl 1 -
    b3 R (tRp .mul .br) rfl 1 ∈ (JG R).sub (Fin 3) := by
  have h1 := mapJ R c021 (outer_mem R .br .mul)
  rw [map_sub, map_b3, map_b3, mul_one, pm1] at h1
  have h2 := mapJ R c102 (leib_mem R)
  rw [map_sub, map_sub, map_b3, map_b3, map_b3, mul_one, pm2] at h2
  convert add_mem (sub_mem h2 h1) (innerL_mem R .mul .br) using 1
  abel

/-- **The Leibniz rule** below. -/
lemma cert_leib₃ : b3 R (tLp .br .mul) rfl 1 - b3 R (tLp .mul .br) rfl c021 -
    b3 R (tRp .mul .br) rfl 1 ∈ (JG R).sub (Fin 3) := by
  have h2 := mapJ R c201 (leib_mem R)
  rw [map_sub, map_sub, map_b3, map_b3, map_b3, mul_one, pm3] at h2
  have h3 := mapJ R c021 (innerL_mem R .mul .br)
  rw [map_sub, map_b3, map_b3, mul_one, pm4] at h3
  convert add_mem (add_mem (sub_mem h2 (outer_mem R .br .mul)) h3) (innerR_mem R .mul .br)
    using 1
  abel

/-- **Associativity** at the root. -/
lemma cert_as₁ : b3 R (tRp .mul .mul) rfl 1 - b3 R (tLp .mul .mul) rfl 1 ∈ (JG R).sub (Fin 3) := by
  convert neg_mem (assoc_mem R) using 1
  abel

/-- **Associativity** below, the inputs exchanged. -/
lemma cert_as₂ : b3 R (tLp .mul .mul) rfl c021 - b3 R (tLp .mul .mul) rfl 1 ∈
    (JG R).sub (Fin 3) := by
  have h1 := mapJ R c021 (assoc_mem R)
  rw [map_sub, map_b3, map_b3, mul_one] at h1
  convert sub_mem (add_mem h1 (innerR_mem R .mul .mul)) (assoc_mem R) using 1
  abel

/-! ## The monomials of arity two and three -/

/-- The positions `0, 1, 2`. -/
def e3 : Fin 3 ≃ ↥p3 where
  toFun k := ⟨k.1, by rw [Finset.mem_range, Fintype.card_fin]; exact k.2⟩
  invFun x := ⟨x.1, by have := x.2; rwa [Finset.mem_range, Fintype.card_fin] at this⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The positions `0, 1`. -/
def e2 : Fin 2 ≃ ↥p2 where
  toFun k := ⟨k.1, by rw [Finset.mem_range, Fintype.card_fin]; exact k.2⟩
  invFun x := ⟨x.1, by have := x.2; rwa [Finset.mem_range, Fintype.card_fin] at this⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The basis element of a monomial. -/
noncomputable def bs {A : Finset ℕ} (m : SMono PE A) : FreeGr R gerPar ↥A :=
  Finsupp.single (uv m.1 A (okV m.valid (lset_smono m))) 1

lemma pw_mL₁ (g h : PoisOp) : pw (mL₁ g h).1 = [0, 1, 2] := rfl
lemma pw_mL₂ (g h : PoisOp) : pw (mL₂ g h).1 = [0, 2, 1] := rfl
lemma pw_mR (g h : PoisOp) : pw (mR g h).1 = [0, 1, 2] := rfl

lemma fin3_cases (x : ↥p3) : x = e3 0 ∨ x = e3 1 ∨ x = e3 2 := by
  obtain ⟨a, ha⟩ := x
  have : a < 3 := by rwa [Finset.mem_range, Fintype.card_fin] at ha
  interval_cases a
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

lemma fin2_cases (x : ↥p2) : x = e2 0 ∨ x = e2 1 := by
  obtain ⟨a, ha⟩ := x
  have : a < 2 := by rwa [Finset.mem_range, Fintype.card_fin] at ha
  interval_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma uv_mL₁ (g h : PoisOp) (hh) :
    uv (mL₁ g h).1 p3 hh = SetOperad.map e3 (op3 (tLp (gg g) (gg h)) rfl 1) := by
  refine Reg.ext (Sym.LinOrd.ext fun x y => ?_) (TreeOfArity.arr_ext rfl)
  change (ordOf (pw _) hh).lt x y ↔ _
  rw [ordOf_lt, pw_mL₁]
  rcases fin3_cases x with rfl | rfl | rfl <;> rcases fin3_cases y with rfl | rfl | rfl <;>
    simp [e3, op3, SetOperad.map, Reg.mapR, ← Equiv.Perm.inv_def]

lemma uv_mL₂ (g h : PoisOp) (hh) :
    uv (mL₂ g h).1 p3 hh = SetOperad.map e3 (op3 (tLp (gg g) (gg h)) rfl c021) := by
  refine Reg.ext (Sym.LinOrd.ext fun x y => ?_) (TreeOfArity.arr_ext rfl)
  change (ordOf (pw _) hh).lt x y ↔ _
  rw [ordOf_lt, pw_mL₂]
  rcases fin3_cases x with rfl | rfl | rfl <;> rcases fin3_cases y with rfl | rfl | rfl <;>
    simp [e3, op3, SetOperad.map, Reg.mapR, c021]

lemma uv_mR (g h : PoisOp) (hh) :
    uv (mR g h).1 p3 hh = SetOperad.map e3 (op3 (tRp (gg g) (gg h)) rfl 1) := by
  refine Reg.ext (Sym.LinOrd.ext fun x y => ?_) (TreeOfArity.arr_ext rfl)
  change (ordOf (pw _) hh).lt x y ↔ _
  rw [ordOf_lt, pw_mR]
  rcases fin3_cases x with rfl | rfl | rfl <;> rcases fin3_cases y with rfl | rfl | rfl <;>
    simp [e3, op3, SetOperad.map, Reg.mapR, ← Equiv.Perm.inv_def]

lemma uv_cor_one (g : PoisOp) (hh) :
    uv (cor g 1).1 p2 hh = SetOperad.map e2 (op2 (gg g) 1) := by
  refine Reg.ext (Sym.LinOrd.ext fun x y => ?_) (TreeOfArity.arr_ext rfl)
  change (ordOf (pw _) hh).lt x y ↔ _
  rw [ordOf_lt, show pw (cor g 1).1 = [0, 1] from rfl]
  rcases fin2_cases x with rfl | rfl <;> rcases fin2_cases y with rfl | rfl <;>
    simp [e2, op2, SetOperad.map, Reg.mapR, ← Equiv.Perm.inv_def]

lemma uv_cor_swap (g : PoisOp) (hh) :
    uv (cor g (Equiv.swap 0 1)).1 p2 hh = SetOperad.map e2 (op2 (gg g) (Equiv.swap 0 1)) := by
  refine Reg.ext (Sym.LinOrd.ext fun x y => ?_) (TreeOfArity.arr_ext rfl)
  change (ordOf (pw _) hh).lt x y ↔ _
  rw [ordOf_lt, show pw (cor g (Equiv.swap 0 1)).1 = [1, 0] from rfl]
  rcases fin2_cases x with rfl | rfl <;> rcases fin2_cases y with rfl | rfl <;>
    simp [e2, op2, SetOperad.map, Reg.mapR]

lemma bs_mL₁ (g h : PoisOp) :
    bs R (mL₁ g h) = GrOperad.map (R := R) e3 (b3 R (tLp (gg g) (gg h)) rfl 1) := by
  rw [bs, uv_mL₁, b3, SgnLin.map_def, Lin.mapL_single]

lemma bs_mL₂ (g h : PoisOp) :
    bs R (mL₂ g h) = GrOperad.map (R := R) e3 (b3 R (tLp (gg g) (gg h)) rfl c021) := by
  rw [bs, uv_mL₂, b3, SgnLin.map_def, Lin.mapL_single]

lemma bs_mR (g h : PoisOp) :
    bs R (mR g h) = GrOperad.map (R := R) e3 (b3 R (tRp (gg g) (gg h)) rfl 1) := by
  rw [bs, uv_mR, b3, SgnLin.map_def, Lin.mapL_single]

lemma bs_cor_one (g : PoisOp) : bs R (cor g 1) = GrOperad.map (R := R) e2 (b2 R (gg g) 1) := by
  rw [bs, uv_cor_one, b2, SgnLin.map_def, Lin.mapL_single]

lemma bs_cor_swap (g : PoisOp) :
    bs R (cor g (Equiv.swap 0 1)) = GrOperad.map (R := R) e2 (b2 R (gg g) (Equiv.swap 0 1)) := by
  rw [bs, uv_cor_swap, b2, SgnLin.map_def, Lin.mapL_single]

lemma mem_span_bs {A : Finset ℕ} {S : Set (SMono PE A)} {g : SMono PE A} (hg : g ∈ S) :
    bs R g ∈ Submodule.span R (bs R '' S) :=
  Submodule.subset_span (Set.mem_image_of_mem _ hg)

/-- The monomials of the tails of the rules. -/
def tails : ∀ r : PR, Set (SMono PE r.src)
  | .jac => {mL₂ .bracket .bracket, mR .bracket .bracket}
  | .leib₁ => {mL₁ .mul .bracket, mL₂ .mul .bracket}
  | .leib₂ => {mL₁ .mul .bracket, mR .mul .bracket}
  | .leib₃ => {mL₂ .mul .bracket, mR .mul .bracket}
  | .as₁ => {mL₁ .mul .mul}
  | .as₂ => {mL₁ .mul .mul}
  | .cm => {cor .mul 1}
  | .an => {cor .bracket 1}

theorem tails_lt : ∀ r : PR, ∀ m ∈ tails r, poisOrder.lt m r.lead
  | .jac, m, hm => by
    dsimp only [PR.lead]
    rcases hm with rfl | rfl
    · refine lt_at1 ((words_L₂ _ _).1.trans (words_L₁ _ _).1.symm) ?_
      rw [(words_L₂ _ _).2.1, (words_L₁ _ _).2.1]
      exact Or.inl (by decide)
    · refine lt_at0 ?_
      rw [(words_R _ _).1, (words_L₁ _ _).1]
      exact Or.inl (by decide)
  | .leib₁, m, hm => by
    dsimp only [PR.lead]
    rcases hm with rfl | rfl
    · refine lt_at0 ?_
      rw [(words_L₁ _ _).1, (words_R _ _).1]
      exact Or.inr ⟨by decide, Or.inl (by decide)⟩
    · refine lt_at0 ?_
      rw [(words_L₂ _ _).1, (words_R _ _).1]
      exact Or.inr ⟨by decide, Or.inl (by decide)⟩
  | .leib₂, m, hm => by
    dsimp only [PR.lead]
    rcases hm with rfl | rfl
    · refine lt_at0 ?_
      rw [(words_L₁ _ _).1, (words_L₂ _ _).1]
      exact Or.inr ⟨by decide, Or.inr ⟨by decide, by decide⟩⟩
    · refine lt_at0 ?_
      rw [(words_R _ _).1, (words_L₂ _ _).1]
      exact Or.inl (by decide)
  | .leib₃, m, hm => by
    dsimp only [PR.lead]
    rcases hm with rfl | rfl
    · refine lt_at0 ?_
      rw [(words_L₂ _ _).1, (words_L₁ _ _).1]
      exact Or.inr ⟨by decide, Or.inr ⟨by decide, by decide⟩⟩
    · refine lt_at0 ?_
      rw [(words_R _ _).1, (words_L₁ _ _).1]
      exact Or.inl (by decide)
  | .as₁, m, hm => by
    dsimp only [PR.lead]
    rcases hm with rfl
    refine lt_at0 ?_
    rw [(words_L₁ _ _).1, (words_R _ _).1]
    exact Or.inr ⟨by decide, Or.inl (by decide)⟩
  | .as₂, m, hm => by
    dsimp only [PR.lead]
    rcases hm with rfl
    refine lt_at1 ((words_L₁ _ _).1.trans (words_L₂ _ _).1.symm) ?_
    rw [(words_L₁ _ _).2.1, (words_L₂ _ _).2.1]
    exact Or.inr ⟨by decide, Or.inl (by decide)⟩
  | .cm, m, hm => by
    dsimp only [PR.lead]
    rcases hm with rfl
    refine ⟨⟨0, mem_p2⟩, fun j hj => absurd hj (by
      show ¬ j.1 < 0
      omega), ?_⟩
    show PW (STree.word ltr (cor _ _).1 0) (STree.word ltr (cor _ _).1 0)
    rw [word_cor, word_cor]
    exact Or.inr ⟨by decide, Or.inr ⟨by decide, by decide⟩⟩
  | .an, m, hm => by
    dsimp only [PR.lead]
    rcases hm with rfl
    refine ⟨⟨0, mem_p2⟩, fun j hj => absurd hj (by
      show ¬ j.1 < 0
      omega), ?_⟩
    show PW (STree.word ltr (cor _ _).1 0) (STree.word ltr (cor _ _).1 0)
    rw [word_cor, word_cor]
    exact Or.inr ⟨by decide, Or.inr ⟨by decide, by decide⟩⟩


/-- **The rules hold in the Gerstenhaber operad**, up to a unit: each leading monomial is a unit
multiple of a combination of its tails modulo the ideal of `Ger`. -/
theorem cert : ∀ r : PR, ∃ ρ ∈ (JG R).sub ↥r.src, ∃ u : R, IsUnit u ∧
    ρ - u • bs R r.lead ∈ Submodule.span R (bs R '' tails r)
  | .jac => by
    refine ⟨_, (JG R).map_mem e3 (cert_jac R), 1, isUnit_one, ?_⟩
    have e1 := bs_mL₁ R .bracket .bracket
    have e2 := bs_mL₂ R .bracket .bracket
    have e4 := bs_mR R .bracket .bracket
    dsimp only [gg] at e1 e2 e4
    have : GrOperad.map (R := R) e3 (b3 R (tLp .br .br) rfl 1 + b3 R (tLp .br .br) rfl c021 +
        b3 R (tRp .br .br) rfl 1) - (1 : R) • bs R (mL₁ .bracket .bracket) =
        bs R (mL₂ .bracket .bracket) + bs R (mR .bracket .bracket) := by
      rw [e1, e2, e4, map_add, map_add, one_smul]
      abel
    show _ - (1 : R) • bs R (mL₁ .bracket .bracket) ∈ _
    rw [this]
    exact add_mem (mem_span_bs R (Or.inl rfl))
      (mem_span_bs R (Or.inr rfl))
  | .leib₁ => by
    refine ⟨_, (JG R).map_mem e3 (cert_leib₁ R), 1, isUnit_one, ?_⟩
    have e1 := bs_mR R .bracket .mul
    have e2 := bs_mL₁ R .mul .bracket
    have e4 := bs_mL₂ R .mul .bracket
    dsimp only [gg] at e1 e2 e4
    have : GrOperad.map (R := R) e3 (b3 R (tRp .br .mul) rfl 1 - b3 R (tLp .mul .br) rfl 1 -
        b3 R (tLp .mul .br) rfl c021) - (1 : R) • bs R (mR .bracket .mul) =
        -bs R (mL₁ .mul .bracket) - bs R (mL₂ .mul .bracket) := by
      rw [e1, e2, e4, map_sub, map_sub, one_smul]
      abel
    show _ - (1 : R) • bs R (mR .bracket .mul) ∈ _
    rw [this]
    exact sub_mem (neg_mem (mem_span_bs R (Or.inl rfl)))
      (mem_span_bs R (Or.inr rfl))
  | .leib₂ => by
    refine ⟨_, (JG R).map_mem e3 (cert_leib₂ R), 1, isUnit_one, ?_⟩
    have e1 := bs_mL₂ R .bracket .mul
    have e2 := bs_mL₁ R .mul .bracket
    have e4 := bs_mR R .mul .bracket
    dsimp only [gg] at e1 e2 e4
    have : GrOperad.map (R := R) e3 (b3 R (tLp .br .mul) rfl c021 - b3 R (tLp .mul .br) rfl 1 -
        b3 R (tRp .mul .br) rfl 1) - (1 : R) • bs R (mL₂ .bracket .mul) =
        -bs R (mL₁ .mul .bracket) - bs R (mR .mul .bracket) := by
      rw [e1, e2, e4, map_sub, map_sub, one_smul]
      abel
    show _ - (1 : R) • bs R (mL₂ .bracket .mul) ∈ _
    rw [this]
    exact sub_mem (neg_mem (mem_span_bs R (Or.inl rfl)))
      (mem_span_bs R (Or.inr rfl))
  | .leib₃ => by
    refine ⟨_, (JG R).map_mem e3 (cert_leib₃ R), 1, isUnit_one, ?_⟩
    have e1 := bs_mL₁ R .bracket .mul
    have e2 := bs_mL₂ R .mul .bracket
    have e4 := bs_mR R .mul .bracket
    dsimp only [gg] at e1 e2 e4
    have : GrOperad.map (R := R) e3 (b3 R (tLp .br .mul) rfl 1 - b3 R (tLp .mul .br) rfl c021 -
        b3 R (tRp .mul .br) rfl 1) - (1 : R) • bs R (mL₁ .bracket .mul) =
        -bs R (mL₂ .mul .bracket) - bs R (mR .mul .bracket) := by
      rw [e1, e2, e4, map_sub, map_sub, one_smul]
      abel
    show _ - (1 : R) • bs R (mL₁ .bracket .mul) ∈ _
    rw [this]
    exact sub_mem (neg_mem (mem_span_bs R (Or.inl rfl)))
      (mem_span_bs R (Or.inr rfl))
  | .as₁ => by
    refine ⟨_, (JG R).map_mem e3 (cert_as₁ R), 1, isUnit_one, ?_⟩
    have e1 := bs_mR R .mul .mul
    have e2 := bs_mL₁ R .mul .mul
    dsimp only [gg] at e1 e2
    have : GrOperad.map (R := R) e3 (b3 R (tRp .mul .mul) rfl 1 - b3 R (tLp .mul .mul) rfl 1) -
        (1 : R) • bs R (mR .mul .mul) = -bs R (mL₁ .mul .mul) := by
      rw [e1, e2, map_sub, one_smul]
      abel
    show _ - (1 : R) • bs R (mR .mul .mul) ∈ _
    rw [this]
    exact neg_mem (mem_span_bs R (rfl))
  | .as₂ => by
    refine ⟨_, (JG R).map_mem e3 (cert_as₂ R), 1, isUnit_one, ?_⟩
    have e1 := bs_mL₂ R .mul .mul
    have e2 := bs_mL₁ R .mul .mul
    dsimp only [gg] at e1 e2
    have : GrOperad.map (R := R) e3 (b3 R (tLp .mul .mul) rfl c021 -
        b3 R (tLp .mul .mul) rfl 1) - (1 : R) • bs R (mL₂ .mul .mul) = -bs R (mL₁ .mul .mul) := by
      rw [e1, e2, map_sub, one_smul]
      abel
    show _ - (1 : R) • bs R (mL₂ .mul .mul) ∈ _
    rw [this]
    exact neg_mem (mem_span_bs R (rfl))
  | .cm => by
    refine ⟨_, (JG R).map_mem e2 (rel2_mem R .mul), 1, isUnit_one, ?_⟩
    have e1 := bs_cor_swap R .mul
    have e4 := bs_cor_one R .mul
    dsimp only [gg] at e1 e4
    have : GrOperad.map (R := R) e2 (b2 R .mul (Equiv.swap 0 1) - b2 R .mul 1) -
        (1 : R) • bs R (cor .mul (Equiv.swap 0 1)) = -bs R (cor .mul 1) := by
      rw [e1, e4, map_sub, one_smul]
      abel
    show _ - (1 : R) • bs R (cor .mul (Equiv.swap 0 1)) ∈ _
    rw [this]
    exact neg_mem (mem_span_bs R (rfl))
  | .an => by
    refine ⟨_, (JG R).map_mem e2 (rel2_mem R .br), 1, isUnit_one, ?_⟩
    have e1 := bs_cor_swap R .bracket
    have e4 := bs_cor_one R .bracket
    dsimp only [gg] at e1 e4
    have : GrOperad.map (R := R) e2 (b2 R .br (Equiv.swap 0 1) - b2 R .br 1) -
        (1 : R) • bs R (cor .bracket (Equiv.swap 0 1)) = -bs R (cor .bracket 1) := by
      rw [e1, e4, map_sub, one_smul]
      abel
    show _ - (1 : R) • bs R (cor .bracket (Equiv.swap 0 1)) ∈ _
    rw [this]
    exact neg_mem (mem_span_bs R (rfl))

/-! ## Spanning -/

section Span

variable (K : Type u) [Field K]

/-- **The class of a monomial** in the Gerstenhaber operad. -/
noncomputable def vG {B : Finset ℕ} (m : SMono PE B) : GerOp K ↥B := (JG K).proj ↥B (bs K m)

/-- **The normal monomials span the Gerstenhaber operad**, modulo smaller monomials: every
monomial is a combination of normal monomials, by well-founded induction along the order. -/
theorem vG_mem_span {B : Finset ℕ} (m : SMono PE B) :
    vG K m ∈ Submodule.span K (Set.range fun n : ((rules K).rw B).Irr => vG K n.1) := by
  induction m using (poisOrder.wf B).induction with
  | h m ih =>
  set W := Submodule.span K (Set.range fun n : ((rules K).rw B).Irr => vG K n.1)
  by_cases hm : (rules K).Normal m
  · exact Submodule.subset_span ⟨⟨m, (rules K).mem_irr_iff.2 hm⟩, rfl⟩
  · simp only [Rules.Normal, not_forall, not_not] at hm
    obtain ⟨r, f, hf, rfl⟩ := hm
    obtain ⟨F, ⟨L, hL1, hL2⟩, hF⟩ := uv_ctx K (A := r.src) (f := f) hf (PR.lead r)
    obtain ⟨ρ, hρ, u, hu, hv⟩ := cert K r
    have hL : ∀ g : SMono PE r.src, ∃ c : K, IsUnit c ∧ L (bs K g) = c • bs K (f g) := fun g => by
      obtain ⟨c, hc, h⟩ := hL2 (uv g.1 _ (okV g.valid (lset_smono g)))
      refine ⟨c, hc, ?_⟩
      rw [bs, h, ← hF g (okV g.valid (lset_smono g)) (okV (f g).valid (lset_smono (f g))), bs]
      exact (Finsupp.smul_single_one _ _).symm
    have hW : ∀ x ∈ Submodule.span K (bs K '' tails r), (JG K).proj ↥B (L x) ∈ W := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, hg, rfl⟩ := hx
        obtain ⟨c, -, h⟩ := hL g
        rw [h, map_smul]
        exact Submodule.smul_mem _ _ (ih (f g) (poisOrder.lt_ctx hf (tails_lt r g hg)))
      | zero => rw [map_zero, map_zero]; exact W.zero_mem
      | add x y _ _ hx hy => rw [map_add, map_add]; exact W.add_mem hx hy
      | smul a x _ hx => rw [map_smul, map_smul]; exact W.smul_mem a hx
    obtain ⟨c, hc, h0⟩ := hL (PR.lead r)
    have h1 : (JG K).proj ↥B (L ρ) = 0 :=
      ((JG K).proj_eq_zero_iff _).2 (hL1 _ ρ hρ)
    have h2 : (JG K).proj ↥B (L ρ) = (u * c) • vG K (f (PR.lead r)) +
        (JG K).proj ↥B (L (ρ - u • bs K (PR.lead r))) := by
      rw [map_sub, map_sub, map_smul, h0, smul_smul, vG, map_smul]
      abel
    rw [h1, eq_comm, ← eq_neg_iff_add_eq_zero] at h2
    have h3 : (u * c) • vG K (f (PR.lead r)) ∈ W := by
      rw [h2]
      exact W.neg_mem (hW _ hv)
    exact (Submodule.smul_mem_iff W (hu.mul hc).ne_zero).1 h3

/-- **The normal monomials span the Gerstenhaber operad.** -/
theorem span_vG (B : Finset ℕ) :
    Submodule.span K (Set.range fun n : ((rules K).rw B).Irr => vG K n.1) = ⊤ := by
  set W := Submodule.span K (Set.range fun n : ((rules K).rw B).Irr => vG K n.1)
  have key : ∀ x : FreeGr K gerPar ↥B, x ∈ W.comap ((JG K).proj ↥B) := fun x => by
    induction x using Finsupp.induction_linear with
    | zero => exact Submodule.zero_mem _
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | single s a =>
      obtain ⟨m, hm⟩ := uv_surjective B s
      have : (Finsupp.single s a : FreeGr K gerPar ↥B) = a • bs K m := by
        rw [bs, hm]
        exact (Finsupp.smul_single_one _ _).symm
      rw [this]
      exact Submodule.smul_mem _ _ (vG_mem_span K m)
  refine eq_top_iff.2 fun q _ => ?_
  obtain ⟨x, rfl⟩ := (JG K).proj_surjective ↥B q
  exact key x

/-- **The Gerstenhaber operad has at most `n!` operations of arity `n`.** -/
theorem finite_finrank_le (n : ℕ) :
    Module.Finite K (GerOp K ↥(Finset.range n)) ∧
      Module.finrank K (GerOp K ↥(Finset.range n)) ≤ n.factorial := by
  classical
  obtain ⟨hfin, hcard⟩ := card_irr_le (K := K) n
  have := Fintype.ofFinite ((rules K).rw (Finset.range n)).Irr
  have htop := span_vG K (Finset.range n)
  refine ⟨⟨⟨Finset.univ.image fun n' : ((rules K).rw (Finset.range n)).Irr => vG K n'.1, ?_⟩⟩, ?_⟩
  · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, htop]
  · have h := finrank_range_le_card (R := K)
      (fun n' : ((rules K).rw (Finset.range n)).Irr => vG K n'.1)
    rw [Set.finrank, htop, finrank_top, ← Nat.card_eq_fintype_card] at h
    exact h.trans hcard

end Span

end GerDim

end Operad

