/-
# The sign rule of merging an edge

Step (2b) of the bridge between symmetric and shuffle operads (Dotsenko–Khoroshkin), continued from
`ShuffleBarSymDiff.lean`: `T = FreeGrL K E` for `E` even with the basis `c` indexed by `BinGen G`,
`Ī` its ideal of operations with at least two inputs, and `ShuffleBarSym.ΦL` the comparison of
`B(T, Ī)(Fin n)` with the bar construction of the free shuffle operad on `G`, a basis vector `t`
going to `sign t` times its bar tree.

* **Inversions of lists** (`ShuffleBarSym.inv`, and `ShuffleBarSym.cross` between two lists):
  permuting blocks with no entry in common by `π` multiplies `(-1)^inv` of their concatenation by
  the Koszul sign `ShuffleBarSym.kz`, a sign `(-1)^{|B a| |B b|}` for each pair of blocks that `π`
  puts in the opposite order (`ShuffleBarSym.neg_one_pow_inv_flatten_perm`); removing an entry `w`
  at position `p` multiplies it by `(-1)^p` and `(-1)` to the number of entries smaller than `w`
  (`ShuffleBarSym.neg_one_pow_inv_erase`). Together they give **the sign rule on lists**
  (`ShuffleBarSym.sign_rule_list`).
* **The cut edges in preorder**: the cut edges of the bar tree `toBar t` are named by the keys of
  the vertices of `t` other than the root (`ShuffleBarSym.cutKeys_toBar`), which are distinct
  (`ShuffleBarSym.nodup_tail_preKeys`), so `ShuffleBar.sgn (toBar t) κ` is `(-1)` to the number of
  those keys smaller than `κ` (`ShuffleBarSym.sgn_toBar`).
* **Merging an edge** (`ShuffleBarSym.mergeT`): the vertex of key `κ` is merged into its parent;
  the children of the two vertices, in planar order (`ShuffleBarSym.planar`, in the positions
  `posEquivF` of the composite), are sorted by their least leaves (`ShuffleBarSym.sortP`), and the
  merged monomial `mergeMono` has its leaves named by their ranks (`ShuffleBarSym.mergedMono`, a
  monomial by `ShuffleBarSym.mergedMono_mem`). **The merged tree is a shuffle tree with the same
  leaves whose bar tree is `mergeK (toBar t) κ`** (`ShuffleBarSym.mergeT_spec`, by
  `ShuffleBarSym.toBar_rootMerge` at the root).
* **The sign rule** (`ShuffleBarSym.sign_mergeT`):
  `sign t · (-1)^p · kzAt t κ · sign (mergeT t κ) = ShuffleBar.sgn (toBar t) κ`, for `p` the
  position of `κ` among the keys of the vertices other than the root in preorder and `kzAt t κ`
  the Koszul sign of sorting the children of the merged vertex, a child of the parity of its number
  of vertices. The preorder of the merged tree is that of `t` with `κ` removed and the blocks of the
  merged vertex permuted (`ShuffleBarSym.preKeys_mergeT`).
* **The differential identity from the expansion over the edges**
  (`ShuffleBarSym.ΦL_d_of_expansion`): if `Bar.d` of every basis vector `t` of `B(T, Ī)(Fin n)`
  is the sum, over the keys `κ` of the vertices other than the root, of `(-1)^p kzAt t κ` times the
  basis vector of `mergeT t κ` (`ShuffleBarSym.DExpansion`), then
  `ΦL ∘ Bar.d = ShuffleBar.d ∘ ΦL` on all of `B(T, Ī)(Fin n)`. The expansion holds on the trees
  with one or two vertices (`ShuffleBarSym.dExpansion_of_weight`), by `ShuffleBarSymDiff.lean`.

`FreeGr.barD` contracts the edge below the vertex in position `k` of the preorder, the root in
position zero, with the sign `contrSgn`, the parity of the vertices before the parent and of those
between the parent and the vertex, that is `k - 1 = p` for odd vertices; the merge `Bar.msVal` of an
odd generator carries no sign; and reading the children of the merged vertex in the shuffle order
costs the Koszul sign `kzAt`. These are the signs of `ShuffleBarSym.DExpansion`. A script
checked `sign_mergeT` with these signs on about 9000 edges of random trees with up to ten leaves.

Not proved here: the expansion `ShuffleBarSym.DExpansion` on the trees with three or more vertices.
It needs `Bar.d` of a basis vector expanded over its edges, by `Bar.d_comp` and
`FreeGrL.shEv_split` (or by `FreeGr.barD` on a planar representative of the evaluation), the merge
`Bar.msVal` of two basis generators as the relabelled basis generator of `mergedMono` (as
`ShuffleBarSym.comp_tBasis` does for two vertices), and the evaluation of a vertex whose generator
is relabelled by a permutation as the Koszul sign `GrEnd.rsg` times the evaluation with its children
permuted (`GrComposite.mk_reorder`), which is `kzAt`.
-/
import Operad.ShuffleBarSymDiff

universe u

namespace Operad

namespace ShuffleBarSym

/-! ## Inversions of lists -/

section Inv

variable {α : Type*} [LinearOrder α]

/-- **The cross inversions** of two lists: the pairs of an entry `x` of the first and an entry
`y < x` of the second. -/
def cross (l₁ l₂ : List α) : ℕ := (l₁.map fun x => l₂.countP (· < x)).sum

@[simp] lemma cross_nil_left (l : List α) : cross [] l = 0 := rfl

lemma cross_cons_left (a : α) (l₁ l₂ : List α) :
    cross (a :: l₁) l₂ = l₂.countP (· < a) + cross l₁ l₂ := by
  simp [cross]

@[simp] lemma cross_nil_right (l : List α) : cross l [] = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [cross_cons_left, ih]; rfl

lemma cross_append_left (l₁ l₂ l : List α) : cross (l₁ ++ l₂) l = cross l₁ l + cross l₂ l := by
  simp [cross]

lemma cross_append_right (l l₂ l₃ : List α) : cross l (l₂ ++ l₃) = cross l l₂ + cross l l₃ := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [cross_cons_left, cross_cons_left, cross_cons_left, ih, List.countP_append]
    omega

lemma cross_cons_right (b : α) (l₁ l₂ : List α) :
    cross l₁ (b :: l₂) = l₁.countP (b < ·) + cross l₁ l₂ := by
  induction l₁ with
  | nil => rfl
  | cons a l ih =>
    rw [cross_cons_left, cross_cons_left, ih, List.countP_cons, List.countP_cons]
    split_ifs <;> simp_all <;> omega

lemma cross_perm {l₁ l₁' l₂ l₂' : List α} (h₁ : l₁.Perm l₁') (h₂ : l₂.Perm l₂') :
    cross l₁ l₂ = cross l₁' l₂' := by
  unfold cross
  rw [(h₁.map _).sum_eq]
  congr 1
  exact List.map_congr_left fun x _ => h₂.countP_eq _

/-- **Two disjoint lists cross in every pair once**: `cross l₁ l₂ + cross l₂ l₁ = |l₁| |l₂|`. -/
lemma cross_add_cross {l₁ l₂ : List α} (h : ∀ x ∈ l₁, x ∉ l₂) :
    cross l₁ l₂ + cross l₂ l₁ = l₁.length * l₂.length := by
  induction l₁ with
  | nil => simp
  | cons a l ih =>
    have ha : a ∉ l₂ := h a (List.mem_cons_self ..)
    have ih' := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [cross_cons_left, cross_cons_right, List.length_cons, Nat.succ_mul]
    have hsplit : l₂.countP (· < a) + l₂.countP (a < ·) = l₂.length := by
      rw [List.length_eq_countP_add_countP (· < a)]
      congr 1
      refine List.countP_congr fun y hy => ?_
      have hne : y ≠ a := fun e => ha (e ▸ hy)
      simp only [decide_eq_true_eq, not_lt]
      exact ⟨le_of_lt, fun h' => lt_of_le_of_ne h' (Ne.symm hne)⟩
    omega

/-- **Inversions of a concatenation.** -/
lemma inv_append (l₁ l₂ : List α) : inv (l₁ ++ l₂) = inv l₁ + inv l₂ + cross l₁ l₂ := by
  induction l₁ with
  | nil => simp [inv]
  | cons a l ih =>
    simp only [List.cons_append, inv, ih, cross_cons_left, List.filter_append,
      List.length_append, ← List.countP_eq_length_filter]
    omega

lemma inv_cons (a : α) (l : List α) : inv (a :: l) = l.countP (· < a) + inv l := by
  rw [inv, List.countP_eq_length_filter]

lemma cross_flatten_ofFn_right (l : List α) :
    ∀ {N : ℕ} (D : Fin N → List α), cross l (List.ofFn D).flatten = ∑ b, cross l (D b)
  | 0, _ => by simp
  | N + 1, D => by
    rw [List.ofFn_succ, List.flatten_cons, cross_append_right, Fin.sum_univ_succ,
      cross_flatten_ofFn_right l (fun i => D i.succ)]

variable (K : Type u) [CommRing K]

lemma neg_one_pow_mul_self (n : ℕ) : (-1 : K) ^ n * (-1) ^ n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

/-- **Products over the pairs of a linear order**, each unordered pair taken once. -/
lemma prod_prod_orient {ι : Type*} [Fintype ι] [LinearOrder ι] {M : Type*} [CommMonoid M]
    (F : ι → ι → M) (hF : ∀ a, F a a = 1) :
    ∏ a, ∏ b, F a b = ∏ a, ∏ b, if a < b then F a b * F b a else 1 := by
  have h1 : ∀ a b, F a b = (if a < b then F a b else 1) * (if b < a then F a b else 1) := by
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · rw [if_pos h, if_neg (lt_asymm h), mul_one]
    · rw [if_neg (lt_irrefl a), hF, one_mul]
    · rw [if_neg (lt_asymm h), if_pos h, one_mul]
  calc ∏ a, ∏ b, F a b
      = ∏ a, ∏ b, (if a < b then F a b else 1) * (if b < a then F a b else 1) :=
        Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => h1 a b
    _ = (∏ a, ∏ b, if a < b then F a b else 1) * ∏ a, ∏ b, if b < a then F a b else 1 := by
        simp only [Finset.prod_mul_distrib]
    _ = (∏ a, ∏ b, if a < b then F a b else 1) * ∏ a, ∏ b, if a < b then F b a else 1 := by
        rw [Finset.prod_comm (f := fun a b => if b < a then F a b else 1)]
    _ = ∏ a, ∏ b, if a < b then F a b * F b a else 1 := by
        simp only [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
        split_ifs <;> simp

/-- **The sign of the inversions of a concatenation of blocks**: the signs of the blocks and of
the cross inversions of the pairs of blocks. -/
theorem neg_one_pow_inv_flatten : ∀ {N : ℕ} (C : Fin N → List α),
    (-1 : K) ^ inv (List.ofFn C).flatten
      = (∏ a, (-1 : K) ^ inv (C a)) * ∏ a, ∏ b, if a < b then (-1 : K) ^ cross (C a) (C b) else 1
  | 0, _ => by simp [inv]
  | N + 1, C => by
    rw [List.ofFn_succ, List.flatten_cons, inv_append, cross_flatten_ofFn_right, pow_add, pow_add,
      neg_one_pow_inv_flatten (fun i => C i.succ), Fin.prod_univ_succ, Fin.prod_univ_succ,
      Fin.prod_univ_succ, if_neg (lt_irrefl _), one_mul, ← Finset.prod_pow_eq_pow_sum]
    have h1 : ∀ i : Fin N, (∏ b : Fin (N + 1), if i.succ < b then (-1 : K) ^ cross (C i.succ) (C b)
        else 1) = ∏ b : Fin N, if i < b then (-1 : K) ^ cross (C i.succ) (C b.succ) else 1 := by
      intro i
      rw [Fin.prod_univ_succ, if_neg (Fin.not_lt_zero _), one_mul]
      simp only [Fin.succ_lt_succ_iff]
    simp only [Fin.succ_pos, if_true, h1]
    ring

omit [LinearOrder α] in
/-- **The Koszul sign of permuting blocks**: a sign `(-1)^{|B a| |B b|}` for each pair of blocks
whose order the permutation reverses. -/
def kz {N : ℕ} (B : Fin N → List α) (π : Equiv.Perm (Fin N)) : K :=
  ∏ a, ∏ b, if a < b ∧ π.symm b < π.symm a then (-1 : K) ^ ((B a).length * (B b).length) else 1

omit [LinearOrder α] in
lemma kz_mul_self {N : ℕ} (B : Fin N → List α) (π : Equiv.Perm (Fin N)) :
    kz K B π * kz K B π = 1 := by
  unfold kz
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun a _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun b _ => ?_
  split_ifs
  · exact neg_one_pow_mul_self K _
  · exact one_mul 1

/-- **Permuting blocks changes the sign of the inversions by the Koszul sign**, for blocks with no
entry in common. -/
theorem neg_one_pow_inv_flatten_perm {N : ℕ} (B : Fin N → List α) (π : Equiv.Perm (Fin N))
    (hd : ∀ a b, a ≠ b → ∀ x ∈ B a, x ∉ B b) :
    (-1 : K) ^ inv (List.ofFn (B ∘ π)).flatten = kz K B π * (-1) ^ inv (List.ofFn B).flatten := by
  rw [neg_one_pow_inv_flatten, neg_one_pow_inv_flatten]
  simp only [Function.comp_apply]
  rw [Equiv.prod_comp π (fun a => (-1 : K) ^ inv (B a))]
  suffices hpair : (∏ a, ∏ b, if a < b then (-1 : K) ^ cross (B (π a)) (B (π b)) else 1)
      = kz K B π * ∏ a, ∏ b, if a < b then (-1 : K) ^ cross (B a) (B b) else 1 by
    rw [hpair]
    ring
  set f : Fin N → Fin N → K := fun a b => (-1 : K) ^ cross (B a) (B b) with hf
  have hre : (∏ a, ∏ b, if a < b then f (π a) (π b) else 1)
      = ∏ a, ∏ b, if π.symm a < π.symm b then f a b else 1 := by
    rw [← Equiv.prod_comp π.symm]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← Equiv.prod_comp π.symm]
    simp only [Equiv.apply_symm_apply]
  have hff : ∀ a b, a ≠ b → f a b * f b a = (-1 : K) ^ ((B a).length * (B b).length) := by
    intro a b hab
    rw [hf]
    dsimp only
    rw [← pow_add, cross_add_cross (hd a b hab)]
  have hsq : ∀ a b, f a b * f a b = 1 := fun a b => neg_one_pow_mul_self K _
  change (∏ a, ∏ b, if a < b then f (π a) (π b) else 1)
    = kz K B π * ∏ a, ∏ b, if a < b then f a b else 1
  rw [hre, prod_prod_orient (fun a b => if π.symm a < π.symm b then f a b else 1)
      (fun a => if_neg (lt_irrefl _)),
    prod_prod_orient (fun a b => if a < b then f a b else 1) (fun a => if_neg (lt_irrefl _)),
    kz, prod_prod_orient (fun a b => if a < b ∧ π.symm b < π.symm a then
      (-1 : K) ^ ((B a).length * (B b).length) else 1) (fun a => if_neg fun h => lt_irrefl _ h.1),
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  by_cases hab : a < b
  · have hne : π.symm a ≠ π.symm b := fun h => hab.ne (π.symm.injective h)
    have hba : ¬b < a := lt_asymm hab
    rcases lt_or_gt_of_ne hne with h | h
    · have h' : ¬π.symm b < π.symm a := lt_asymm h
      simp only [hab, hba, h, h', and_false, false_and, if_true, if_false, mul_one, one_mul]
    · have h' : ¬π.symm a < π.symm b := lt_asymm h
      simp only [hab, hba, h, h', and_self, if_true, if_false, mul_one, one_mul]
      rw [← hff a b hab.ne, mul_comm (f a b) (f b a), mul_assoc, hsq, mul_one]
  · simp only [if_neg hab, mul_one]

/-- **Removing an entry from a list**: `(-1)^{inv (A ++ w :: B)} (-1)^{|A|}` is the sign of the
inversions without `w` times `(-1)` to the number of entries smaller than `w`. -/
theorem neg_one_pow_inv_erase (A B : List α) (w : α) (hw : w ∉ A) :
    (-1 : K) ^ inv (A ++ w :: B) * (-1) ^ A.length
      = (-1) ^ inv (A ++ B) * (-1) ^ (A ++ B).countP (· < w) := by
  rw [inv_append, inv_append, inv_cons, cross_cons_right, List.countP_append]
  have hA : A.length = A.countP (· < w) + A.countP (w < ·) := by
    rw [List.length_eq_countP_add_countP (· < w)]
    congr 1
    refine List.countP_congr fun y hy => ?_
    have hne : y ≠ w := fun e => hw (e ▸ hy)
    simp only [decide_eq_true_eq, not_lt]
    exact ⟨fun h' => lt_of_le_of_ne h' (Ne.symm hne), le_of_lt⟩
  rw [hA]
  have e : inv A + (B.countP (· < w) + inv B) + (A.countP (w < ·) + cross A B)
      + (A.countP (· < w) + A.countP (w < ·))
      = (inv A + inv B + cross A B) + (A.countP (· < w) + B.countP (· < w))
        + 2 * A.countP (w < ·) := by ring
  rw [← pow_add, e, pow_add, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

/-- **Permuting the middle of a list** changes the sign of its inversions by the signs of the
inversions of the two middles. -/
theorem neg_one_pow_inv_perm_mid (P M M' S : List α) (h : M.Perm M') :
    (-1 : K) ^ inv (P ++ M' ++ S)
      = (-1) ^ inv (P ++ M ++ S) * ((-1) ^ inv M' * (-1) ^ inv M) := by
  have hc1 : cross P (M' ++ S) = cross P (M ++ S) :=
    cross_perm (List.Perm.refl P) (h.symm.append_right S)
  have hc2 : cross M' S = cross M S := cross_perm h.symm (List.Perm.refl S)
  simp only [List.append_assoc, inv_append, hc1, hc2]
  have e : inv P + (inv M + inv S + cross M S) + cross P (M ++ S) + (inv M' + inv M)
      = (inv P + (inv M' + inv S + cross M S) + cross P (M ++ S)) + 2 * inv M := by ring
  rw [← pow_add, ← pow_add, e, pow_add (-1 : K) _ (2 * inv M), pow_mul, neg_one_sq, one_pow,
    mul_one]

/-- **The sign rule of merging an edge, on lists.** Let `L = P ++ (X ++ w :: Y) ++ S` be a list
whose entry `w` is not in `P ++ X`, and let `L'` be `L` with `w` removed and the middle
`X ++ Y = (B 0) ++ ⋯ ++ (B (N - 1))`, a concatenation of blocks with no entry in common, replaced
by the blocks in the order `π`. Then `(-1)^{inv L} (-1)^{|P| + |X|} kz(B, π) (-1)^{inv L'}` is
`(-1)` to the number of entries of `L` smaller than `w`. -/
theorem sign_rule_list {N : ℕ} (P X Y S : List α) (w : α) (B : Fin N → List α)
    (π : Equiv.Perm (Fin N)) (hB : (List.ofFn B).flatten = X ++ Y)
    (hd : ∀ a b, a ≠ b → ∀ x ∈ B a, x ∉ B b) (hw : w ∉ P ++ X) :
    (-1 : K) ^ inv (P ++ (X ++ w :: Y) ++ S) * (-1) ^ (P.length + X.length) * kz K B π
        * (-1) ^ inv (P ++ (List.ofFn (B ∘ π)).flatten ++ S)
      = (-1) ^ (P ++ (X ++ w :: Y) ++ S).countP (· < w) := by
  have hperm : (List.ofFn (B ∘ π)).flatten.Perm (X ++ Y) :=
    hB ▸ (Equiv.Perm.ofFn_comp_perm π B).flatten
  have hmid := neg_one_pow_inv_perm_mid K P (X ++ Y) _ S hperm.symm
  have hblk := neg_one_pow_inv_flatten_perm K B π hd
  rw [hB] at hblk
  have hL : P ++ (X ++ w :: Y) ++ S = (P ++ X) ++ w :: (Y ++ S) := by simp
  have hL' : P ++ (X ++ Y) ++ S = (P ++ X) ++ (Y ++ S) := by simp
  have her := neg_one_pow_inv_erase K (P ++ X) (Y ++ S) w hw
  rw [List.length_append] at her
  rw [hmid, hblk, hL, hL', her]
  have hc : (P ++ X ++ w :: (Y ++ S)).countP (· < w) = (P ++ X ++ (Y ++ S)).countP (· < w) := by
    simp [List.countP_append]
  rw [hc]
  have h1 := kz_mul_self K B π
  have h2 := neg_one_pow_mul_self K (inv (X ++ Y))
  have h3 := neg_one_pow_mul_self K (inv (P ++ X ++ (Y ++ S)))
  linear_combination (-1 : K) ^ (P ++ X ++ (Y ++ S)).countP (· < w) *
    ((-1) ^ inv (P ++ X ++ (Y ++ S)) * (-1) ^ inv (P ++ X ++ (Y ++ S)) * (kz K B π * kz K B π) * h2
      + (-1) ^ inv (P ++ X ++ (Y ++ S)) * (-1) ^ inv (P ++ X ++ (Y ++ S)) * h1 + h3)

end Inv

/-! ## The cut edges of a bar tree in preorder -/

section CutKeys

open ShuffleBar STree LTree

variable {G : Type} [Fintype G] [DecidableEq G]

lemma cutKeys_cutRoot_toBar_node {k : ℕ} (m : VMono G k) (ch : Fin k → STree (VMono G)) :
    ShuffleBar.cutKeys (cutRoot (toBar (STree.node m ch)))
      = insert (LTree.key (toBar (STree.node m ch)))
        (ShuffleBar.cutKeys (toBar (STree.node m ch))) := by
  obtain ⟨e, l, r, hT⟩ := toBar_node_eq m ch
  rw [hT]
  simp only [cutRoot, ShuffleBar.cutKeys, Bool.false_eq_true, if_false, if_true,
    Finset.empty_union, Finset.singleton_union]
  rfl

/-- The key of the vertex at the root of a bar tree is that of the shuffle tree. -/
lemma key_toBar {t : STree (VMono G)} (ht : t.IsShuffle) : LTree.key (toBar t) = vkey t := by
  have h1 : (toBar t).arity = Multiset.card t.labels := by
    rw [← length_labels, ← Multiset.coe_card, labels_toBar]
  simp only [LTree.key, vkey, minLabel_toBar t ht, h1]

lemma cutKeys_toBar_node_of {k : ℕ} (m : VMono G k) (ch : Fin k → STree (VMono G))
    (ih : ∀ j, ShuffleBar.cutKeys (cutRoot (toBar (ch j))) = (preKeys (ch j)).toFinset) :
    ShuffleBar.cutKeys (toBar (STree.node m ch))
      = (List.ofFn fun j => preKeys (ch j)).flatten.toFinset := by
  rw [cutKeys_toBar_node]
  ext κ
  simp only [Finset.mem_biUnion, Finset.mem_range, List.mem_toFinset, List.mem_flatten,
    List.mem_ofFn]
  constructor
  · rintro ⟨a, ha, hκ⟩
    rw [kids_of_lt ch ha, ih, List.mem_toFinset] at hκ
    exact ⟨_, ⟨⟨a, ha⟩, rfl⟩, hκ⟩
  · rintro ⟨_, ⟨j, rfl⟩, hκ⟩
    refine ⟨j, j.2, ?_⟩
    rw [kids_fin, ih, List.mem_toFinset]
    exact hκ

/-- **The cut edges of the bar tree with the edge above the root cut** are named by the keys of
all the vertices of the shuffle tree. -/
theorem cutKeys_cutRoot_toBar : ∀ t : STree (VMono G), t.IsShuffle →
    ShuffleBar.cutKeys (cutRoot (toBar t)) = (preKeys t).toFinset
  | STree.leaf _, _ => rfl
  | STree.node m ch, ht => by
    rw [cutKeys_cutRoot_toBar_node]
    rw [key_toBar ht]
    rw [cutKeys_toBar_node_of m ch fun j => cutKeys_cutRoot_toBar (ch j) (ht.child j)]
    rw [preKeys, List.toFinset_cons]

/-- **The cut edges of a bar tree are named by the keys of the vertices other than the root**, in
the preorder of the shuffle tree. -/
theorem cutKeys_toBar {t : STree (VMono G)} (ht : t.IsShuffle) :
    ShuffleBar.cutKeys (toBar t) = (preKeys t).tail.toFinset := by
  cases t with
  | leaf => rfl
  | node m ch =>
    rw [cutKeys_toBar_node_of m ch fun j => cutKeys_cutRoot_toBar (ch j) (ht.child j), preKeys,
      List.tail_cons]

/-- **The keys of the vertices other than the root are distinct.** -/
theorem nodup_tail_preKeys {t : STree (VMono G)} (ht : t.IsShuffle) (hnd : t.labels.Nodup) :
    (preKeys t).tail.Nodup := by
  cases t with
  | leaf => exact List.nodup_nil
  | node m ch =>
    have hc := card_cutKeys_toBar m ch hnd
    have hl := length_preKeys (STree.node m ch)
    rw [cutKeys_toBar ht] at hc
    have hlen : (preKeys (STree.node m ch)).tail.toFinset.card
        = (preKeys (STree.node m ch)).tail.length := by
      rw [List.length_tail]
      omega
    have := (Multiset.toFinset_card_eq_card_iff_nodup
      (m := ((preKeys (STree.node m ch)).tail : Multiset (ℕ ×ₗ ℕ)))).1 hlen
    exact Multiset.coe_nodup.1 this

variable (K : Type u) [CommRing K]

/-- **The sign of merging a cut edge of a bar tree** is `(-1)` to the number of vertices of the
shuffle tree other than the root with smaller key. -/
theorem sgn_toBar {t : STree (VMono G)} (ht : t.IsShuffle) (hnd : t.labels.Nodup)
    (κ : ℕ ×ₗ ℕ) :
    ShuffleBar.sgn K (toBar t) κ = (-1) ^ (preKeys t).tail.countP (· < κ) := by
  unfold ShuffleBar.sgn
  have hf : ((preKeys t).tail.toFinset.filter (· < κ))
      = ((preKeys t).tail.filter (· < κ)).toFinset := by
    ext x
    simp
  rw [cutKeys_toBar ht, hf, List.toFinset_card_of_nodup ((nodup_tail_preKeys ht hnd).filter _),
    ← List.countP_eq_length_filter]

end CutKeys

/-! ## Merging an edge of a shuffle tree of monomials -/

section Merge

open ShuffleBar STree LTree

/-- **The children of a merged vertex in planar order**: the children of the vertex before its
child `j`, the children of `j`, then the children of the vertex after `j`, in the positions of the
composite (`posEquivF`). -/
noncomputable def planar {B : ℕ → Type*} {k l N : ℕ} (ch : Fin k → STree B) (j : Fin k)
    (c₂ : Fin l → STree B) (hN : N + 1 = k + l) (r : Fin N) : STree B :=
  Sum.elim (fun a => ch a.1) c₂ ((posEquivF j l N hN).symm r)

lemma planar_inl {B : ℕ → Type*} {k l N : ℕ} (ch : Fin k → STree B) (j : Fin k)
    (c₂ : Fin l → STree B) (hN : N + 1 = k + l) (a : Without (Fin k) j) :
    planar ch j c₂ hN (posEquivF j l N hN (Sum.inl a)) = ch a.1 := by
  simp [planar]

lemma planar_inr {B : ℕ → Type*} {k l N : ℕ} (ch : Fin k → STree B) (j : Fin k)
    (c₂ : Fin l → STree B) (hN : N + 1 = k + l) (i : Fin l) :
    planar ch j c₂ hN (posEquivF j l N hN (Sum.inr i)) = c₂ i := by
  simp [planar]

/-- **The permutation sorting the children** by their least leaves. -/
def sortP {B : ℕ → Type*} {N : ℕ} (Q : Fin N → STree B) : Equiv.Perm (Fin N) :=
  Tuple.sort fun r => (Q r).first

lemma monotone_sortP {B : ℕ → Type*} {N : ℕ} (Q : Fin N → STree B) :
    Monotone fun r => (Q (sortP Q r)).first :=
  Tuple.monotone_sort fun r => (Q r).first

/-- Sorting puts a child with a smaller least leaf before one with a larger least leaf. -/
lemma sortP_symm_lt {B : ℕ → Type*} {N : ℕ} (Q : Fin N → STree B) {r r' : Fin N}
    (h : (Q r).first < (Q r').first) : (sortP Q).symm r < (sortP Q).symm r' := by
  by_contra hle
  have := monotone_sortP Q (not_lt.1 hle)
  simp only [Equiv.apply_symm_apply] at this
  omega

/-- The rank of a leaf `a ≠ j` of the vertex, in the merged monomial. -/
noncomputable def rk₁ {k l N : ℕ} (j : Fin k) (hN : N + 1 = k + l) (π : Equiv.Perm (Fin N))
    (a : ℕ) : ℕ :=
  if h : a < k then
    if h' : (⟨a, h⟩ : Fin k) = j then 0 else (π.symm (posEquivF j l N hN (Sum.inl ⟨⟨a, h⟩, h'⟩)))
  else 0

/-- The rank of a leaf `i` of the child, in the merged monomial. -/
noncomputable def rk₂ {k l N : ℕ} (j : Fin k) (hN : N + 1 = k + l) (π : Equiv.Perm (Fin N))
    (i : ℕ) : ℕ :=
  if h : i < l then (π.symm (posEquivF j l N hN (Sum.inr ⟨i, h⟩))) else 0

lemma rk₁_of {k l N : ℕ} (j : Fin k) (hN : N + 1 = k + l) (π : Equiv.Perm (Fin N))
    (a : Without (Fin k) j) : rk₁ j hN π a.1 = π.symm (posEquivF j l N hN (Sum.inl a)) := by
  rw [rk₁, dif_pos a.1.2, dif_neg a.2]

lemma rk₂_of {k l N : ℕ} (j : Fin k) (hN : N + 1 = k + l) (π : Equiv.Perm (Fin N)) (i : Fin l) :
    rk₂ j hN π i = π.symm (posEquivF j l N hN (Sum.inr i)) := by
  rw [rk₂, dif_pos i.2]

variable {G : Type}

/-- **The merged monomial**: the monomial `m₂` grafted on the leaf `j` of `m₁`, its leaves named
by the ranks of the children of the merged vertex in the order `π`. -/
noncomputable def mergedMono {k l N : ℕ} (m₁ : LTree G) (j : Fin k) (m₂ : LTree G)
    (hN : N + 1 = k + l) (π : Equiv.Perm (Fin N)) : LTree G :=
  mergeMono m₁ j m₂ (rk₁ j hN π) (rk₂ j hN π)

variable [Fintype G] [DecidableEq G]

lemma VMono.two_le {k : ℕ} (m : VMono G k) : 2 ≤ k := m.2.2

/-- **The merged monomial is a monomial** of the merged arity, when the children are sorted. -/
theorem mergedMono_mem {k l N : ℕ} (m₁ : VMono G k) (ch : Fin k → STree (VMono G)) (j : Fin k)
    (m₂ : VMono G l) (c₂ : Fin l → STree (VMono G)) (hj : ch j = STree.node m₂ c₂)
    (ht : (STree.node m₁ ch).IsShuffle) (hN : N + 1 = k + l) :
    mergedMono m₁.1 j m₂.1 hN (sortP (planar ch j c₂ hN)) ∈ LTree.monomials N ∧ 2 ≤ N := by
  set Q := planar ch j c₂ hN with hQ
  set π := sortP Q with hπ
  have hk := m₁.two_le
  have hl := m₂.two_le
  have ht₂ : (STree.node m₂ c₂).IsShuffle := hj ▸ ht.child j
  have hF₁ : ∀ a : Without (Fin k) j, (Q (posEquivF j l N hN (Sum.inl a))).first
      = (ch a.1).first := fun a => by rw [hQ, planar_inl]
  have hF₂ : ∀ i : Fin l, (Q (posEquivF j l N hN (Sum.inr i))).first = (c₂ i).first :=
    fun i => by rw [hQ, planar_inr]
  have hl0 : 0 < l := by omega
  have hc0 : (c₂ ⟨0, hl0⟩).first = (ch j).first := by rw [hj, first_node _ _ hl0]
  -- the ranks of the children of the child are increasing
  have hs₂ : StrictOn (fun i => (LTree.leaf (rk₂ j hN π i) : LTree G).minLabel) m₂.1 := by
    intro a ha b hb hab
    have ha' := m₂.lt ha
    have hb' := m₂.lt hb
    show rk₂ j hN π a < rk₂ j hN π b
    rw [rk₂, dif_pos ha', rk₂, dif_pos hb']
    refine sortP_symm_lt Q ?_
    rw [hF₂, hF₂]
    exact ht₂.mono (show (⟨a, ha'⟩ : Fin l) < ⟨b, hb'⟩ from hab)
  -- the least ranks above the leaves of the vertex
  let ins : ℕ → LTree G := fun a =>
    if a = (j : ℕ) then m₂.1.plug (fun i => LTree.leaf (rk₂ j hN π i))
    else LTree.leaf (rk₁ j hN π a)
  have hmin : ∀ a : Fin k, (ins a).minLabel = π.symm (if h : a = j then
      posEquivF j l N hN (Sum.inr ⟨0, hl0⟩) else posEquivF j l N hN (Sum.inl ⟨a, h⟩)) := by
    intro a
    by_cases h : a = j
    · subst h
      rw [dif_pos rfl]
      simp only [ins, if_true]
      rw [minLabel_plug_of_strictOn _ hs₂, m₂.minLabel]
      show rk₂ a hN π 0 = _
      rw [rk₂, dif_pos hl0]
    · simp only [ins, if_neg (fun h' => h (Fin.ext h')), dif_neg h]
      show rk₁ j hN π a = _
      rw [rk₁, dif_pos a.2, dif_neg (by simpa using h)]
  have hfirst : ∀ a : Fin k, (Q (if h : a = j then posEquivF j l N hN (Sum.inr ⟨0, hl0⟩)
      else posEquivF j l N hN (Sum.inl ⟨a, h⟩))).first = (ch a).first := by
    intro a
    by_cases h : a = j
    · subst h
      rw [dif_pos rfl, hF₂, hc0]
    · rw [dif_neg h, hF₁]
  have hstrict : StrictOn (fun a => (ins a).minLabel) m₁.1 := by
    intro a ha b hb hab
    have ha' := m₁.lt ha
    have hb' := m₁.lt hb
    show (ins (⟨a, ha'⟩ : Fin k)).minLabel < (ins (⟨b, hb'⟩ : Fin k)).minLabel
    rw [hmin, hmin]
    refine sortP_symm_lt Q ?_
    rw [hfirst, hfirst]
    exact ht.mono (show (⟨a, ha'⟩ : Fin k) < ⟨b, hb'⟩ from hab)
  have hshuf : (mergedMono m₁.1 j m₂.1 hN π).IsShuffle := by
    refine isShuffle_plug_of_strictOn _ m₁.isShuffle hstrict fun a _ => ?_
    show (ins a).IsShuffle
    simp only [ins]
    split_ifs
    · exact isShuffle_plug_of_strictOn _ m₂.isShuffle hs₂ fun _ _ => trivial
    · trivial
  -- the leaves are the ranks
  have hlabs : ((mergedMono m₁.1 j m₂.1 hN π).labels : Multiset ℕ) = Multiset.range N := by
    have e1 : ((mergedMono m₁.1 j m₂.1 hN π).labels : Multiset ℕ)
        = ∑ a : Fin k, ((ins a).labels : Multiset ℕ) := by
      rw [mergedMono, mergeMono, labels_plug, ← Multiset.coe_bind, bind_kids m₁]
    have e2 : ((ins j).labels : Multiset ℕ) = ∑ i : Fin l, {rk₂ j hN π i} := by
      simp only [ins, if_true]
      rw [labels_plug_leaf, ← Multiset.map_coe,
        show Multiset.map (rk₂ j hN π) (m₂.1.labels : Multiset ℕ)
          = Multiset.bind (m₂.1.labels : Multiset ℕ) fun a => {rk₂ j hN π a} by
            rw [Multiset.bind_singleton], bind_kids m₂]
    have e3 : ∀ a : Without (Fin k) j, ((ins a.1).labels : Multiset ℕ) = {rk₁ j hN π a.1} := by
      intro a
      simp only [ins, if_neg (fun h' => a.2 (Fin.ext h'))]
      rfl
    have e4 : Multiset.range N = ∑ r : Fin N, {(r : ℕ)} := by
      rw [Fin.sum_univ_eq_sum_range (fun i => ({i} : Multiset ℕ)) N, Finset.sum_eq_multiset_sum,
        Multiset.sum_map_singleton]
      rfl
    rw [e1, Fintype.sum_eq_add_sum_subtype_ne _ j, e2, e4,
      ← Equiv.sum_comp ((posEquivF j l N hN).trans π.symm), Fintype.sum_sum_type,
      add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [e3, rk₁_of]
      rfl
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [rk₂_of]
      rfl
  refine ⟨(LTree.mem_monomials N _).2 ⟨hshuf, Multiset.coe_eq_coe.1 ?_⟩, by omega⟩
  rw [hlabs, Multiset.coe_range]

end Merge

/-! ## Merging the edge above a child of the root -/

section RootMerge

open ShuffleBar STree LTree

lemma mem_preKeys {B : ℕ → Type*} : ∀ {t : STree B} {κ : ℕ ×ₗ ℕ}, t.IsShuffle → κ ∈ preKeys t →
    (ofLex κ).1 ∈ t.labels ∧ (ofLex κ).2 ≤ Multiset.card t.labels
  | STree.leaf _, _, _, h => by simp [preKeys] at h
  | STree.node _ ch, κ, ht, h => by
    simp only [preKeys, List.mem_cons, List.mem_flatten, List.mem_ofFn] at h
    rcases h with rfl | ⟨_, ⟨j, rfl⟩, hj⟩
    · exact ⟨first_mem ht, le_rfl⟩
    · have := mem_preKeys (ht.child j) hj
      exact ⟨Multiset.mem_of_le (labels_le_node _ _ j) this.1,
        this.2.trans (Multiset.card_le_card (labels_le_node _ _ j))⟩

lemma vkey_mem_preKeys {B : ℕ → Type*} {k : ℕ} (β : B k) (ch : Fin k → STree B) :
    vkey (STree.node β ch) ∈ preKeys (STree.node β ch) := by
  simp [preKeys]

lemma preKeys_node {B : ℕ → Type*} {k : ℕ} (β : B k) (ch : Fin k → STree B) :
    preKeys (STree.node β ch)
      = vkey (STree.node β ch) :: (List.ofFn fun j => preKeys (ch j)).flatten := rfl

/-- Shuffle trees with the same leaves have the same least leaf. -/
lemma first_eq_of_labels {B : ℕ → Type*} {t t' : STree B} (ht : t.IsShuffle) (ht' : t'.IsShuffle)
    (h : t.labels = t'.labels) : t.first = t'.first :=
  le_antisymm (first_le ht _ (h ▸ first_mem ht')) (first_le ht' _ (h.symm ▸ first_mem ht))

lemma vkey_eq_of_labels {B : ℕ → Type*} {t t' : STree B} (ht : t.IsShuffle) (ht' : t'.IsShuffle)
    (h : t.labels = t'.labels) : vkey t = vkey t' := by
  rw [vkey, vkey, first_eq_of_labels ht ht' h, h]

variable {G : Type} [Fintype G] [DecidableEq G]

lemma mergeN_eq {k : ℕ} (m₁ : VMono G k) (l : ℕ) : k + l - 1 + 1 = k + l := by
  have := m₁.two_le
  omega

/-- **Merging the edge above the child `j` of the root**, for `ch j = node m₂ c₂`: the vertex of
the merged monomial, with the children of the two vertices sorted by their least leaves. -/
noncomputable def rootMerge {k l : ℕ} (m₁ : VMono G k) (ch : Fin k → STree (VMono G)) (j : Fin k)
    (m₂ : VMono G l) (c₂ : Fin l → STree (VMono G)) : STree (VMono G) :=
  if h : mergedMono m₁.1 j m₂.1 (mergeN_eq m₁ l) (sortP (planar ch j c₂ (mergeN_eq m₁ l)))
      ∈ LTree.monomials (k + l - 1) ∧ 2 ≤ k + l - 1 then
    STree.node (⟨_, h⟩ : VMono G (k + l - 1))
      (planar ch j c₂ (mergeN_eq m₁ l) ∘ sortP (planar ch j c₂ (mergeN_eq m₁ l)))
  else STree.node m₁ ch

variable {k l : ℕ} {m₁ : VMono G k} {ch : Fin k → STree (VMono G)} {j : Fin k} {m₂ : VMono G l}
  {c₂ : Fin l → STree (VMono G)}

lemma rootMerge_eq (hj : ch j = STree.node m₂ c₂) (ht : (STree.node m₁ ch).IsShuffle) :
    rootMerge m₁ ch j m₂ c₂ = STree.node
      (⟨_, mergedMono_mem m₁ ch j m₂ c₂ hj ht (mergeN_eq m₁ l)⟩ : VMono G (k + l - 1))
      (planar ch j c₂ (mergeN_eq m₁ l) ∘ sortP (planar ch j c₂ (mergeN_eq m₁ l))) :=
  dif_pos _

lemma isShuffle_planar {N : ℕ} (hN : N + 1 = k + l) (hj : ch j = STree.node m₂ c₂)
    (ht : (STree.node m₁ ch).IsShuffle) (r : Fin N) : (planar ch j c₂ hN r).IsShuffle := by
  obtain ⟨x, rfl⟩ := (posEquivF j l N hN).surjective r
  rcases x with a | i
  · rw [planar_inl]
    exact ht.child _
  · rw [planar_inr]
    exact (hj ▸ ht.child j : (STree.node m₂ c₂).IsShuffle).child i

lemma first_planar_injective {N : ℕ} (hN : N + 1 = k + l) (hj : ch j = STree.node m₂ c₂)
    (ht : (STree.node m₁ ch).IsShuffle) (hnd : (STree.node m₁ ch).labels.Nodup) :
    Function.Injective fun r => (planar ch j c₂ hN r).first := by
  have ht₂ : (STree.node m₂ c₂).IsShuffle := hj ▸ ht.child j
  have hsub : ∀ i, (c₂ i).labels ≤ (ch j).labels := fun i => by
    rw [hj]
    exact labels_le_node _ _ i
  have hcross : ∀ (a : Without (Fin k) j) (i : Fin l), (ch a.1).first ≠ (c₂ i).first := by
    intro a i h
    have h1 := first_mem (ht.child a.1)
    have h2 := Multiset.mem_of_le (hsub i) (first_mem (ht₂.child i))
    rw [← h] at h2
    exact not_mem_of_node hnd a.2 h1 h2
  intro r r' h
  obtain ⟨x, rfl⟩ := (posEquivF j l N hN).surjective r
  obtain ⟨y, rfl⟩ := (posEquivF j l N hN).surjective r'
  congr 1
  rcases x with a | i <;> rcases y with b | i' <;>
    simp only [planar_inl, planar_inr] at h
  · exact congrArg Sum.inl (Subtype.ext (ht.mono.injective h))
  · exact absurd h (hcross a i')
  · exact absurd h.symm (hcross b i)
  · exact congrArg Sum.inr (ht₂.mono.injective h)

/-- **The merged tree is a shuffle tree.** -/
theorem isShuffle_rootMerge (hj : ch j = STree.node m₂ c₂) (ht : (STree.node m₁ ch).IsShuffle)
    (hnd : (STree.node m₁ ch).labels.Nodup) : (rootMerge m₁ ch j m₂ c₂).IsShuffle := by
  rw [rootMerge_eq hj ht]
  have hk := m₁.two_le
  refine ⟨by omega, fun r => isShuffle_planar _ hj ht _, ?_⟩
  exact (monotone_sortP _).strictMono_of_injective
    ((first_planar_injective _ hj ht hnd).comp (Equiv.injective _))

/-- **The merged tree has the leaves of the tree.** -/
theorem labels_rootMerge (hj : ch j = STree.node m₂ c₂) (ht : (STree.node m₁ ch).IsShuffle) :
    (rootMerge m₁ ch j m₂ c₂).labels = (STree.node m₁ ch).labels := by
  rw [rootMerge_eq hj ht, STree.labels_node, STree.labels_node]
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp (sortP (planar ch j c₂ (mergeN_eq m₁ l)))
      (fun r => (planar ch j c₂ (mergeN_eq m₁ l) r).labels),
    ← Equiv.sum_comp (posEquivF j l (k + l - 1) (mergeN_eq m₁ l)), Fintype.sum_sum_type]
  simp only [planar_inl, planar_inr]
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun a => (ch a).labels) j, hj, STree.labels_node,
    add_comm]

lemma kids_planar_sortP {N : ℕ} (Q : Fin N → STree (VMono G)) (r : Fin N) :
    kids (Q ∘ sortP Q) ((sortP Q).symm r : ℕ) = cutRoot (toBar (Q r)) := by
  rw [kids_fin]
  simp

omit [Fintype G] [DecidableEq G] in
lemma key_cutRoot (y : BarTree G) : LTree.key (cutRoot y) = LTree.key y := by
  cases y <;> rfl

/-- **Merging the edge above a child of the root, on bar trees**: the bar tree of the merged
tree is the bar tree of the tree with that edge merged. -/
theorem toBar_rootMerge (hj : ch j = STree.node m₂ c₂) (ht : (STree.node m₁ ch).IsShuffle)
    (hnd : (STree.node m₁ ch).labels.Nodup) :
    toBar (rootMerge m₁ ch j m₂ c₂) = mergeK (toBar (STree.node m₁ ch)) (vkey (ch j)) := by
  set hN := mergeN_eq m₁ l
  set Q := planar ch j c₂ hN with hQ
  set π := sortP Q with hπ
  have ht₂ : (STree.node m₂ c₂).IsShuffle := hj ▸ ht.child j
  rw [rootMerge_eq hj ht, toBar_node]
  show (liftW false (mergedMono m₁.1 j m₂.1 hN π)).plug (kids (Q ∘ π)) = _
  rw [mergedMono, mergeMono, liftW_false_plug, plug_plug]
  obtain ⟨e, l', r', hm⟩ := m₁.exists_node
  rw [toBar_node, hm, mergeK_plug_liftW (kids ch) false e l' r' _ (by simp), ← hm]
  refine plug_congr fun a ha => ?_
  rw [labels_liftW] at ha
  have hak := m₁.lt ha
  by_cases haj : a = (j : ℕ)
  · have hja : (⟨a, hak⟩ : Fin k) = j := Fin.ext haj
    simp only [if_pos haj]
    rw [liftW_false_plug, plug_plug]
    obtain ⟨e₂, l₂, r₂, hm₂⟩ := m₂.exists_node
    have hkid : kids ch a = (liftW true (LTree.node e₂ l₂ r₂)).plug (kids c₂) := by
      rw [kids_of_lt ch hak, hja, hj, toBar_node, hm₂]
      rfl
    have hkey : LTree.key ((liftW true (LTree.node e₂ l₂ r₂)).plug (kids c₂)) = vkey (ch j) := by
      rw [← hkid, kids_of_lt ch hak, hja, key_cutRoot, key_toBar (ht.child j)]
    rw [hkid, mergeK_plug_liftW_root _ true e₂ l₂ r₂ _ ⟨rfl, hkey⟩, ← hm₂]
    refine plug_congr fun i hi => ?_
    rw [labels_liftW] at hi
    have hil := m₂.lt hi
    show kids (Q ∘ π) (rk₂ j hN π i) = kids c₂ i
    rw [show rk₂ j hN π i = rk₂ j hN π ((⟨i, hil⟩ : Fin l) : ℕ) from rfl, rk₂_of, hπ,
      kids_planar_sortP, hQ, planar_inr, kids_of_lt c₂ hil]
  · have hja : (⟨a, hak⟩ : Fin k) ≠ j := fun h => haj (congrArg Fin.val h)
    simp only [if_neg haj]
    show kids (Q ∘ π) (rk₁ j hN π a) = _
    rw [show rk₁ j hN π a = rk₁ j hN π ((⟨⟨a, hak⟩, hja⟩ : Without (Fin k) j).1 : ℕ) from rfl,
      rk₁_of, hπ, kids_planar_sortP, hQ, planar_inl, ← kids_of_lt ch hak]
    refine (mergeK_of_not_mem _ fun hmem => ?_).symm
    rw [kids_of_lt ch hak, cutKeys_cutRoot_toBar _ (ht.child _), List.mem_toFinset] at hmem
    have h1 := (mem_preKeys (ht.child _) hmem).1
    have h2 : (ofLex (vkey (ch j))).1 ∈ (ch j).labels := first_mem (ht.child j)
    exact not_mem_of_node hnd hja h1 h2

end RootMerge

/-! ## Merging an edge at any depth -/

section MergeT

open ShuffleBar STree LTree

lemma mem_flatten_ofFn {α : Type*} {k : ℕ} (f : Fin k → List α) (x : α) :
    x ∈ (List.ofFn f).flatten ↔ ∃ j, x ∈ f j := by
  simp only [List.mem_flatten, List.mem_ofFn]
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, hx⟩
    exact ⟨j, hx⟩
  · rintro ⟨j, hx⟩
    exact ⟨_, ⟨j, rfl⟩, hx⟩

lemma preKeys_eq_cons {B : ℕ → Type*} {t : STree B} (hw : t.weight ≠ 0) :
    preKeys t = vkey t :: (preKeys t).tail := by
  cases t with
  | leaf => simp [STree.weight] at hw
  | node β ch => rfl

lemma weight_ne_zero_of_mem {B : ℕ → Type*} {t : STree B} {κ : ℕ ×ₗ ℕ} (h : κ ∈ preKeys t) :
    t.weight ≠ 0 := by
  cases t with
  | leaf => simp [preKeys] at h
  | node β ch => simp [STree.weight]

variable {G : Type} [Fintype G] [DecidableEq G]

/-- Merging the edge above the child `j` of the root, a leaf leaving the tree as it is. -/
noncomputable def mergeAt {k : ℕ} (m : VMono G k) (ch : Fin k → STree (VMono G)) (j : Fin k) :
    STree (VMono G) → STree (VMono G)
  | .leaf _ => .node m ch
  | .node m₂ c₂ => rootMerge m ch j m₂ c₂

open Classical in
/-- **Merging the edge above the vertex of key `κ`** of a shuffle tree of monomials: at the child
of the root of key `κ` if there is one (`rootMerge`), and in every child otherwise. -/
noncomputable def mergeT : STree (VMono G) → ℕ ×ₗ ℕ → STree (VMono G)
  | .leaf a, _ => .leaf a
  | .node m ch, κ =>
    if h : ∃ j, vkey (ch j) = κ ∧ (ch j).weight ≠ 0 then mergeAt m ch h.choose (ch h.choose)
    else .node m fun j => mergeT (ch j) κ

lemma mergeT_of_not_mem : ∀ {t : STree (VMono G)} {κ : ℕ ×ₗ ℕ}, κ ∉ preKeys t → mergeT t κ = t
  | .leaf _, _, _ => rfl
  | .node m ch, κ, h => by
    have hmem : ∀ j, κ ∉ preKeys (ch j) := fun j hj => h (by
      rw [preKeys_node]
      exact List.mem_cons_of_mem _ ((mem_flatten_ofFn _ _).2 ⟨j, hj⟩))
    have hno : ¬∃ j, vkey (ch j) = κ ∧ (ch j).weight ≠ 0 := by
      rintro ⟨j, rfl, hw⟩
      exact hmem j (by rw [preKeys_eq_cons hw]; exact List.mem_cons_self ..)
    rw [mergeT, dif_neg hno]
    congr 1
    funext j
    exact mergeT_of_not_mem (hmem j)

variable {k : ℕ} {m : VMono G k} {ch : Fin k → STree (VMono G)}

lemma mergeT_root (ht : (STree.node m ch).IsShuffle) {j : Fin k} {l : ℕ} {m₂ : VMono G l}
    {c₂ : Fin l → STree (VMono G)} (hj : ch j = STree.node m₂ c₂) :
    mergeT (STree.node m ch) (vkey (ch j)) = rootMerge m ch j m₂ c₂ := by
  have hex : ∃ j', vkey (ch j') = vkey (ch j) ∧ (ch j').weight ≠ 0 :=
    ⟨j, rfl, by rw [hj]; simp [STree.weight]⟩
  rw [mergeT, dif_pos hex]
  have hc : hex.choose = j := by
    have := congrArg (fun κ : ℕ ×ₗ ℕ => (ofLex κ).1) hex.choose_spec.1
    simp only [vkey, ofLex_toLex] at this
    exact ht.mono.injective this
  rw [hc, hj]
  rfl

lemma nodup_preKeys_child (ht : (STree.node m ch).IsShuffle)
    (hnd : (STree.node m ch).labels.Nodup) (j : Fin k) : (preKeys (ch j)).Nodup := by
  have := nodup_tail_preKeys ht hnd
  rw [preKeys_node, List.tail_cons] at this
  exact (List.nodup_flatten.1 this).1 _ (List.mem_ofFn.2 ⟨j, rfl⟩)

lemma not_mem_preKeys_of_ne (ht : (STree.node m ch).IsShuffle)
    (hnd : (STree.node m ch).labels.Nodup) {a b : Fin k} (hab : a ≠ b) {κ : ℕ ×ₗ ℕ}
    (hκ : κ ∈ preKeys (ch a)) : κ ∉ preKeys (ch b) := fun h' =>
  not_mem_of_node hnd hab (mem_preKeys (ht.child a) hκ).1 (mem_preKeys (ht.child b) h').1

lemma mergeT_child (ht : (STree.node m ch).IsShuffle) (hnd : (STree.node m ch).labels.Nodup)
    {j₀ : Fin k} {κ : ℕ ×ₗ ℕ} (hκ : κ ∈ (preKeys (ch j₀)).tail) :
    mergeT (STree.node m ch) κ = STree.node m (Function.update ch j₀ (mergeT (ch j₀) κ)) := by
  have hκ' : κ ∈ preKeys (ch j₀) := List.mem_of_mem_tail hκ
  have hno : ¬∃ j, vkey (ch j) = κ ∧ (ch j).weight ≠ 0 := by
    rintro ⟨j, rfl, hw⟩
    by_cases hjj : j = j₀
    · subst hjj
      have hnd' := nodup_preKeys_child ht hnd j
      rw [preKeys_eq_cons hw] at hnd'
      exact (List.nodup_cons.1 hnd').1 hκ
    · exact not_mem_preKeys_of_ne ht hnd (Ne.symm hjj) hκ'
        (by rw [preKeys_eq_cons hw]; exact List.mem_cons_self ..)
  rw [mergeT, dif_neg hno]
  congr 1
  funext j
  by_cases hjj : j = j₀
  · subst hjj
    rw [Function.update_self]
  · rw [Function.update_of_ne hjj]
    exact mergeT_of_not_mem (not_mem_preKeys_of_ne ht hnd (Ne.symm hjj) hκ')

omit [Fintype G] [DecidableEq G] in
lemma cutRoot_mergeK {y : BarTree G} (hy : rootFlag y = false) {κ : ℕ ×ₗ ℕ}
    (hκ : LTree.key y ≠ κ) : cutRoot (mergeK y κ) = mergeK (cutRoot y) κ := by
  cases y with
  | leaf => rfl
  | node d l r =>
    simp only [rootFlag] at hy
    have h1 : mergeK (LTree.node d l r) κ = LTree.node d (mergeK l κ) (mergeK r κ) := by
      rw [mergeK, if_neg (by simp [hy])]
    have h2 : mergeK (cutRoot (LTree.node d l r)) κ
        = LTree.node (d.1, true) (mergeK l κ) (mergeK r κ) := by
      rw [cutRoot, mergeK, if_neg]
      rintro ⟨-, h⟩
      exact hκ h
    rw [h1, h2]
    rfl

/-- **Merging an edge of a shuffle tree of monomials**: for `κ` the key of a vertex other than the
root, the merged tree is a shuffle tree with the same leaves, and its bar tree is the bar tree with
the cut edge `κ` merged. -/
theorem mergeT_spec : ∀ (t : STree (VMono G)) (κ : ℕ ×ₗ ℕ), t.IsShuffle → t.labels.Nodup →
    κ ∈ (preKeys t).tail → (mergeT t κ).IsShuffle ∧ (mergeT t κ).labels = t.labels ∧
      toBar (mergeT t κ) = mergeK (toBar t) κ
  | .leaf _, _, _, _, h => by simp [preKeys] at h
  | .node (k := k) m ch, κ, ht, hnd, hκ => by
    rw [preKeys_node, List.tail_cons, mem_flatten_ofFn] at hκ
    obtain ⟨j₀, hj₀⟩ := hκ
    have hw := weight_ne_zero_of_mem hj₀
    rw [preKeys_eq_cons hw, List.mem_cons] at hj₀
    rcases hj₀ with rfl | hj₀
    · obtain ⟨l, m₂, c₂, hc⟩ : ∃ (l : ℕ) (m₂ : VMono G l) (c₂ : Fin l → STree (VMono G)),
          ch j₀ = STree.node m₂ c₂ := by
        cases h : ch j₀ with
        | leaf => rw [h] at hw; simp [STree.weight] at hw
        | node m₂ c₂ => exact ⟨_, m₂, c₂, rfl⟩
      rw [mergeT_root ht hc]
      exact ⟨isShuffle_rootMerge hc ht hnd, labels_rootMerge hc ht, toBar_rootMerge hc ht hnd⟩
    · have hjs := ht.child j₀
      have hjnd := nodup_of_node hnd j₀
      obtain ⟨ih1, ih2, ih3⟩ := mergeT_spec (ch j₀) κ hjs hjnd hj₀
      rw [mergeT_child ht hnd hj₀]
      have hfirst : ∀ j, (Function.update ch j₀ (mergeT (ch j₀) κ) j).first = (ch j).first := by
        intro j
        by_cases hjj : j = j₀
        · subst hjj
          rw [Function.update_self]
          exact first_eq_of_labels ih1 hjs ih2
        · rw [Function.update_of_ne hjj]
      refine ⟨⟨ht.pos, fun j => ?_, ?_⟩, ?_, ?_⟩
      · by_cases hjj : j = j₀
        · subst hjj
          rw [Function.update_self]
          exact ih1
        · rw [Function.update_of_ne hjj]
          exact ht.child j
      · simp only [hfirst]
        exact ht.mono
      · simp only [STree.labels_node]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hjj : j = j₀
        · subst hjj
          rw [Function.update_self, ih2]
        · rw [Function.update_of_ne hjj]
      · have hne : LTree.key (toBar (ch j₀)) ≠ κ := by
          rw [key_toBar hjs]
          intro h
          have hnd' := nodup_preKeys_child ht hnd j₀
          rw [preKeys_eq_cons hw] at hnd'
          exact (List.nodup_cons.1 hnd').1 (h ▸ hj₀)
        rw [toBar_node, toBar_node]
        obtain ⟨e, l', r', hm⟩ := m.exists_node
        rw [hm, mergeK_plug_liftW (kids ch) false e l' r' _ (by simp), ← hm]
        refine plug_congr fun a ha => ?_
        rw [labels_liftW] at ha
        have hak := m.lt ha
        rw [kids_of_lt _ hak, kids_of_lt _ hak]
        by_cases haj : (⟨a, hak⟩ : Fin k) = j₀
        · rw [haj, Function.update_self, ih3]
          exact cutRoot_mergeK (rootFlag_toBar _) hne
        · rw [Function.update_of_ne haj]
          refine (mergeK_of_not_mem _ ?_).symm
          rw [cutKeys_cutRoot_toBar _ (ht.child _), List.mem_toFinset]
          exact not_mem_preKeys_of_ne ht hnd (Ne.symm haj) (List.mem_of_mem_tail hj₀)

end MergeT

/-! ## The sign of merging an edge -/

section MergeSign

open ShuffleBar STree LTree

section Planar

variable {B : ℕ → Type*} {k l N : ℕ} (ch : Fin k → STree B) (j : Fin k) (c₂ : Fin l → STree B)
  (hN : N + 1 = k + l)

lemma planar_of_lt {r : ℕ} (hr : r < N) (h : r < j) :
    planar ch j c₂ hN ⟨r, hr⟩ = ch ⟨r, by omega⟩ := by
  have hne : (⟨r, by omega⟩ : Fin k) ≠ j := fun e => by
    have := congrArg Fin.val e
    simp only at this
    omega
  rw [show (⟨r, hr⟩ : Fin N) = posEquivF j l N hN (Sum.inl ⟨⟨r, by omega⟩, hne⟩) from
    Fin.ext (posEquivF_inl_of_lt j hN ⟨⟨r, by omega⟩, hne⟩ h).symm, planar_inl]

lemma planar_of_mid {r : ℕ} (hr : r < N) (h₁ : (j : ℕ) ≤ r) (h₂ : r < j + l) :
    planar ch j c₂ hN ⟨r, hr⟩ = c₂ ⟨r - j, by omega⟩ := by
  rw [show (⟨r, hr⟩ : Fin N) = posEquivF j l N hN (Sum.inr ⟨r - j, by omega⟩) from
    Fin.ext (by rw [posEquivF_inr]; simp only; omega), planar_inr]

lemma planar_of_gt {r : ℕ} (hr : r < N) (h : j + l ≤ r) :
    planar ch j c₂ hN ⟨r, hr⟩ = ch ⟨r + 1 - l, by omega⟩ := by
  have hne : (⟨r + 1 - l, by omega⟩ : Fin k) ≠ j := fun e => by
    have := congrArg Fin.val e
    simp only at this
    omega
  have hgt : j < (⟨⟨r + 1 - l, by omega⟩, hne⟩ : Without (Fin k) j).1 := by
    show (j : ℕ) < r + 1 - l
    omega
  have := posEquivF_inl_of_gt j hN _ hgt
  rw [show (⟨r, hr⟩ : Fin N) = posEquivF j l N hN (Sum.inl ⟨⟨r + 1 - l, by omega⟩, hne⟩) from
    Fin.ext (by simp only at this ⊢; omega), planar_inl]

/-- **The children of the merged vertex in planar order**, listed: those of the vertex before `j`,
those of the child, then those of the vertex after `j`. -/
lemma ofFn_planar {β : Type*} (g : STree B → β) :
    (List.ofFn fun r => g (planar ch j c₂ hN r))
      = (List.ofFn fun a => g (ch a)).take j ++ (List.ofFn fun i => g (c₂ i))
        ++ (List.ofFn fun a => g (ch a)).drop (j + 1) := by
  have hj := j.2
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_take, List.length_drop]
    omega
  · intro r h₁ h₂
    have hr : r < N := by simpa using h₁
    rw [List.getElem_ofFn]
    simp only [List.getElem_append, List.length_append, List.length_take, List.length_ofFn,
      List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    split_ifs with ha hb
    · rw [planar_of_lt ch j c₂ hN hr (by omega)]
    · rw [planar_of_mid ch j c₂ hN hr (by omega) (by omega)]
      congr 2
      ext
      simp only
      omega
    · rw [planar_of_gt ch j c₂ hN hr (by omega)]
      congr 2
      ext
      simp only
      omega

end Planar

lemma flatten_ofFn_split {α : Type*} {k : ℕ} (f : Fin k → List α) (j : Fin k) :
    (List.ofFn f).flatten
      = ((List.ofFn f).take j).flatten ++ (f j ++ ((List.ofFn f).drop (j + 1)).flatten) := by
  conv_lhs => rw [← List.take_append_drop j (List.ofFn f)]
  rw [List.drop_eq_getElem_cons (by simp), List.getElem_ofFn, List.flatten_append,
    List.flatten_cons]

lemma take_ofFn_update {α β : Type*} {k : ℕ} (g : α → β) (f : Fin k → α) (j : Fin k) (x : α) :
    (List.ofFn fun i => g (Function.update f j x i)).take j = (List.ofFn fun i => g (f i)).take j
    := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_take, List.getElem_ofFn]
    rw [Function.update_of_ne]
    intro e
    have := congrArg Fin.val e
    simp only [List.length_take, List.length_ofFn] at h₁
    simp only at this
    omega

lemma drop_ofFn_update {α β : Type*} {k : ℕ} (g : α → β) (f : Fin k → α) (j : Fin k) (x : α) :
    (List.ofFn fun i => g (Function.update f j x i)).drop (j + 1)
      = (List.ofFn fun i => g (f i)).drop (j + 1) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_drop, List.getElem_ofFn]
    rw [Function.update_of_ne]
    intro e
    have := congrArg Fin.val e
    simp only at this
    omega

variable {G : Type} [Fintype G] [DecidableEq G]

/-- The leaves of different children of a merged vertex are disjoint. -/
lemma disjoint_planar {k l N : ℕ} {m₁ : VMono G k} {ch : Fin k → STree (VMono G)} {j : Fin k}
    {m₂ : VMono G l} {c₂ : Fin l → STree (VMono G)} (hN : N + 1 = k + l)
    (hj : ch j = STree.node m₂ c₂) (hnd : (STree.node m₁ ch).labels.Nodup) {r r' : Fin N}
    (hrr : r ≠ r') {x : ℕ} (hx : x ∈ (planar ch j c₂ hN r).labels) :
    x ∉ (planar ch j c₂ hN r').labels := by
  have hnd₂ : (STree.node m₂ c₂).labels.Nodup := hj ▸ nodup_of_node hnd j
  have hsub : ∀ i, (c₂ i).labels ≤ (ch j).labels := fun i => by
    rw [hj]
    exact labels_le_node _ _ i
  obtain ⟨x₁, rfl⟩ := (posEquivF j l N hN).surjective r
  obtain ⟨x₂, rfl⟩ := (posEquivF j l N hN).surjective r'
  have hne : x₁ ≠ x₂ := fun e => hrr (by rw [e])
  intro hx'
  rcases x₁ with a | i <;> rcases x₂ with b | i' <;> simp only [planar_inl, planar_inr] at hx hx'
  · exact not_mem_of_node hnd (fun e => hne (by rw [Subtype.ext e])) hx hx'
  · exact not_mem_of_node hnd a.2 hx (Multiset.mem_of_le (hsub i') hx')
  · exact not_mem_of_node hnd b.2 hx' (Multiset.mem_of_le (hsub i) hx)
  · exact not_mem_of_node hnd₂ (fun e => hne (by rw [e])) hx hx'

variable (K : Type u) [CommRing K]

/-- The Koszul sign of sorting the children of the vertex merged with its child `j`. -/
noncomputable def kzRoot {k : ℕ} (m₁ : VMono G k) (ch : Fin k → STree (VMono G)) (j : Fin k) :
    STree (VMono G) → K
  | .leaf _ => 1
  | .node (k := l) _ c₂ => kz K (fun r => preKeys (planar ch j c₂ (mergeN_eq m₁ l) r))
      (sortP (planar ch j c₂ (mergeN_eq m₁ l)))

open Classical in
/-- **The Koszul sign of merging the edge above the vertex of key `κ`**: the sign of sorting the
children of the merged vertex, a block of parity the number of vertices of its subtree. -/
noncomputable def kzAt : STree (VMono G) → ℕ ×ₗ ℕ → K
  | .leaf _, _ => 1
  | .node m ch, κ =>
    if h : ∃ j, vkey (ch j) = κ ∧ (ch j).weight ≠ 0 then kzRoot K m ch h.choose (ch h.choose)
    else ∏ j, kzAt (ch j) κ

lemma kzAt_of_not_mem : ∀ {t : STree (VMono G)} {κ : ℕ ×ₗ ℕ}, κ ∉ preKeys t → kzAt K t κ = 1
  | .leaf _, _, _ => rfl
  | .node m ch, κ, h => by
    have hmem : ∀ j, κ ∉ preKeys (ch j) := fun j hj => h (by
      rw [preKeys_node]
      exact List.mem_cons_of_mem _ ((mem_flatten_ofFn _ _).2 ⟨j, hj⟩))
    have hno : ¬∃ j, vkey (ch j) = κ ∧ (ch j).weight ≠ 0 := by
      rintro ⟨j, rfl, hw⟩
      exact hmem j (by rw [preKeys_eq_cons hw]; exact List.mem_cons_self ..)
    rw [kzAt, dif_neg hno]
    exact Finset.prod_eq_one fun j _ => kzAt_of_not_mem (hmem j)

lemma weight_mergeT_node {k : ℕ} (m : VMono G k) (ch : Fin k → STree (VMono G)) (κ : ℕ ×ₗ ℕ) :
    (mergeT (STree.node m ch) κ).weight ≠ 0 := by
  rw [mergeT]
  split_ifs with h
  · generalize h.choose = j
    cases ch j with
    | leaf => simp [mergeAt]
    | node m₂ c₂ =>
      simp only [mergeAt, rootMerge]
      split_ifs <;> simp [STree.weight]
  · simp [STree.weight]

/-- **The preorder of the merged tree**: removing the key `κ` from the keys of the vertices other
than the root and permuting the blocks of the children of the merged vertex by `π`, with the
Koszul sign `kzAt`. -/
theorem preKeys_mergeT : ∀ (t : STree (VMono G)) (κ : ℕ ×ₗ ℕ), t.IsShuffle → t.labels.Nodup →
    κ ∈ (preKeys t).tail → ∃ (P X Y S : List (ℕ ×ₗ ℕ)) (N : ℕ) (B : Fin N → List (ℕ ×ₗ ℕ))
      (π : Equiv.Perm (Fin N)), (preKeys t).tail = P ++ (X ++ κ :: Y) ++ S ∧
        (preKeys (mergeT t κ)).tail = P ++ (List.ofFn (B ∘ π)).flatten ++ S ∧
        (List.ofFn B).flatten = X ++ Y ∧ (∀ a b, a ≠ b → ∀ x ∈ B a, x ∉ B b) ∧
        kzAt K t κ = kz K B π
  | .leaf _, _, _, _, h => by simp [preKeys] at h
  | .node (k := k) m ch, κ, ht, hnd, hκ => by
    have hκ0 := hκ
    rw [preKeys_node, List.tail_cons, mem_flatten_ofFn] at hκ
    obtain ⟨j₀, hj₀⟩ := hκ
    have hw := weight_ne_zero_of_mem hj₀
    have hsplit := flatten_ofFn_split (fun a => preKeys (ch a)) j₀
    rw [preKeys_eq_cons hw, List.mem_cons] at hj₀
    rcases hj₀ with rfl | hj₀
    · obtain ⟨l, m₂, c₂, hc⟩ : ∃ (l : ℕ) (m₂ : VMono G l) (c₂ : Fin l → STree (VMono G)),
          ch j₀ = STree.node m₂ c₂ := by
        cases h : ch j₀ with
        | leaf => rw [h] at hw; simp [STree.weight] at hw
        | node m₂ c₂ => exact ⟨_, m₂, c₂, rfl⟩
      set hN := mergeN_eq m l
      set Q := planar ch j₀ c₂ hN with hQ
      have hpre : preKeys (ch j₀)
          = vkey (ch j₀) :: (List.ofFn fun i => preKeys (c₂ i)).flatten := by
        rw [hc, preKeys_node]
      refine ⟨[], ((List.ofFn fun a => preKeys (ch a)).take j₀).flatten,
        (List.ofFn fun i => preKeys (c₂ i)).flatten
          ++ ((List.ofFn fun a => preKeys (ch a)).drop (j₀ + 1)).flatten, [], _,
        fun r => preKeys (Q r), sortP Q, ?_, ?_, ?_, ?_, ?_⟩
      · rw [preKeys_node, List.tail_cons, hsplit, hpre]
        simp
      · rw [mergeT_root ht hc, rootMerge_eq hc ht, preKeys_node, List.tail_cons]
        simp only [List.nil_append, List.append_nil]
        rfl
      · rw [hQ, ofFn_planar ch j₀ c₂ hN preKeys, List.flatten_append, List.flatten_append]
        simp
      · intro a b hab x hx hx'
        have h1 := (mem_preKeys (isShuffle_planar hN hc ht a) hx).1
        have h2 := (mem_preKeys (isShuffle_planar hN hc ht b) hx').1
        exact disjoint_planar hN hc hnd hab h1 h2
      · have hex : ∃ j', vkey (ch j') = vkey (ch j₀) ∧ (ch j').weight ≠ 0 := ⟨j₀, rfl, hw⟩
        rw [kzAt, dif_pos hex]
        have hch : hex.choose = j₀ := by
          have := congrArg (fun κ : ℕ ×ₗ ℕ => (ofLex κ).1) hex.choose_spec.1
          simp only [vkey, ofLex_toLex] at this
          exact ht.mono.injective this
        rw [hch, hc]
        rfl
    · have hjs := ht.child j₀
      have hjnd := nodup_of_node hnd j₀
      obtain ⟨P, X, Y, S, N, B, π, h1, h2, h3, h4, h5⟩ := preKeys_mergeT (ch j₀) κ hjs hjnd hj₀
      obtain ⟨ih1, ih2, -⟩ := mergeT_spec (ch j₀) κ hjs hjnd hj₀
      have hwm : (mergeT (ch j₀) κ).weight ≠ 0 := by
        cases h : ch j₀ with
        | leaf => rw [h] at hw; simp [STree.weight] at hw
        | node m₂ c₂ => exact weight_mergeT_node m₂ c₂ κ
      have hvk : vkey (mergeT (ch j₀) κ) = vkey (ch j₀) := vkey_eq_of_labels ih1 hjs ih2
      set A := ((List.ofFn fun a => preKeys (ch a)).take j₀).flatten
      set C := ((List.ofFn fun a => preKeys (ch a)).drop (j₀ + 1)).flatten
      refine ⟨A ++ vkey (ch j₀) :: P, X, Y, S ++ C, N, B, π, ?_, ?_, h3, h4, ?_⟩
      · rw [preKeys_node, List.tail_cons, hsplit, preKeys_eq_cons hw, h1]
        simp
      · rw [mergeT_child ht hnd hj₀, preKeys_node, List.tail_cons,
          flatten_ofFn_split _ j₀]
        simp only [Function.update_self]
        rw [take_ofFn_update preKeys ch j₀ (mergeT (ch j₀) κ),
          drop_ofFn_update preKeys ch j₀ (mergeT (ch j₀) κ)]
        rw [preKeys_eq_cons hwm, h2, hvk]
        simp only [List.append_assoc, List.cons_append]
        rfl
      · have hno : ¬∃ j, vkey (ch j) = κ ∧ (ch j).weight ≠ 0 := by
          rintro ⟨j, rfl, hw'⟩
          by_cases hjj : j = j₀
          · subst hjj
            have hnd' := nodup_preKeys_child ht hnd j
            rw [preKeys_eq_cons hw'] at hnd'
            exact (List.nodup_cons.1 hnd').1 hj₀
          · exact not_mem_preKeys_of_ne ht hnd (Ne.symm hjj) (List.mem_of_mem_tail hj₀)
              (by rw [preKeys_eq_cons hw']; exact List.mem_cons_self ..)
        rw [kzAt, dif_neg hno, Fintype.prod_eq_single j₀ fun j hj =>
          kzAt_of_not_mem K (not_mem_preKeys_of_ne ht hnd (Ne.symm hj) (List.mem_of_mem_tail hj₀))]
        exact h5

/-- **The sign rule of merging an edge.** For a shuffle tree of monomials `t` with distinct leaves
and the key `κ` of a vertex other than the root, `sign t` times `(-1)` to the position of `κ` among
the keys of the vertices other than the root in preorder, times the Koszul sign of sorting the
children of the merged vertex, times the sign of the merged tree, is the sign `ShuffleBar.sgn` of
merging the cut edge `κ` of the bar tree. -/
theorem sign_mergeT {t : STree (VMono G)} (ht : t.IsShuffle) (hnd : t.labels.Nodup)
    {κ : ℕ ×ₗ ℕ} (hκ : κ ∈ (preKeys t).tail) :
    sign K t * (-1) ^ (preKeys t).tail.idxOf κ * kzAt K t κ * sign K (mergeT t κ)
      = ShuffleBar.sgn K (toBar t) κ := by
  obtain ⟨P, X, Y, S, N, B, π, h1, h2, h3, h4, h5⟩ := preKeys_mergeT K t κ ht hnd hκ
  have hL := nodup_tail_preKeys ht hnd
  rw [h1] at hL
  have hw : κ ∉ P ++ X := by
    intro hmem
    have hL' : (P ++ X ++ κ :: (Y ++ S)).Nodup := by simpa using hL
    exact (List.nodup_append.1 hL').2.2 _ hmem _ (List.mem_cons_self ..) rfl
  have hidx : (preKeys t).tail.idxOf κ = P.length + X.length := by
    rw [h1, show P ++ (X ++ κ :: Y) ++ S = (P ++ X) ++ κ :: (Y ++ S) by simp,
      List.idxOf_append_of_notMem hw, List.idxOf_cons_self, List.length_append, add_zero]
  rw [sign, sign, hidx, h5, h1, h2, sign_rule_list K P X Y S κ B π h3 h4 hw, sgn_toBar K ht hnd, h1]

end MergeSign

/-! ## The differential identity from the expansion of the bar differential -/

section Reduction

open ShuffleBar STree

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {G : Type} [Fintype G] [DecidableEq G]
  (c : ∀ k, Module.Basis (BinGen G k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen G k), GrSpecies.par (R := K) false (c k β) = c k β)

lemma nodup_smono {n : ℕ} (t : SMono (VMono G) (Finset.range n)) : t.1.labels.Nodup := by
  rw [t.2.2]
  exact Finset.nodup _

/-- **The merged tree as a shuffle basis index**: `mergeT t κ` for `κ` the key of a vertex other
than the root, and `t` otherwise. -/
noncomputable def mergeS {n : ℕ} (t : SMono (VMono G) (Finset.range n)) (κ : ℕ ×ₗ ℕ) :
    SMono (VMono G) (Finset.range n) :=
  if h : κ ∈ (preKeys t.1).tail then
    ⟨mergeT t.1 κ, (mergeT_spec t.1 κ t.2.1 (nodup_smono t) h).1,
      (mergeT_spec t.1 κ t.2.1 (nodup_smono t) h).2.1.trans t.2.2⟩
  else t

lemma mergeS_val {n : ℕ} (t : SMono (VMono G) (Finset.range n)) {κ : ℕ ×ₗ ℕ}
    (h : κ ∈ (preKeys t.1).tail) : (mergeS t κ).1 = mergeT t.1 κ := by
  rw [mergeS, dif_pos h]

/-- **The expansion of the bar differential over the edges**, on the basis vector of `t`: the
merged trees, with the sign `(-1)` to the position of the edge among the vertices other than the
root in preorder, times the Koszul sign of sorting the children of the merged vertex. This is the
statement left open; `ΦL_d_of_expansion` derives the differential identity from it. -/
def DExpansion {n : ℕ} (t : SMono (VMono G) (Finset.range n)) : Prop :=
  Bar.d (Ibar K E c hc) (Fin n) (barBasisN c hc n t)
    = ∑ κ ∈ (preKeys t.1).tail.toFinset,
        ((-1 : K) ^ (preKeys t.1).tail.idxOf κ * kzAt K t.1 κ) • barBasisN c hc n (mergeS t κ)

/-- **`Φ` intertwines the differentials on a basis vector whose bar differential expands over the
edges**: the sign rule `sign_mergeT` and the merged bar trees `mergeT_spec` turn the expansion
into `ShuffleBar.d`. -/
theorem ΦL_d_barBasisN_of_expansion {n : ℕ} (t : SMono (VMono G) (Finset.range n))
    (hexp : DExpansion c hc t) :
    ΦL c hc n (Bar.d (Ibar K E c hc) (Fin n) (barBasisN c hc n t))
      = ShuffleBar.d K (ΦL c hc n (barBasisN c hc n t)) := by
  have hnd := nodup_smono t
  unfold DExpansion at hexp
  rw [hexp, map_sum, Φ_barBasisN, map_smul, ShuffleBar.d_single, one_smul, ShuffleBar.dTree,
    cutKeys_toBar t.2.1, Finset.smul_sum]
  refine Finset.sum_congr rfl fun κ hκ => ?_
  rw [List.mem_toFinset] at hκ
  rw [map_smul, Φ_barBasisN, mergeS_val t hκ, (mergeT_spec t.1 κ t.2.1 hnd hκ).2.2, smul_smul,
    smul_smul]
  congr 1
  rw [← sign_mergeT K t.2.1 hnd hκ]
  linear_combination (-((-1 : K) ^ (preKeys t.1).tail.idxOf κ * kzAt K t.1 κ
    * sign K (mergeT t.1 κ))) * sign_mul_self K t.1

/-- **The differential identity from the expansion**: if the bar differential of every basis
vector of `B(T, Ī)(Fin n)` expands over the edges (`DExpansion`), then
`ΦL ∘ Bar.d = ShuffleBar.d ∘ ΦL` on all of `B(T, Ī)(Fin n)`. -/
theorem ΦL_d_of_expansion {n : ℕ} (hexp : ∀ t : SMono (VMono G) (Finset.range n),
      DExpansion c hc t) (x : BarCoop (Ibar K E c hc) (Fin n)) :
    ΦL c hc n (Bar.d (Ibar K E c hc) (Fin n) x) = ShuffleBar.d K (ΦL c hc n x) := by
  have h : (ΦL c hc n).comp (Bar.d (Ibar K E c hc) (Fin n))
      = (ShuffleBar.d K).comp (ΦL c hc n) :=
    (barBasisN c hc n).ext fun t => ΦL_d_barBasisN_of_expansion c hc t (hexp t)
  exact LinearMap.congr_fun h x

end Reduction

/-! ## The expansion on trees with at most two vertices -/

section ExpansionTwo

open ShuffleBar STree

lemma kz_eq_one_of_nil (K : Type u) [CommRing K] {α : Type*} {N : ℕ} {B : Fin N → List α}
    (hB : ∀ a, B a = []) (π : Equiv.Perm (Fin N)) : kz K B π = 1 := by
  unfold kz
  refine Finset.prod_eq_one fun a _ => Finset.prod_eq_one fun b _ => ?_
  split_ifs
  · rw [hB a, List.length_nil, zero_mul, pow_zero]
  · rfl

variable {G : Type} [Fintype G] [DecidableEq G]

lemma kzAt_root (K : Type u) [CommRing K] {k l : ℕ} {m : VMono G k}
    {ch : Fin k → STree (VMono G)} (ht : (STree.node m ch).IsShuffle) {j : Fin k}
    {m₂ : VMono G l} {c₂ : Fin l → STree (VMono G)} (hj : ch j = STree.node m₂ c₂) :
    kzAt K (STree.node m ch) (vkey (ch j))
      = kz K (fun r => preKeys (planar ch j c₂ (mergeN_eq m l) r))
          (sortP (planar ch j c₂ (mergeN_eq m l))) := by
  have hex : ∃ j', vkey (ch j') = vkey (ch j) ∧ (ch j').weight ≠ 0 :=
    ⟨j, rfl, by rw [hj]; simp [STree.weight]⟩
  rw [kzAt, dif_pos hex]
  have hch : hex.choose = j := by
    have := congrArg (fun κ : ℕ ×ₗ ℕ => (ofLex κ).1) hex.choose_spec.1
    simp only [vkey, ofLex_toLex] at this
    exact ht.mono.injective this
  rw [hch, hj]
  rfl

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  (c : ∀ k, Module.Basis (BinGen G k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen G k), GrSpecies.par (R := K) false (c k β) = c k β)

/-- **The expansion holds on the trees with one or two vertices**, by the computations of
`ShuffleBarSymDiff.lean`: a corolla has no edge and is killed by the bar differential, and a tree
with two vertices has one edge, of position zero, whose merged vertex has leaves as children. -/
theorem dExpansion_of_weight {n : ℕ} (t : SMono (VMono G) (Finset.range n))
    (hw : t.1.weight = 1 ∨ t.1.weight = 2) : DExpansion c hc t := by
  unfold DExpansion
  rcases hw with hw | hw
  · have htail : (preKeys t.1).tail = [] :=
      List.eq_nil_of_length_eq_zero (by rw [List.length_tail, length_preKeys, hw])
    rw [htail, d_barBasisN_of_weight_one c hc t hw]
    simp
  · obtain ⟨t, ht, hlab⟩ := t
    obtain ⟨k, m₁, ch, j₀, l, m₂, c₂, rfl, hj₀, hl₁, hl₂⟩ := exists_two hw
    have hnd : (STree.node m₁ ch).labels.Nodup := by
      rw [hlab]
      exact Finset.nodup _
    have hw₀ : (ch j₀).weight ≠ 0 := by
      rw [hj₀]
      simp [STree.weight]
    have hmem : vkey (ch j₀) ∈ (preKeys (STree.node m₁ ch)).tail := by
      rw [preKeys_node, List.tail_cons, mem_flatten_ofFn]
      exact ⟨j₀, by rw [preKeys_eq_cons hw₀]; exact List.mem_cons_self ..⟩
    have htail : (preKeys (STree.node m₁ ch)).tail = [vkey (ch j₀)] := by
      have hlen : (preKeys (STree.node m₁ ch)).tail.length = 1 := by
        rw [List.length_tail, length_preKeys, hw]
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 hlen
      rw [ha] at hmem ⊢
      rw [List.mem_singleton.1 hmem]
    have hleaf : ∀ r, preKeys (planar ch j₀ c₂ (mergeN_eq m₁ l) r) = [] := by
      intro r
      obtain ⟨x, rfl⟩ := (posEquivF j₀ l _ (mergeN_eq m₁ l)).surjective r
      rcases x with a | i
      · obtain ⟨y, hy⟩ := hl₁ a.1 a.2
        rw [planar_inl, hy]
        rfl
      · obtain ⟨y, hy⟩ := hl₂ i
        rw [planar_inr, hy]
        rfl
    have hspec := mergeT_spec (STree.node m₁ ch) (vkey (ch j₀)) ht hnd hmem
    have hkey : vkey (ch j₀) = twoKey ch j₀ := by
      rw [twoKey, kids_fin, key_cutRoot, key_toBar (ht.child j₀)]
    have hS : mergeS ⟨STree.node m₁ ch, ht, hlab⟩ (vkey (ch j₀))
        = corollaS ⟨_, twoMono_mem hj₀ hl₂ hl₁ ht hlab⟩ := by
      refine Subtype.ext ?_
      rw [mergeS_val _ hmem]
      refine (toBar_injective (isShuffle_corolla _) hspec.1 ?_).symm
      rw [toBar_corolla, hspec.2.2, hkey, mergeK_toBar_two hj₀ hl₂ hl₁]
    dsimp only
    rw [htail, d_barBasisN_two c hc m₁ ch j₀ m₂ c₂ hj₀ hl₁ hl₂ ht hlab]
    simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.sum_singleton,
      List.idxOf_cons_self, pow_zero, one_mul]
    rw [kzAt_root K ht hj₀, kz_eq_one_of_nil K hleaf, one_smul, hS]

end ExpansionTwo

end ShuffleBarSym

end Operad
