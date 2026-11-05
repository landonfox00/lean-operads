/-
# The associative operad on the binary side: a quadratic Gröbner basis and Koszulness

`Operad.ShuffleAnyAss` proves the associative operad Koszul as a shuffle operad with generators
of any arity (`Operad.AssShGen.isKoszul`, for `Operad.Rules.IsKoszul`). This file proves it Koszul
as a binary shuffle operad (`Operad.ShuffleBar.IsKoszul`), through the Gröbner criterion of
`Operad.ShuffleKoszul`, so that both shuffle predicates hold for the same operad
(`Operad.AssBin.isKoszul_and`). The binary framework takes any finite set of binary generators;
here it is `AssShGen 2`, the product `x₁x₂` and the opposite product `x₂x₁`.

* **The relators** (`AssBin.rel`) are the vectors on the twelve monomials of arity three whose
  evaluation to words vanishes (`AssBin.ev`, `AssBin.evL`): the relations of `Ass` in arity
  three. They are spanned by the six rules of `Operad.AssShGen.rules`, each leading left comb
  minus the monomial with the same word (`AssBin.rel_eq_span`).
* **The evaluation vanishes on the ideal** (`AssBin.idealOf_le_ker`): the word of a substitution
  at an edge is a function of the word of the substituted monomial (`AssBin.ev_substAt`).
* **A normal monomial is determined by its word** (`AssBin.ev_inj`). The windows of edges into
  the first slot with `x₁x₂` above `x₂x₁` are not leading, so `Operad.LTree.isNormal_iff` does not
  apply; instead, at a vertex whose first input is a vertex the window is leading unless it is
  `x₁x₂` above `x₂x₁` (`AssBin.eq_of_normal`), and the word of a normal monomial splits at its
  least label (`AssBin.exists_split`).
* Hence **the relators are a quadratic Gröbner basis** (`AssBin.isGroebner`) for the
  path-lexicographic key ranking `x₁x₂` below `x₂x₁`, the evaluation separating the normal
  monomials from the ideal; by the criterion of Dotsenko and Khoroshkin **the operad is Koszul**
  (`AssBin.isKoszul`), and so is the operad of the Koszul dual relators (`AssBin.isKoszul_dualRel`).

`AssBin.isKoszul_dualRel` concerns the shuffle operad presented by `Operad.ShuffleBar.dualRel` of
the relators. That this is again the shuffle operad of `Ass` is the classical self-duality of
`Ass`, proved for the symmetric binary presentation (`Operad.BinAss.dual`) and not here.

The two shuffle notions are not compared: the bar trees `Operad.BarTree` and the trees
`Operad.STree` are not translated into each other, so neither Koszulness is deduced from the
other. The two proofs only run in parallel, on the same rules.
-/
import Operad.ShuffleKoszul
import Operad.ShuffleDualKoszul
import Operad.ShuffleAnyAss

namespace Operad

instance : DecidableEq (AssShGen 2) := fun a b =>
  match a, b with
  | .mu, .mu => isTrue rfl
  | .op, .op => isTrue rfl
  | .mu, .op => isFalse fun h => by cases h
  | .op, .mu => isFalse fun h => by cases h

instance : Fintype (AssShGen 2) where
  elems := {.mu, .op}
  complete x := by cases x <;> simp

namespace AssBin

open LTree ShuffleBar AssShGen

/-! ## Evaluation to words -/

/-- **The evaluation of a binary tree to a word**: the arrangement of its leaves computed by the
products. -/
def ev : LTree (AssShGen 2) → List ℕ
  | leaf a => [a]
  | node e l r => ap e (ev l) (ev r)

/-- **The word of a tree arranges its leaves.** -/
theorem perm_ev : ∀ t : LTree (AssShGen 2), (ev t).Perm t.labels
  | leaf _ => List.Perm.refl _
  | node mu l r => (perm_ev l).append (perm_ev r)
  | node op l r => List.perm_append_comm.trans ((perm_ev l).append (perm_ev r))

/-- **The word of a tree is not empty.** -/
theorem ev_ne_nil : ∀ t : LTree (AssShGen 2), ev t ≠ []
  | leaf _ => List.cons_ne_nil _ _
  | node mu l r => by simp [ev, ap, ev_ne_nil l]
  | node op l r => by simp [ev, ap, ev_ne_nil r]

/-- **The word of a tree with a subtree replaced**, from the word of the new subtree. -/
def evRep : LTree (AssShGen 2) → List Bool → List ℕ → List ℕ
  | _, [], w => w
  | leaf a, _ :: _, _ => [a]
  | node e l r, false :: p, w => ap e (evRep l p w) (ev r)
  | node e l r, true :: p, w => ap e (ev l) (evRep r p w)

theorem ev_replaceAt : ∀ (t : LTree (AssShGen 2)) (p : List Bool) (u : LTree (AssShGen 2)),
    ev (t.replaceAt p u) = evRep t p (ev u)
  | leaf _, [], _ => rfl
  | node _ _ _, [], _ => rfl
  | leaf _, _ :: _, _ => rfl
  | node e l r, false :: p, u => by
    simp only [replaceAt, ev, evRep, ev_replaceAt l p u]
  | node e l r, true :: p, u => by
    simp only [replaceAt, ev, evRep, ev_replaceAt r p u]

/-- **The word of a grafted tree**: each leaf replaced by the word of its input. -/
theorem ev_plug (ins : ℕ → LTree (AssShGen 2)) : ∀ m : LTree (AssShGen 2),
    ev (m.plug ins) = (ev m).flatMap fun a => ev (ins a)
  | leaf a => by simp [plug, ev]
  | node mu l r => by simp [plug, ev, ap, ev_plug ins l, ev_plug ins r]
  | node op l r => by simp [plug, ev, ap, ev_plug ins l, ev_plug ins r]

/-- **The word of a substitution at an edge** is a function of the word of the substituted
monomial. -/
theorem ev_substAt (t : LTree (AssShGen 2)) (p : List Bool) (s : Bool) (m : LTree (AssShGen 2)) :
    ev (t.substAt p s m) = evRep t p ((ev m).flatMap fun a => ev ((t.subtreeAt p).winIns s a)) := by
  rw [substAt, ev_replaceAt, ev_plug]

/-! ## Arity three -/

/-- **The left combs** `e(f(0, 1), 2)` (`true`) and `e(f(0, 2), 1)` (`false`). -/
def lead3 (e f : AssShGen 2) : Bool → LTree (AssShGen 2)
  | true => node e (node f (leaf 0) (leaf 1)) (leaf 2)
  | false => node e (node f (leaf 0) (leaf 2)) (leaf 1)

/-- **The monomial with the same word as a left comb**, the tail of its rule
(`Operad.AssShGen.tailOf`). -/
def tail3 : AssShGen 2 → AssShGen 2 → Bool → LTree (AssShGen 2)
  | mu, mu, true => node mu (leaf 0) (node mu (leaf 1) (leaf 2))
  | mu, mu, false => node mu (leaf 0) (node op (leaf 1) (leaf 2))
  | op, op, true => node op (leaf 0) (node op (leaf 1) (leaf 2))
  | op, op, false => node op (leaf 0) (node mu (leaf 1) (leaf 2))
  | op, mu, true => node mu (node op (leaf 0) (leaf 2)) (leaf 1)
  | op, mu, false => node mu (node op (leaf 0) (leaf 1)) (leaf 2)
  | mu, op, _ => node mu (leaf 0) (node mu (leaf 1) (leaf 2))

/-- **The leading monomials**: the left combs `e(f(-, -), -)` with `(e, f) ≠ (x₁x₂, x₂x₁)`. -/
def leads : Set (LTree (AssShGen 2)) := {t | ∃ e f s, (e, f) ≠ (mu, op) ∧ t = lead3 e f s}

/-- The ranking of the decorations, for the path-lexicographic key. -/
def rk : AssShGen 2 → ℕ
  | mu => 0
  | op => 1

lemma lead3_mem (e f : AssShGen 2) (s : Bool) : lead3 e f s ∈ monomials 3 := by
  cases e <;> cases f <;> cases s <;> exact (mem_monomials 3 _).2 ⟨by decide, by decide⟩

lemma tail3_mem (e f : AssShGen 2) (s : Bool) : tail3 e f s ∈ monomials 3 := by
  cases e <;> cases f <;> cases s <;> exact (mem_monomials 3 _).2 ⟨by decide, by decide⟩

/-- Each rule: the tail differs from the leading monomial, has the same word, a smaller key, and
is not leading. -/
lemma spec3 {e f : AssShGen 2} (hef : (e, f) ≠ (mu, op)) (s : Bool) :
    tail3 e f s ≠ lead3 e f s ∧ ev (lead3 e f s) = ev (tail3 e f s) ∧
      pathKey rk 3 (tail3 e f s) < pathKey rk 3 (lead3 e f s) ∧ tail3 e f s ∉ leads := by
  cases e <;> cases f <;> cases s <;> first
    | exact absurd rfl hef
    | refine ⟨by decide, rfl, by decide, ?_⟩
      rintro ⟨e', f', s', hne, h⟩
      cases e' <;> cases f' <;> cases s' <;>
        first | exact absurd rfl hne | exact absurd h (by decide)

/-! ## Normal monomials -/

/-- **In a normal monomial, a vertex whose first input is a vertex is `x₁x₂` above `x₂x₁`**:
otherwise its window is leading. -/
theorem eq_of_normal {e f : AssShGen 2} {a b r : LTree (AssShGen 2)}
    (hs : (node e (node f a b) r).IsShuffle) (hnd : (node e (node f a b) r).labels.Nodup)
    (hn : IsNormal leads (node e (node f a b) r)) : e = mu ∧ f = op := by
  by_contra hne'
  have hne : (e, f) ≠ (mu, op) := fun h => hne' (Prod.mk.inj h)
  have hw : window e f false a.minLabel b.minLabel r.minLabel ∈ leads := by
    rcases window_left_shape hs hnd with h | h <;> rw [h]
    · exact ⟨e, f, true, hne, rfl⟩
    · exact ⟨e, f, false, hne, rfl⟩
  exact hn _ (by simp [windows]) hw

/-- **The word of a normal monomial, split at its least label**: the least label comes first
under `x₁x₂(a, -)`, last under `x₂x₁(a, -)`, and between the words of the two other inputs under
`x₁x₂(x₂x₁(a, -), -)`. -/
theorem exists_split {e : AssShGen 2} {l r : LTree (AssShGen 2)}
    (hs : (node e l r).IsShuffle) (hnd : (node e l r).labels.Nodup)
    (hn : IsNormal leads (node e l r)) :
    ∃ A B, ev (node e l r) = A ++ l.minLabel :: B ∧
      (e = mu ∧ l = leaf l.minLabel ∧ A = [] ∧ B = ev r ∨
        e = op ∧ l = leaf l.minLabel ∧ A = ev r ∧ B = [] ∨
        e = mu ∧ ev l = A ++ [l.minLabel] ∧ A ≠ [] ∧ B = ev r) := by
  cases l with
  | leaf a =>
    cases e
    · exact ⟨[], ev r, rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
    · exact ⟨ev r, [], by simp [ev, ap], Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)⟩
  | node g a b =>
    obtain ⟨rfl, rfl⟩ := eq_of_normal hs hnd hn
    have hm := minLabel_node_of_shuffle hs.2.1
    cases a with
    | leaf c =>
      rw [hm, minLabel_leaf]
      exact ⟨ev b, ev r, by simp [ev, ap], Or.inr (Or.inr ⟨rfl, by simp [ev, ap], ev_ne_nil b,
        rfl⟩)⟩
    | node g' a' b' =>
      have hnd' : (node op (node g' a' b') b).labels.Nodup :=
        (List.nodup_append.1 hnd).1
      exact absurd (eq_of_normal hs.2.1 hnd' hn.left).1 (fun h => by cases h)

/-- **A normal monomial is determined by its word.** -/
theorem ev_inj (x : LTree (AssShGen 2)) : ∀ {y : LTree (AssShGen 2)}, x.IsShuffle →
    y.IsShuffle → x.labels.Nodup → y.labels.Nodup → IsNormal leads x → IsNormal leads y →
    ev x = ev y → x = y := by
  induction x with
  | leaf a =>
    intro y _ _ _ _ _ _ h
    cases y with
    | leaf b =>
      simp only [ev, List.singleton_inj] at h
      rw [h]
    | node e l r =>
      have h2 := (perm_ev (node e l r)).length_eq
      rw [← h, length_labels] at h2
      have := arity_pos l
      have := arity_pos r
      simp only [ev, List.length_singleton, arity] at h2
      omega
  | node e l r ihl ihr =>
    intro y hs hs' hn hn' hg hg' h
    cases y with
    | leaf b =>
      have h2 := (perm_ev (node e l r)).length_eq
      rw [h, length_labels] at h2
      have := arity_pos l
      have := arity_pos r
      simp only [ev, List.length_singleton, arity] at h2
      omega
    | node e' l' r' =>
      have hm : l.minLabel = l'.minLabel := by
        rw [← minLabel_node_of_shuffle hs, ← minLabel_node_of_shuffle hs']
        exact minLabel_eq_of_perm ((perm_ev _).symm.trans (h ▸ perm_ev _))
      have hnd : (ev (node e l r)).Nodup := (perm_ev _).nodup_iff.2 hn
      have hnl := (List.nodup_append.1 hn).1
      have hnr := (List.nodup_append.1 hn).2.1
      have hnl' := (List.nodup_append.1 hn').1
      have hnr' := (List.nodup_append.1 hn').2.1
      obtain ⟨A, B, hA, hx⟩ := exists_split hs hn hg
      obtain ⟨A', B', hA', hy⟩ := exists_split hs' hn' hg'
      rw [hA, List.nodup_middle, List.nodup_cons, List.mem_append, not_or, hm] at hnd
      obtain ⟨rfl, -, rfl⟩ :=
        (List.append_cons_inj_of_notMem hnd.1.1 hnd.1.2).1 (hA.symm.trans (h.trans hA'))
      have hR : ev r = ev r' → r = r' :=
        fun hrr => ihr hs.2.2 hs'.2.2 hnr hnr' hg.right hg'.right hrr
      rcases hx with ⟨rfl, hl1, rfl, rfl⟩ | ⟨rfl, hl1, rfl, rfl⟩ | ⟨rfl, hl1, hA0, rfl⟩ <;>
        rcases hy with ⟨rfl, hl1', hA0', hB'⟩ | ⟨rfl, hl1', hA0', hB'⟩ | ⟨rfl, hl1', hA0', hB'⟩
      · rw [hR hB', hl1, hl1', hm]
      · exact absurd hA0'.symm (ev_ne_nil r')
      · exact absurd rfl hA0'
      · exact absurd hA0' (ev_ne_nil r)
      · rw [hR hA0', hl1, hl1', hm]
      · exact absurd hB'.symm (ev_ne_nil r')
      · exact absurd hA0' hA0
      · exact absurd hB' (ev_ne_nil r)
      · rw [hR hB', ihl hs.2.1 hs'.2.1 hnl hnl' hg.left hg'.left (by rw [hl1, hl1', hm])]

/-! ## The relators -/

variable (K : Type*) [Field K]

/-- **The evaluation to words** in arity `n`: every monomial to its word. -/
noncomputable def evL (n : ℕ) : (Mono (AssShGen 2) n → K) →ₗ[K] (List ℕ →₀ K) :=
  ∑ σ, (LinearMap.proj σ).smulRight (Finsupp.single (ev σ.1) (1 : K))

/-- **The relators of the associative operad**: the vectors of arity three whose evaluation to
words vanishes, the relations of `Ass` in arity three. -/
noncomputable def rel : Submodule K (Mono (AssShGen 2) 3 → K) := LinearMap.ker (evL K 3)

variable {K}

lemma evL_apply {n : ℕ} (v : Mono (AssShGen 2) n → K) :
    evL K n v = ∑ σ, v σ • Finsupp.single (ev σ.1) 1 := by
  simp [evL]

/-- The evaluation of the vector of a monomial is its word. -/
lemma evL_vecOf {n : ℕ} {t : LTree (AssShGen 2)} (ht : t ∈ monomials n) :
    evL K n (vecOf K n t) = Finsupp.single (ev t) 1 := by
  rw [evL_apply, Finset.sum_eq_single ⟨t, ht⟩ (fun σ _ hσ => ?_) (by simp)]
  · simp [vecOf]
  · rw [show vecOf K n t σ = 0 from if_neg fun h => hσ (Subtype.ext h), zero_smul]

/-- **The evaluation vanishes on the ideal**: the word of a substitution at an edge is a
function of the word of the substituted monomial. -/
theorem idealOf_le_ker (n : ℕ) : idealOf K (rel K) n ≤ LinearMap.ker (evL K n) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨t, p, s, r, hr, he, rfl⟩
  set F : List ℕ → List ℕ :=
    fun w => evRep t.1 p (w.flatMap fun a => ev ((t.1.subtreeAt p).winIns s a))
  have h1 : ∀ σ : Mono (AssShGen 2) 3, evL K n (r σ • vecOf K n (t.1.substAt p s σ.1)) =
      Finsupp.mapDomain F (r σ • Finsupp.single (ev σ.1) 1) := fun σ => by
    rw [map_smul, evL_vecOf (substAt_mem_monomials t.2 he σ.2), ev_substAt,
      Finsupp.mapDomain_smul, Finsupp.mapDomain_single]
  rw [SetLike.mem_coe, LinearMap.mem_ker, substVec, map_sum, Finset.sum_congr rfl fun σ _ => h1 σ,
    ← Finsupp.mapDomain_finsetSum, ← evL_apply, LinearMap.mem_ker.1 hr, Finsupp.mapDomain_zero]

/-- **The evaluation is injective on the normal monomials**: a vector supported on them with no
word is zero. -/
theorem eq_zero_of_evL {n : ℕ} {v : Mono (AssShGen 2) n → K}
    (hv : v ∈ supportedOn K (normalSet leads n)) (h0 : evL K n v = 0) : v = 0 := by
  funext y
  by_cases hy : y ∈ normalSet leads n
  · have := congrArg (· (ev y.1)) h0
    simp only [evL_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.single_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finsupp.coe_zero, Pi.zero_apply] at this
    rw [Finset.sum_eq_single y (fun σ _ hσ => ?_) (by simp)] at this
    · simpa using this
    · split_ifs with h
      · by_contra hσ0
        have hσN : σ ∈ normalSet leads n := by
          by_contra hN
          exact hσ0 (hv σ hN)
        have hσm := (mem_monomials n σ.1).1 σ.2
        have hym := (mem_monomials n y.1).1 y.2
        exact hσ (Subtype.ext (ev_inj σ.1 hσm.1 hym.1 (hσm.2.nodup_iff.2 List.nodup_range)
          (hym.2.nodup_iff.2 List.nodup_range) hσN hy h))
      · rfl
  · exact hv y hy

/-- **A monomial of arity three is its own window.** -/
lemma windows_mono3 (σ : Mono (AssShGen 2) 3) : σ.1.windows = [σ.1] := by
  have hm := (mem_monomials 3 σ.1).1 σ.2
  obtain ⟨e, f, h | h | h⟩ := mono3_cases hm.1 hm.2 <;> rw [h] <;> rfl

/-- The left combs are distinct. -/
lemma lead3_inj {e f e' f' : AssShGen 2} {s s' : Bool} (h : lead3 e f s = lead3 e' f' s') :
    e = e' ∧ f = f' ∧ s = s' := by
  cases s <;> cases s' <;> simp_all [lead3]

/-- **The relators are spanned by the rules**: each leading left comb minus the monomial with the
same word, the rules of `Operad.AssShGen.rules`. -/
theorem rel_eq_span : rel K = Submodule.span K (Set.range fun r : AssShGen.Rule =>
    vecOf K 3 (lead3 r.1.1.1 r.1.1.2 r.2) - vecOf K 3 (tail3 r.1.1.1 r.1.1.2 r.2)) := by
  set g : AssShGen.Rule → Mono (AssShGen 2) 3 → K :=
    fun r => vecOf K 3 (lead3 r.1.1.1 r.1.1.2 r.2) - vecOf K 3 (tail3 r.1.1.1 r.1.1.2 r.2)
  have hg : ∀ r, g r ∈ rel K := fun r => by
    obtain ⟨-, hev, -, -⟩ := spec3 r.1.2 r.2
    rw [rel, LinearMap.mem_ker, map_sub, evL_vecOf (lead3_mem _ _ _), evL_vecOf (tail3_mem _ _ _),
      hev, sub_self]
  refine le_antisymm (fun v hv => ?_) (Submodule.span_le.2 ?_)
  · set u : Mono (AssShGen 2) 3 → K :=
      ∑ r : AssShGen.Rule, v ⟨lead3 r.1.1.1 r.1.1.2 r.2, lead3_mem _ _ _⟩ • g r
    have hu : u ∈ Submodule.span K (Set.range g) :=
      Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)
    have hw : v - u ∈ rel K :=
      Submodule.sub_mem _ hv (Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (hg r))
    have hN : v - u ∈ supportedOn K (normalSet leads 3) := by
      intro σ hσ
      have hσL : σ.1 ∈ leads := by
        by_contra hL
        refine hσ fun w hw => ?_
        rw [windows_mono3, List.mem_singleton] at hw
        exact hw ▸ hL
      obtain ⟨e, f, s, hne, hσ1⟩ := hσL
      have hval : ∀ r : AssShGen.Rule, g r σ =
          if lead3 e f s = lead3 r.1.1.1 r.1.1.2 r.2 then 1 else 0 := fun r => by
        have ht : σ.1 ≠ tail3 r.1.1.1 r.1.1.2 r.2 :=
          fun h => (spec3 r.1.2 r.2).2.2.2 (h ▸ hσ1 ▸ ⟨e, f, s, hne, rfl⟩)
        rw [hσ1] at ht
        simp only [g, Pi.sub_apply, vecOf, hσ1, if_neg ht, sub_zero]
      have hsum : u σ = v σ := by
        simp only [u, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hval, mul_ite, mul_one,
          mul_zero]
        rw [Finset.sum_eq_single (⟨⟨(e, f), hne⟩, s⟩ : AssShGen.Rule) (fun r _ hr => ?_)
          (by simp)]
        · rw [if_pos rfl]
          congr 1
          exact Subtype.ext hσ1.symm
        · rw [if_neg]
          intro h
          obtain ⟨h1, h2, h3⟩ := lead3_inj h
          exact hr (Prod.ext (Subtype.ext (Prod.ext h1.symm h2.symm)) h3.symm)
      rw [Pi.sub_apply, hsum, sub_self]
    have h0 := eq_zero_of_evL hN hw
    rw [sub_eq_zero.1 h0]
    exact hu
  · rintro _ ⟨r, rfl⟩
    exact hg r

/-! ## The Gröbner basis and Koszulness -/

variable (K) in
/-- **The relators are a quadratic Gröbner basis** for the path-lexicographic key, with the left
combs `e(f(-, -), -)`, `(e, f) ≠ (x₁x₂, x₂x₁)`, leading. -/
theorem isGroebner : IsGroebner K rk leads (rel K) where
  mem ℓ hℓ := by
    obtain ⟨e, f, s, -, rfl⟩ := hℓ
    exact lead3_mem e f s
  lead ℓ hℓ := by
    obtain ⟨e, f, s, hne, rfl⟩ := hℓ
    obtain ⟨hne', hev, hkey, -⟩ := spec3 hne s
    refine ⟨vecOf K 3 (lead3 e f s) - vecOf K 3 (tail3 e f s), ?_, ?_, fun σ hσ hσ0 => ?_⟩
    · rw [rel, LinearMap.mem_ker, map_sub, evL_vecOf (lead3_mem e f s),
        evL_vecOf (tail3_mem e f s), hev, sub_self]
    · simp [vecOf, hne'.symm]
    · by_cases hσt : σ.1 = tail3 e f s
      · rwa [hσt]
      · exact absurd (by simp [vecOf, hσ, hσt]) hσ0
  indep _ _ hv hN := eq_zero_of_evL hN (idealOf_le_ker _ hv)

variable (K) in
/-- **The associative operad is Koszul as a binary shuffle operad**, by the criterion of
Dotsenko and Khoroshkin. -/
theorem isKoszul : ShuffleBar.IsKoszul K (rel K) :=
  ShuffleBar.isKoszul K rk (isGroebner K)

variable (K) in
/-- **The Koszul dual relators of the associative operad present a Koszul operad.** -/
theorem isKoszul_dualRel : ShuffleBar.IsKoszul K (dualRel K (rel K)) :=
  ShuffleBar.isKoszul_dualRel (isGroebner K)

variable (K) in
/-- **The associative operad is Koszul in both shuffle senses**: as a binary shuffle operad,
presented by `rel`, and as a shuffle operad with generators of any arity, presented by
`AssShGen.rules`. -/
theorem isKoszul_and : ShuffleBar.IsKoszul K (rel K) ∧ (AssShGen.rules K).IsKoszul :=
  ⟨isKoszul K, AssShGen.isKoszul⟩

end AssBin

end Operad
