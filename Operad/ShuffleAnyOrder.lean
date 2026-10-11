/-
# The path-lexicographic order on shuffle monomials of any arity

**The word of a leaf** of a tree (`STree.word`): the letters of the vertices on the path from the
root to the leaf, each letter `ltr k e i` recording the generator `e` of arity `k` and the input
`i` through which the path leaves it (`STree.pathWord`). Words are compared
**degree-lexicographically** (`STree.DegLex`): by length, then lexicographically, for a
well-founded linear order on the letters; this order is well-founded (`STree.degLex_wf`) and
compatible with concatenation on both sides (`STree.DegLex.append`).

**The path-lexicographic order** (`STree.pathLex`): two monomials on the same set of leaves are
compared by the words of their leaves, lexicographically in the order of the leaves. It is
well-founded, and preserved by every context (`STree.pathLex_ctx`): inside a context, the word of a
leaf of the input at `a` is the word of the path to the hole, then the word of `a` in the inserted
monomial, then the word of the leaf in the input (`STree.word_ctx_in`); the words of the other
leaves do not depend on the inserted monomial (`STree.word_ctx_out`); and the first leaf where two
insertions differ is the least leaf of the input at the first leaf where the two monomials
differ, because the inputs increase with their least leaves. So the path-lexicographic order is
an **admissible order** (`STree.pathLexOrder`), and the Buchberger criterion
(`STree.isCompl_of_critical`) applies to it.
-/
import Operad.ShuffleAnyGroebner
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Data.List.Lex

universe v

namespace Operad

namespace STree

/-! ## The degree-lexicographic order on words -/

section DegLex

variable {L : Type*} [LinearOrder L]

/-- **The degree-lexicographic order on words**: by length, then lexicographically. -/
def DegLex (u w : List L) : Prop :=
  u.length < w.length ∨ u.length = w.length ∧ List.Lex (· < ·) u w

theorem lex_trans : ∀ {u v w : List L}, List.Lex (· < ·) u v → List.Lex (· < ·) v w →
    List.Lex (· < ·) u w
  | _, _, _, .nil, .cons _ => .nil
  | _, _, _, .nil, .rel _ => .nil
  | _, _, _, .cons h₁, .cons h₂ => .cons (lex_trans h₁ h₂)
  | _, _, _, .cons _, .rel h₂ => .rel h₂
  | _, _, _, .rel h₁, .cons _ => .rel h₁
  | _, _, _, .rel h₁, .rel h₂ => .rel (h₁.trans h₂)

theorem lex_append_right : ∀ {u w : List L}, List.Lex (· < ·) u w → u.length = w.length →
    ∀ Q : List L, List.Lex (· < ·) (u ++ Q) (w ++ Q)
  | _, _, .nil, h, _ => by simp at h
  | _, _, .cons hl, h, Q => .cons (lex_append_right hl (by simpa using h) Q)
  | _, _, .rel hr, _, _ => .rel hr

theorem DegLex.trans {u v w : List L} : DegLex u v → DegLex v w → DegLex u w := by
  rintro (h₁ | ⟨h₁, l₁⟩) (h₂ | ⟨h₂, l₂⟩)
  · exact Or.inl (h₁.trans h₂)
  · exact Or.inl (h₂ ▸ h₁)
  · exact Or.inl (h₁ ▸ h₂)
  · exact Or.inr ⟨h₁.trans h₂, lex_trans l₁ l₂⟩

/-- **Concatenation on both sides preserves the degree-lexicographic order.** -/
theorem DegLex.append {u w : List L} (h : DegLex u w) (P Q : List L) :
    DegLex (P ++ (u ++ Q)) (P ++ (w ++ Q)) := by
  rcases h with h | ⟨h, hl⟩
  · left
    simp only [List.length_append]
    omega
  · exact Or.inr ⟨by simp only [List.length_append, h],
      List.Lex.append_left _ (lex_append_right hl h Q) P⟩

/-- Words of the same length, compared lexicographically. -/
def LexEq (u w : List L) : Prop := u.length = w.length ∧ List.Lex (· < ·) u w

variable [WellFoundedLT L]

theorem acc_lexEq_cons {n : ℕ} (ih : ∀ u : List L, u.length = n → Acc LexEq u) :
    ∀ (b : L) (w : List L), w.length = n → Acc LexEq (b :: w) := by
  intro b
  induction b using WellFoundedLT.induction with
  | _ b ihb =>
  intro w hw
  induction ih w hw with
  | intro w _ ihw =>
  refine ⟨_, fun v hv => ?_⟩
  obtain ⟨hlen, hlex⟩ := hv
  cases v with
  | nil => simp at hlen
  | cons a u =>
    have hu : u.length = w.length := by simpa using hlen
    cases hlex with
    | cons h => exact ihw u ⟨hu, h⟩ (hu.trans hw)
    | rel h => exact ihb a h u (hu.trans hw)

theorem acc_lexEq : ∀ (n : ℕ) (u : List L), u.length = n → Acc LexEq u
  | 0, u, hu => by
    rw [List.length_eq_zero_iff] at hu
    subst hu
    exact ⟨_, fun v hv => by cases hv.2⟩
  | n + 1, u, hu => by
    cases u with
    | nil => simp at hu
    | cons b w => exact acc_lexEq_cons (acc_lexEq n) b w (by simpa using hu)

/-- **The degree-lexicographic order is well-founded.** -/
theorem degLex_wf : WellFounded (DegLex (L := L)) := by
  have h : WellFounded (Prod.Lex (· < ·) LexEq : ℕ × List L → ℕ × List L → Prop) :=
    ⟨fun ⟨n, u⟩ => Prod.lexAccessible (wellFounded_lt.apply n)
      (fun u => acc_lexEq u.length u rfl) u⟩
  refine Subrelation.wf (fun {u w} huw => ?_) (InvImage.wf (fun u => (u.length, u)) h)
  rcases huw with h' | h'
  · exact Prod.Lex.left _ _ h'
  · exact Prod.lex_def.2 (Or.inr ⟨h'.1, h'⟩)

end DegLex

/-! ## Path words -/

variable {E : ℕ → Type v} {L : Type*} (ltr : ∀ k, E k → ℕ → L)

/-- **The word along a position**: the letter `ltr k e i` for each vertex `e` of arity `k` on the
path, `i` the input taken. -/
def pathWord : STree E → List ℕ → List L
  | leaf _, _ => []
  | _, [] => []
  | @node _ k e c, i :: q => if h : i < k then ltr k e i :: pathWord (c ⟨i, h⟩) q else []

/-- **The word of a leaf**: the word along its position. -/
noncomputable def word (t : STree E) (b : ℕ) : List L := pathWord ltr t (t.pos b)

@[simp] lemma pathWord_nil (t : STree E) : pathWord ltr t [] = [] := by cases t <;> rfl

lemma pathWord_node_cons {k : ℕ} (e : E k) (c : Fin k → STree E) (i : ℕ) (q : List ℕ) :
    pathWord ltr (node e c) (i :: q) =
      if h : i < k then ltr k e i :: pathWord ltr (c ⟨i, h⟩) q else [] := rfl

/-- **The word along a concatenated position.** -/
theorem pathWord_append : ∀ {t u : STree E} {p : List ℕ}, t.get? p = some u → ∀ q : List ℕ,
    pathWord ltr t (p ++ q) = pathWord ltr t p ++ pathWord ltr u q
  | t, u, [], h, q => by
    rw [get?_nil, Option.some_inj] at h
    subst h
    simp
  | leaf _, _, _ :: _, h, _ => by simp at h
  | @node _ k e c, u, i :: p, h, q => by
    obtain ⟨hi, h⟩ := get?_node_cons_eq_some.1 h
    rw [List.cons_append, pathWord_node_cons, pathWord_node_cons, dif_pos hi, dif_pos hi,
      pathWord_append h q, List.cons_append]

/-- **The word along a replaced position** does not change. -/
theorem pathWord_replace : ∀ {t : STree E} {p : List ℕ}, (t.get? p).isSome → ∀ u : STree E,
    pathWord ltr (t.replace p u) p = pathWord ltr t p
  | t, [], _, u => by simp
  | leaf _, _ :: _, h, _ => by simp at h
  | @node _ k e c, i :: p, h, u => by
    obtain ⟨hi, h⟩ := get?_node_cons_isSome.1 h
    rw [replace_node_cons, pathWord_node_cons, pathWord_node_cons, dif_pos hi, dif_pos hi]
    simp only [if_true]
    rw [pathWord_replace h u]

/-- **The word along a position incomparable with the replaced one** does not change. -/
theorem pathWord_replace_of_incomp : ∀ (r : List ℕ) {i j : ℕ}, i ≠ j → ∀ (t : STree E)
    (p' q' : List ℕ) (u : STree E),
    pathWord ltr (t.replace (r ++ i :: p') u) (r ++ j :: q') = pathWord ltr t (r ++ j :: q')
  | [], i, j, hij, leaf _, _, _, _ => rfl
  | [], i, j, hij, @node _ k e c, p', q', u => by
    rw [List.nil_append, List.nil_append, replace_node_cons, pathWord_node_cons,
      pathWord_node_cons]
    split_ifs with hj h <;> first | rfl | exact absurd h (Ne.symm hij)
  | _ :: _, _, _, _, leaf _, _, _, _ => rfl
  | a :: r, i, j, hij, @node _ k e c, p', q', u => by
    rw [List.cons_append, List.cons_append, replace_node_cons, pathWord_node_cons,
      pathWord_node_cons]
    split_ifs <;> first | rfl | rw [pathWord_replace_of_incomp r hij _ p' q' u]

lemma pathWord_replace_incomp {p r : List ℕ} (h : Incomp p r) (t u : STree E) :
    pathWord ltr (t.replace p u) r = pathWord ltr t r := by
  obtain ⟨r₀, i, j, p', q', hij, rfl, rfl⟩ := h
  exact pathWord_replace_of_incomp ltr r₀ hij t p' q' u

/-- **The word along a position of a substituted tree** is that of the tree. -/
theorem pathWord_subst : ∀ {t : STree E} {q : List ℕ}, (t.get? q).isSome →
    ∀ xs : ℕ → STree E, pathWord ltr (t.subst xs) q = pathWord ltr t q
  | t, [], _, xs => by simp
  | leaf _, _ :: _, h, _ => by simp at h
  | @node _ k e c, i :: q, h, xs => by
    obtain ⟨hi, h⟩ := get?_node_cons_isSome.1 h
    rw [subst_node, pathWord_node_cons, pathWord_node_cons, dif_pos hi, dif_pos hi,
      pathWord_subst h xs]

/-- **The proper prefixes of a position are vertices.** -/
lemma get?_node_of_prefix {t : STree E} {p r : List ℕ} (hp : (t.get? p).isSome) (h : r <+: p)
    (hne : r ≠ p) : ∃ k, ∃ (e : E k) (c : Fin k → STree E), t.get? r = some (node e c) := by
  obtain ⟨s, rfl⟩ := h
  cases s with
  | nil => exact absurd (List.append_nil r).symm hne
  | cons i s =>
    rw [get?_append] at hp
    cases hw : t.get? r with
    | none => rw [hw] at hp; simp at hp
    | some w =>
      rw [hw, Option.bind_some] at hp
      cases w with
      | leaf a => simp at hp
      | node e c => exact ⟨_, e, c, rfl⟩

/-! ## Words in a context -/

/-- **The word of a leaf of an input** inside a context: the word of the path to the hole, then
the word of the input's leaf in the inserted monomial, then the word in the input. -/
theorem word_ctx_in {T t g : STree E} {p : List ℕ} {xs : ℕ → STree E} (hp : (T.get? p).isSome)
    (ht : t = T.replace p (g.subst xs)) (hn : t.labels.Nodup) {a b : ℕ} (ha : a ∈ g.labels)
    (hb : b ∈ (xs a).labels) :
    word ltr t b = pathWord ltr T p ++ (word ltr g a ++ word ltr (xs a) b) := by
  subst ht
  have hga := get?_pos ha
  have h1 : (T.replace p (g.subst xs)).get? (p ++ (g.pos a ++ (xs a).pos b)) =
      some (leaf b) := by
    rw [get?_replace_append hp, get?_append_of (get?_subst hga xs)]
    exact get?_pos hb
  rw [word, pos_eq hn h1, pathWord_append ltr (get?_replace hp _), pathWord_replace ltr hp,
    pathWord_append ltr (get?_subst hga xs), pathWord_subst ltr (by rw [hga]; rfl)]
  rfl

/-- **The word of a leaf outside the inputs** does not depend on the inserted monomial. -/
theorem word_ctx_out {T U₁ U₂ : STree E} {p : List ℕ} (hp : (T.get? p).isSome)
    (hn₂ : (T.replace p U₂).labels.Nodup) {b : ℕ} (hb₁ : b ∈ (T.replace p U₁).labels)
    (hU₁ : b ∉ U₁.labels) : word ltr (T.replace p U₁) b = word ltr (T.replace p U₂) b := by
  have hr := get?_pos hb₁
  rw [word, word]
  generalize (T.replace p U₁).pos b = r at hr ⊢
  have hinc : Incomp p r := by
    rcases prefix_or_incomp p r with ⟨r', rfl⟩ | hpr | hinc
    · rw [get?_replace_append hp] at hr
      exact absurd (mem_labels_of_get? hr) hU₁
    · by_cases he : r = p
      · subst he
        rw [get?_replace hp, Option.some_inj] at hr
        subst hr
        exact absurd (Multiset.mem_singleton_self b) hU₁
      · obtain ⟨k, e, c, hc⟩ := get?_node_of_prefix (by rw [get?_replace hp U₁]; rfl) hpr he
        rw [hc] at hr
        simp at hr
    · exact hinc
  have hr₂ : (T.replace p U₂).get? r = some (leaf b) := by
    rw [get?_replace_of_incomp' hinc, ← get?_replace_of_incomp' hinc T U₁]
    exact hr
  rw [pos_eq hn₂ hr₂, pathWord_replace_incomp ltr hinc, pathWord_replace_incomp ltr hinc]

/-! ## Path orders -/

/-- **The path order of a word order** `W` on the monomials on `A`: the words of the leaves
compared lexicographically in the order of the leaves, each by `W`. -/
def pathLexBy (W : List L → List L → Prop) {A : Finset ℕ} (x y : SMono E A) : Prop :=
  Pi.Lex (· < ·) (fun {_} u w => W u w) (fun a : A => word ltr x.1 a)
    (fun a : A => word ltr y.1 a)

theorem pathLexBy_trans {W : List L → List L → Prop} (hW : ∀ {u v w}, W u v → W v w → W u w)
    {A : Finset ℕ} {x y z : SMono E A} (h₁ : pathLexBy ltr W x y) (h₂ : pathLexBy ltr W y z) :
    pathLexBy ltr W x z := by
  obtain ⟨i, hi, hxy⟩ := h₁
  obtain ⟨j, hj, hyz⟩ := h₂
  rcases lt_trichotomy i j with hij | rfl | hij
  · refine ⟨i, fun k hk => (hi k hk).trans (hj k (hk.trans hij)), ?_⟩
    have := hj i hij
    simp only at this hxy ⊢
    rw [← this]
    exact hxy
  · exact ⟨i, fun k hk => (hi k hk).trans (hj k hk), hW hxy hyz⟩
  · refine ⟨j, fun k hk => (hi k (hk.trans hij)).trans (hj k hk), ?_⟩
    have := hi j hij
    simp only at this hyz ⊢
    rw [this]
    exact hyz

/-- **Contexts preserve the path order of a word order preserved by concatenation.** -/
theorem pathLexBy_ctx {W : List L → List L → Prop}
    (hW : ∀ {u w}, W u w → ∀ P Q, W (P ++ (u ++ Q)) (P ++ (w ++ Q))) {A B : Finset ℕ}
    {f : SMono E A → SMono E B} (hf : IsSCtx f) {x y : SMono E A} (h : pathLexBy ltr W x y) :
    pathLexBy ltr W (f x) (f y) := by
  obtain ⟨T, p, xs, hp, hin, hfe⟩ := hf
  obtain ⟨a₀, ha₀, hlt⟩ := h
  have hs₀ := hin.shuffle a₀ a₀.2
  have hb₀ : (xs a₀).first ∈ B := hin.labels a₀ a₀.2 _ (first_mem hs₀)
  have hfx : ∀ g : SMono E A, ∀ a ∈ A, ∀ b ∈ (xs a).labels,
      word ltr (f g).1 b = pathWord ltr T p ++ (word ltr g.1 a ++ word ltr (xs a) b) :=
    fun g a ha b hb => word_ctx_in ltr hp (hfe g) (f g).nodup (g.mem_labels.2 ha) hb
  refine ⟨⟨(xs a₀).first, hb₀⟩, fun b hb => ?_, ?_⟩
  · have hb' : b.1 < (xs a₀).first := hb
    show word ltr (f x).1 b.1 = word ltr (f y).1 b.1
    by_cases hex : ∃ a ∈ A, b.1 ∈ (xs a).labels
    · obtain ⟨a, ha, hba⟩ := hex
      have hfa := first_le (hin.shuffle a ha) _ hba
      have haa : a < a₀.1 := by
        by_contra hge
        rcases (not_lt.1 hge).lt_or_eq with hlt' | heq
        · have := hin.mono a₀.2 ha hlt'
          simp only at this
          omega
        · rw [← heq] at hfa
          omega
      rw [hfx x a ha b hba, hfx y a ha b hba]
      have := ha₀ ⟨a, ha⟩ haa
      simp only at this
      rw [this]
    · simp only [not_exists, not_and] at hex
      have hbx : b.1 ∈ (f x).1.labels := (f x).mem_labels.2 b.2
      have hny := (f y).nodup
      rw [hfe x] at hbx ⊢
      rw [hfe y] at hny ⊢
      refine word_ctx_out ltr hp hny hbx ?_
      rw [labels_subst, Multiset.mem_bind]
      rintro ⟨a, ha, hba⟩
      exact hex a (x.mem_labels.1 ha) hba
  · show W (word ltr (f x).1 (xs a₀).first) (word ltr (f y).1 (xs a₀).first)
    rw [hfx x a₀ a₀.2 _ (first_mem hs₀), hfx y a₀ a₀.2 _ (first_mem hs₀)]
    exact hW hlt _ _

/-! ## The path-lexicographic order -/

variable [LinearOrder L]

/-- **The path-lexicographic order** on the monomials on `A`: the words of the leaves compared
lexicographically in the order of the leaves, each degree-lexicographically. -/
def pathLex {A : Finset ℕ} (x y : SMono E A) : Prop := pathLexBy ltr DegLex x y

theorem pathLex_trans {A : Finset ℕ} {x y z : SMono E A} (h₁ : pathLex ltr x y)
    (h₂ : pathLex ltr y z) : pathLex ltr x z :=
  pathLexBy_trans ltr (W := DegLex) (fun h h' => DegLex.trans h h') h₁ h₂

theorem pathLex_wf [WellFoundedLT L] (A : Finset ℕ) :
    WellFounded (pathLex ltr (A := A)) :=
  InvImage.wf (fun x : SMono E A => fun a : A => word ltr x.1 a)
    (Pi.Lex.wellFounded (· < ·) fun _ => degLex_wf)

/-- **Contexts preserve the path-lexicographic order.** -/
theorem pathLex_ctx {A B : Finset ℕ} {f : SMono E A → SMono E B} (hf : IsSCtx f)
    {x y : SMono E A} (h : pathLex ltr x y) : pathLex ltr (f x) (f y) :=
  pathLexBy_ctx ltr (fun h P Q => DegLex.append h P Q) hf h

/-- **The path-lexicographic order is an admissible order.** -/
def pathLexOrder [WellFoundedLT L] : AdmOrder E where
  lt := pathLex ltr
  wf := pathLex_wf ltr
  trans := pathLex_trans ltr
  lt_ctx hf _ _ h := pathLex_ctx ltr hf h

end STree

end Operad
