/-
# Shuffles of words on positions, and cutting them
-/
import Operad.CInfinity
import Operad.UnshuffleSign
import Operad.LInfTransfer
import Mathlib.Order.Interval.Finset.Fin

universe u v

namespace Operad

namespace ShSplit

open GerBV KS

variable {α : Type*} [LinearOrder α]

/-! ## Ranks -/

/-- **The rank of `t` in `T`**: the number of elements of `T` below `t`. -/
def rank (T : Finset α) (t : α) : ℕ := (T.filter (· < t)).card

lemma rank_orderEmbOfFin (T : Finset α) {k : ℕ} (h : T.card = k) (i : Fin k) :
    rank T (T.orderEmbOfFin h i) = i := by
  unfold rank
  have e : T.filter (· < T.orderEmbOfFin h i)
      = (Finset.univ.filter (· < i)).map (T.orderEmbOfFin h).toEmbedding := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨ht, hlt⟩
      have : t ∈ Set.range (T.orderEmbOfFin h) := by
        rw [Finset.range_orderEmbOfFin]
        exact ht
      obtain ⟨j, rfl⟩ := this
      exact ⟨j, (T.orderEmbOfFin h).lt_iff_lt.1 hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem _ _ _, (T.orderEmbOfFin h).lt_iff_lt.2 hj⟩
  rw [e, Finset.card_map, ← Fin.card_Iio]
  congr 1
  ext j
  simp

lemma orderIsoOfFin_symm_val (T : Finset α) {k : ℕ} (h : T.card = k) {t : α} (ht : t ∈ T) :
    (((T.orderIsoOfFin h).symm ⟨t, ht⟩ : Fin k) : ℕ) = rank T t := by
  set i := (T.orderIsoOfFin h).symm ⟨t, ht⟩
  have hi : T.orderEmbOfFin h i = t := by
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  rw [← hi, rank_orderEmbOfFin]

/-! ## Merging two words on a set of positions -/

/-- **The merge of two words on the positions `M`**: the letters of `x` at the positions of `T`,
those of `y` at the others, both in order. Words are sequences indexed by `ℕ`. -/
noncomputable def mergeA {X : Type*} (T M : Finset α) (x y : ℕ → X) : α → X := by
  classical
  exact fun t => if t ∈ T then x (rank T t) else y (rank (M \ T) t)

/-- A finite word as a sequence, with a default value beyond its length. -/
def ext {X : Type*} {k : ℕ} (x : Fin k → X) (d : X) : ℕ → X :=
  fun n => if h : n < k then x ⟨n, h⟩ else d

lemma ext_apply {X : Type*} {k : ℕ} (x : Fin k → X) (d : X) (i : Fin k) : ext x d i = x i := by
  unfold ext
  rw [dif_pos i.isLt]

/-- **The merge of `CInfinity` is the merge on all positions.** -/
lemma merge_eq_mergeA {a c : ℕ} (S : Finset (Fin (a + c))) (hS : S.card = a) {X : Type*}
    (x : Fin a → X) (y : Fin c → X) (d : X) :
    CInf.merge S hS x y = mergeA S Finset.univ (ext x d) (ext y d) := by
  classical
  funext t
  unfold CInf.merge mergeA
  by_cases ht : t ∈ S
  · rw [dif_pos ht, if_pos ht]
    have h1 := orderIsoOfFin_symm_val S hS ht
    rw [← h1, ext_apply]
  · rw [dif_neg ht, if_neg ht]
    have hSc : Sᶜ.card = c := by rw [Finset.card_compl, Fintype.card_fin, hS]; omega
    have h1 := orderIsoOfFin_symm_val Sᶜ hSc (Finset.mem_compl.2 ht)
    rw [← Finset.compl_eq_univ_sdiff, ← h1, ext_apply]

/-! ## Cutting a merged word -/

/-- `P` is an initial segment of `M`. -/
def IsDown (P M : Finset α) : Prop := P ⊆ M ∧ ∀ t ∈ P, ∀ s ∈ M, s < t → s ∈ P

/-- A word shifted by `i` letters. -/
def shift {X : Type*} (x : ℕ → X) (i : ℕ) : ℕ → X := fun n => x (i + n)

lemma IsDown.lt {P M : Finset α} (hP : IsDown P M) {s t : α} (hs : s ∈ P) (ht : t ∈ M)
    (htP : t ∉ P) : s < t := by
  by_contra h
  rcases (not_lt.1 h).lt_or_eq with h' | h'
  · exact htP (hP.2 s hs t ht h')
  · exact htP (h' ▸ hs)

lemma rank_inter_down {P M T : Finset α} (hP : IsDown P M) (hT : T ⊆ M) {t : α} (ht : t ∈ P) :
    rank T t = rank (T ∩ P) t := by
  unfold rank
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨hs, hst⟩
    exact ⟨⟨hs, hP.2 t ht s (hT hs) hst⟩, hst⟩
  · rintro ⟨⟨hs, -⟩, hst⟩
    exact ⟨hs, hst⟩

lemma rank_sdiff_down {P M T : Finset α} (hP : IsDown P M) {t : α} (htP : t ∉ P)
    (ht : t ∈ M) : rank T t = (T ∩ P).card + rank (T \ P) t := by
  classical
  unfold rank
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨hs, hst⟩
      by_cases hsP : s ∈ P
      · exact Or.inl ⟨hs, hsP⟩
      · exact Or.inr ⟨⟨hs, hsP⟩, hst⟩
    · rintro (⟨hs, hsP⟩ | ⟨⟨hs, -⟩, hst⟩)
      · exact ⟨hs, hP.lt hsP ht htP⟩
      · exact ⟨hs, hst⟩
  · refine Finset.disjoint_left.2 fun s hs hs' => ?_
    exact (Finset.mem_sdiff.1 (Finset.mem_filter.1 hs').1).2 (Finset.mem_inter.1 hs).2

/-- **The prefix of a merged word** is the merge of the prefixes. -/
lemma mergeA_down {X : Type*} {P M T : Finset α} (hP : IsDown P M) (hT : T ⊆ M) (x y : ℕ → X)
    {t : α} (ht : t ∈ P) : mergeA T M x y t = mergeA (T ∩ P) P x y t := by
  classical
  unfold mergeA
  by_cases htT : t ∈ T
  · rw [if_pos htT, if_pos (Finset.mem_inter.2 ⟨htT, ht⟩), rank_inter_down hP hT ht]
  · rw [if_neg htT, if_neg fun h => htT (Finset.mem_inter.1 h).1]
    have hd : IsDown P M := hP
    rw [rank_inter_down hd Finset.sdiff_subset ht]
    congr 2
    ext s
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hs, hsT⟩, hsP⟩
      exact ⟨hsP, fun h => hsT h.1⟩
    · rintro ⟨hsP, hsT⟩
      exact ⟨⟨hP.1 hsP, fun h => hsT ⟨h, hsP⟩⟩, hsP⟩

/-- **The suffix of a merged word** is the merge of the suffixes. -/
lemma mergeA_up {X : Type*} {P M T : Finset α} (hP : IsDown P M) (x y : ℕ → X)
    {t : α} (ht : t ∈ M) (htP : t ∉ P) :
    mergeA T M x y t = mergeA (T \ P) (M \ P) (shift x (T ∩ P).card)
      (shift y (P.card - (T ∩ P).card)) t := by
  classical
  unfold mergeA shift
  by_cases htT : t ∈ T
  · rw [if_pos htT, if_pos (Finset.mem_sdiff.2 ⟨htT, htP⟩), rank_sdiff_down hP htP ht]
  · rw [if_neg htT, if_neg fun h => htT (Finset.mem_sdiff.1 h).1,
      rank_sdiff_down hP htP ht]
    congr 1
    have h1 : (M \ T) ∩ P = P \ (T ∩ P) := by
      ext s
      simp only [Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨-, hsT⟩, hsP⟩
        exact ⟨hsP, fun h => hsT h.1⟩
      · rintro ⟨hsP, hsT⟩
        exact ⟨⟨hP.1 hsP, fun h => hsT ⟨h, hsP⟩⟩, hsP⟩
    have h2 : (M \ T) \ P = (M \ P) \ (T \ P) := by
      ext s
      simp only [Finset.mem_sdiff]
      tauto
    rw [h1, h2, Finset.card_sdiff_of_subset Finset.inter_subset_right]

/-! ## Parities of merged words -/

lemma rank_lt_of_lt {T : Finset α} {s t : α} (hs : s ∈ T) (hst : s < t) : rank T s < rank T t := by
  unfold rank
  refine Finset.card_lt_card ⟨fun u hu => ?_, fun h => ?_⟩
  · rw [Finset.mem_filter] at hu ⊢
    exact ⟨hu.1, hu.2.trans hst⟩
  · have := h (Finset.mem_filter.2 ⟨hs, hst⟩)
    exact lt_irrefl _ (Finset.mem_filter.1 this).2

lemma rank_lt_card {T : Finset α} {t : α} (ht : t ∈ T) : rank T t < T.card := by
  unfold rank
  refine Finset.card_lt_card ⟨Finset.filter_subset _ _, fun h => ?_⟩
  exact lt_irrefl _ (Finset.mem_filter.1 (h ht)).2

/-- **The parity of a word on a set of positions** is that of its letters. -/
lemma par_rank (T : Finset α) (q : ℕ → Bool) :
    par (fun t => q (rank T t)) T = par q (Finset.range T.card) := by
  classical
  unfold par
  congr 1
  refine Finset.card_bij (fun t _ => rank T t) ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_filter] at ht ⊢
    exact ⟨Finset.mem_range.2 (rank_lt_card ht.1), ht.2⟩
  · intro t ht t' ht' h
    rw [Finset.mem_filter] at ht ht'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (rank_lt_of_lt ht.1 hlt).ne h
    · exact (rank_lt_of_lt ht'.1 hlt).ne h.symm
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    refine ⟨T.orderEmbOfFin rfl ⟨n, hn.1⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      dsimp only
      rw [rank_orderEmbOfFin]
      exact ⟨Finset.orderEmbOfFin_mem _ _ _, hn.2⟩
    · show rank T _ = n
      rw [rank_orderEmbOfFin]

omit [LinearOrder α] in
lemma par_congr {p p' : α → Bool} {A : Finset α} (h : ∀ a ∈ A, p a = p' a) :
    par p A = par p' A := by
  unfold par
  rw [Finset.filter_congr (p := fun i => p i = true) (q := fun i => p' i = true)
    fun a ha => by simp only [h a ha]]

lemma par_mergeA_left {T M : Finset α} (px py : ℕ → Bool) :
    par (mergeA T M px py) T = par px (Finset.range T.card) := by
  classical
  rw [← par_rank T px]
  exact par_congr fun t ht => by unfold mergeA; rw [if_pos ht]

lemma par_mergeA_right {T M : Finset α} (px py : ℕ → Bool) :
    par (mergeA T M px py) (M \ T) = par py (Finset.range (M \ T).card) := by
  classical
  rw [← par_rank (M \ T) py]
  exact par_congr fun t ht => by unfold mergeA; rw [if_neg (Finset.mem_sdiff.1 ht).2]

/-! ## The shuffle sum -/

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V] {W : Type*}
  [AddCommGroup W] [Module R W]

variable (R) in
/-- **The signed shuffle sum** of an evaluation `Φ` over the merges of `A` letters of `x` with
the rest of `y` on the positions `M`. -/
noncomputable def shf (Φ : (α → V) → Finset α → W) (M : Finset α) (A : ℕ) (x y : ℕ → V)
    (px py : ℕ → Bool) : W :=
  ∑ T ∈ M.powersetCard A, ks R (mergeA T M px py) T (M \ T) • Φ (mergeA T M x y) M

/-! ## The shuffle sum at a cut -/

omit [AddCommGroup V] [Module R V] in
lemma ks_congr {p p' : α → Bool} {A B : Finset α} (h : ∀ a ∈ A ∪ B, p a = p' a) :
    ks R p A B = ks R p' A B := by
  unfold ks
  refine Finset.prod_congr rfl fun i hi => Finset.prod_congr rfl fun j hj => ?_
  rw [h i (Finset.mem_union_left _ hi),
    h j (Finset.mem_union_right _ (Finset.mem_filter.1 hj).1)]

omit [AddCommGroup V] [Module R V] in
/-- Subsets of `M` of size `A`, by their parts in an initial segment and in the rest. -/
lemma sum_powersetCard_split {Z : Type*} [AddCommMonoid Z] {P M : Finset α} (hP : P ⊆ M)
    (A : ℕ) (G : Finset α → Z) :
    ∑ T ∈ M.powersetCard A, G T = ∑ i ∈ Finset.range (A + 1), ∑ T1 ∈ P.powersetCard i,
      ∑ T2 ∈ (M \ P).powersetCard (A - i), G (T1 ∪ T2) := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun T _ => ⟨⟨(T ∩ P).card, T ∩ P⟩, T \ P⟩) (fun x _ => x.1.2 ∪ x.2)
    ?_ ?_ ?_ ?_ ?_
  · intro T hT
    rw [Finset.mem_powersetCard] at hT
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_powersetCard]
    have h1 := Finset.card_inter_add_card_sdiff T P
    refine ⟨⟨by omega, Finset.inter_subset_right, by trivial⟩,
      Finset.sdiff_subset_sdiff hT.1 subset_rfl, by omega⟩
  · rintro ⟨⟨i, T1⟩, T2⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_powersetCard] at hx
    obtain ⟨⟨hi, h1, h2⟩, h3, h4⟩ := hx
    rw [Finset.mem_powersetCard]
    have hd : Disjoint T1 T2 := Finset.disjoint_of_subset_left h1
      (Finset.disjoint_of_subset_right h3 Finset.disjoint_sdiff)
    refine ⟨Finset.union_subset (h1.trans hP) (h3.trans Finset.sdiff_subset), ?_⟩
    rw [Finset.card_union_of_disjoint hd]
    omega
  · intro T _
    show T ∩ P ∪ T \ P = T
    rw [Finset.union_comm]
    exact Finset.sdiff_union_inter T P
  · rintro ⟨⟨i, T1⟩, T2⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_powersetCard] at hx
    obtain ⟨⟨hi, h1, h2⟩, h3, h4⟩ := hx
    have e1 : (T1 ∪ T2) ∩ P = T1 := by
      ext a
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hp⟩
        · exact h
        · exact absurd hp (Finset.mem_sdiff.1 (h3 h)).2
      · intro h
        exact ⟨Or.inl h, h1 h⟩
    have e2 : (T1 ∪ T2) \ P = T2 := by
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hp⟩
        · exact absurd (h1 h) hp
        · exact h
      · intro h
        exact ⟨Or.inr h, (Finset.mem_sdiff.1 (h3 h)).2⟩
    simp only [e1, e2, h2]
  · intro T _
    rw [Finset.union_comm, Finset.sdiff_union_inter]

/-- **The shuffle sum of a product cut at an initial segment** `P`: by the number `i` of letters
of `x` before the cut, the product of the shuffle sums of the two sides, with the sign of the
letters of `x` after the cut moving past those of `y` before it. -/
theorem shf_cut (μ : End R V 2) (EX EY : (α → V) → Finset α → V)
    (hX : ∀ w w' S, (∀ a ∈ S, w a = w' a) → EX w S = EX w' S)
    (hY : ∀ w w' S, (∀ a ∈ S, w a = w' a) → EY w S = EY w' S)
    {P M : Finset α} (hP : IsDown P M) (A : ℕ) (x y : ℕ → V) (px py : ℕ → Bool) :
    shf R (fun w _ => μ ![EX w P, EY w (M \ P)]) M A x y px py
      = ∑ i ∈ Finset.range (A + 1),
        σ R (par (shift px i) (Finset.range (A - i)) && par py (Finset.range (P.card - i))) •
          μ ![shf R EX P i x y px py,
            shf R EY (M \ P) (A - i) (shift x i) (shift y (P.card - i)) (shift px i)
              (shift py (P.card - i))] := by
  classical
  unfold shf
  rw [sum_powersetCard_split hP.1 A]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LInfT.b_sum_left, Finset.smul_sum]
  refine Finset.sum_congr rfl fun T1 hT1 => ?_
  rw [Finset.mem_powersetCard] at hT1
  rw [HTT.mu_smul_left, LInfT.b_sum_right, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun T2 hT2 => ?_
  rw [Finset.mem_powersetCard] at hT2
  set T := T1 ∪ T2
  have hT1Q : Disjoint T1 (M \ P) := Finset.disjoint_of_subset_left hT1.1 Finset.disjoint_sdiff
  have hTsub : T ⊆ M := Finset.union_subset (hT1.1.trans hP.1) (hT2.1.trans Finset.sdiff_subset)
  have e1 : T ∩ P = T1 := by
    ext a
    simp only [T, Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨h | h, hp⟩
      · exact h
      · exact absurd hp (Finset.mem_sdiff.1 (hT2.1 h)).2
    · intro h
      exact ⟨Or.inl h, hT1.1 h⟩
  have e2 : T \ P = T2 := by
    ext a
    simp only [T, Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨h | h, hp⟩
      · exact absurd (hT1.1 h) hp
      · exact h
    · intro h
      exact ⟨Or.inr h, (Finset.mem_sdiff.1 (hT2.1 h)).2⟩
  have hi : (T ∩ P).card = i := by rw [e1, hT1.2]
  -- the letters and parities on each side
  have hdl : ∀ a ∈ P, mergeA T M x y a = mergeA T1 P x y a :=
    fun a ha => by rw [mergeA_down hP hTsub x y ha, e1]
  have hdlp : ∀ a ∈ P, mergeA T M px py a = mergeA T1 P px py a :=
    fun a ha => by rw [mergeA_down hP hTsub px py ha, e1]
  have hdr : ∀ a ∈ M \ P,
      mergeA T M x y a = mergeA T2 (M \ P) (shift x i) (shift y (P.card - i)) a :=
    fun a ha => by
      rw [mergeA_up hP x y (Finset.mem_sdiff.1 ha).1 (Finset.mem_sdiff.1 ha).2, e2, hi]
  have hdrp : ∀ a ∈ M \ P,
      mergeA T M px py a = mergeA T2 (M \ P) (shift px i) (shift py (P.card - i)) a :=
    fun a ha => by
      rw [mergeA_up hP px py (Finset.mem_sdiff.1 ha).1 (Finset.mem_sdiff.1 ha).2, e2, hi]
  dsimp only
  rw [hX _ _ P hdl, hY _ _ (M \ P) hdr,
    HTT.mu_smul_right, smul_smul, smul_smul]
  congr 1
  -- the signs
  set p := mergeA T M px py
  have hMT : M \ T = (P \ T1) ∪ ((M \ P) \ T2) := by
    ext a
    simp only [T, Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨haM, ha⟩
      by_cases haP : a ∈ P
      · exact Or.inl ⟨haP, fun h => ha (Or.inl h)⟩
      · exact Or.inr ⟨⟨haM, haP⟩, fun h => ha (Or.inr h)⟩
    · rintro (⟨haP, ha⟩ | ⟨⟨haM, haP⟩, ha⟩)
      · exact ⟨hP.1 haP, fun h => h.elim ha fun h' => (Finset.mem_sdiff.1 (hT2.1 h')).2 haP⟩
      · exact ⟨haM, fun h => h.elim (fun h' => haP (hT1.1 h')) ha⟩
  have hd1 : Disjoint (P \ T1) ((M \ P) \ T2) :=
    Finset.disjoint_of_subset_left Finset.sdiff_subset
      (Finset.disjoint_of_subset_right Finset.sdiff_subset Finset.disjoint_sdiff)
  have hd2 : Disjoint T1 T2 := Finset.disjoint_of_subset_right hT2.1 hT1Q
  rw [hMT, ks_union_right p T hd1, ks_union_left p (P \ T1) hd2,
    ks_union_left p ((M \ P) \ T2) hd2]
  have k1 : ks R p T1 (P \ T1) = ks R (mergeA T1 P px py) T1 (P \ T1) :=
    ks_congr fun a ha => hdlp a (Finset.mem_union.1 ha |>.elim (fun h => hT1.1 h)
      fun h => (Finset.mem_sdiff.1 h).1)
  have k2 : ks R p T2 ((M \ P) \ T2)
      = ks R (mergeA T2 (M \ P) (shift px i) (shift py (P.card - i))) T2 ((M \ P) \ T2) :=
    ks_congr fun a ha => hdrp a (Finset.mem_union.1 ha |>.elim (fun h => hT2.1 h)
      fun h => (Finset.mem_sdiff.1 h).1)
  have k3 : ks R p T1 ((M \ P) \ T2) = 1 := by
    unfold ks
    refine Finset.prod_eq_one fun s hs => Finset.prod_eq_one fun t ht => ?_
    rw [Finset.mem_filter] at ht
    exact absurd ht.2 (not_lt.2 (hP.lt (hT1.1 hs) (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 ht.1).1).1
      (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 ht.1).1).2).le)
  have k4 : ks R p T2 (P \ T1)
      = σ R (par (shift px i) (Finset.range (A - i)) && par py (Finset.range (P.card - i))) := by
    have hall : ∀ s ∈ T2, ∀ t ∈ P \ T1, t < s := fun s hs t ht =>
      hP.lt (Finset.mem_sdiff.1 ht).1 (Finset.mem_sdiff.1 (hT2.1 hs)).1
        (Finset.mem_sdiff.1 (hT2.1 hs)).2
    have h1 : ks R p T2 (P \ T1) = ∏ s ∈ T2, ∏ t ∈ P \ T1, σ R (p s && p t) := by
      unfold ks
      refine Finset.prod_congr rfl fun s hs => ?_
      rw [Finset.filter_true_of_mem fun t ht => hall s hs t ht]
    rw [h1, ← σ_par_and_par]
    have h2 : par p T2 = par (shift px i) (Finset.range (A - i)) := by
      rw [par_congr fun a ha => hdrp a (hT2.1 ha), par_mergeA_left, hT2.2]
    have h3 : par p (P \ T1) = par py (Finset.range (P.card - i)) := by
      rw [par_congr fun a ha => hdlp a (Finset.mem_sdiff.1 ha).1, par_mergeA_right,
        Finset.card_sdiff_of_subset hT1.1, hT1.2]
    rw [h2, h3]
  rw [k1, k2, k3, k4]
  ring

end ShSplit

end Operad
