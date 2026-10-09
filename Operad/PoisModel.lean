/-
# The Poisson operad has at least `n!` operations of arity `n`

The Poisson algebra of polynomials in words (`KK.wordPoisAlg`) is an algebra over the Poisson
operad, so the operations of `Pois` evaluate on the variables `X [a]` of the one-letter words.

* **The values of the trees on a finite set `s` of letters** (`PoisDim.Tsp`) contain the variables
  `X [a]` (`PoisDim.X_mem_Tsp`) and, for disjoint sets, **their products and brackets**
  (`PoisDim.binop_mem_Tsp`): grafting two trees under a generator.
* So they contain **the products of left-normed brackets** `[[X [m], X [c₁]], …, X [c_k]]` of the
  blocks of a set partition (`PoisDim.comb_mem_Tsp`, `PoisDim.prodB_mem_Tsp`).
* **These are independent** (`PoisDim.linearIndependent_lead`): the algebra map killing the words
  whose first letter is not the least (`PoisDim.killBad`) sends the left-normed bracket of a word
  with least first letter to the word itself (`PoisDim.killBad_comb`), hence a product of such
  brackets to a monomial in distinct words. Cutting a permutation before its left-to-right minima
  (`PoisDim.cut`) gives blocks with least first letters and decreasing first letters, from which it
  is recovered: distinct permutations give distinct monomials.

Hence the values of the operations of arity `n` span a space of dimension at least `n!`
(`PoisDim.le_finrank_Tsp`).
-/
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.List.Permutation
import Mathlib.RingTheory.MvPolynomial.Basic
import Operad.KirillovKostant

universe u

namespace Operad

namespace PoisDim

open MvPolynomial KK Sym SetOperad FreeBin

variable (K : Type u) [Field K]

/-- The polynomials in words. -/
abbrev W := MvPolynomial (List ℕ) K

/-- The operations of the Poisson algebra of polynomials in words. -/
noncomputable def μ : PoisOp → EndOp K (W K) (Fin 2)
  | .mul => (wordPoisAlg K).mul
  | .bracket => (wordPoisAlg K).bracket

/-- The operations, as bilinear maps. -/
noncomputable def βL : PoisOp → W K →ₗ[K] W K →ₗ[K] W K
  | .mul => LinearMap.mul K (W K)
  | .bracket => bracketL (wordBracket K)

lemma μ_apply (g : PoisOp) (y z : W K) : μ K g ![y, z] = βL K g y z := by
  cases g <;> rfl

/-! ## Values of trees -/

variable {K}

/-- **The value of a tree** of the free operad on the Poisson generators. -/
noncomputable def sval {A : Type} [Fintype A] [DecidableEq A] (x : Syn (BinGen PoisOp) A)
    (w : A → W K) : W K :=
  EndOp.ap (Syn.eval (binVal (μ K)) x) w

lemma sval_one (w : Unit → W K) : sval Syn.one w = w () := rfl

lemma sval_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    (x : Syn (BinGen PoisOp) A) (w : B → W K) :
    sval (Syn.map e x) w = sval x fun a => w (e a) := rfl

lemma sval_bin {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (g : PoisOp) (x : Syn (BinGen PoisOp) A) (y : Syn (BinGen PoisOp) B) (w : A ⊕ B → W K) :
    sval (Syn.bin (Syn.gen (BinGen.op g)) x y) w
      = βL K g (sval x fun a => w (Sum.inl a)) (sval y fun b => w (Sum.inr b)) := by
  rw [sval, Syn.eval_bin, EndOp.ap_bin, ← μ_apply]
  rfl

variable (K) in
/-- **The values of the trees on the letters `s`**, at the variables of the one-letter words. -/
noncomputable def Tsp (s : Finset ℕ) : Submodule K (W K) :=
  Submodule.span K (Set.range fun x : Syn (BinGen PoisOp) s => sval x fun a => X [a.1])

lemma sval_mem_Tsp (s : Finset ℕ) (x : Syn (BinGen PoisOp) s) :
    (sval x fun a => X [a.1]) ∈ Tsp K s :=
  Submodule.subset_span ⟨x, rfl⟩

/-- **A variable is the value of the unit.** -/
lemma X_mem_Tsp (a : ℕ) : (X [a] : W K) ∈ Tsp K {a} := by
  let e : Unit ≃ ({a} : Finset ℕ) :=
    ⟨fun _ => ⟨a, Finset.mem_singleton_self a⟩, fun _ => (), fun _ => rfl,
      fun x => Subtype.ext (Finset.mem_singleton.1 x.2).symm⟩
  exact Submodule.subset_span ⟨Syn.map e Syn.one, rfl⟩

/-- **Products and brackets of values on disjoint letters are values.** -/
theorem binop_mem_Tsp (g : PoisOp) {s t : Finset ℕ} (h : Disjoint s t) {y z : W K}
    (hy : y ∈ Tsp K s) (hz : z ∈ Tsp K t) : βL K g y z ∈ Tsp K (s ∪ t) := by
  have hm := Submodule.apply_mem_map₂ (βL K g) hy hz
  rw [Tsp, Tsp, Submodule.map₂_span_span] at hm
  refine (Submodule.span_le.2 ?_) hm
  rintro _ ⟨_, ⟨x, rfl⟩, _, ⟨x', rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨Syn.map (Equiv.Finset.union s t h)
    (Syn.bin (Syn.gen (BinGen.op g)) x x'), ?_⟩
  show sval (Syn.map _ _) _ = _
  rw [sval_map, sval_bin]
  rfl

/-! ## Left-normed brackets and their products -/

variable (K) in
/-- **The left-normed bracket** `[[X [a], X [c₁]], …, X [c_k]]` of a word `a c₁ … c_k`. -/
noncomputable def comb : List ℕ → W K
  | [] => 0
  | a :: rest => rest.foldl (fun p c => bracket (wordBracket K) p (X [c])) (X [a])

lemma comb_single (a : ℕ) : comb K [a] = X [a] := rfl

lemma comb_append_single {w : List ℕ} (hw : w ≠ []) (c : ℕ) :
    comb K (w ++ [c]) = bracket (wordBracket K) (comb K w) (X [c]) := by
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hw
  simp only [List.cons_append, comb, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- **Left-normed brackets of words without repetition are values.** -/
theorem comb_mem_Tsp : ∀ (w : List ℕ), w.Nodup → w ≠ [] → comb K w ∈ Tsp K w.toFinset := by
  intro w
  induction w using List.reverseRecOn with
  | nil => intro _ h; exact absurd rfl h
  | append_singleton w c ih =>
    intro hnd _
    by_cases hw : w = []
    · subst hw
      simpa [comb_single] using X_mem_Tsp (K := K) c
    · have hc : c ∉ w := by
        have := (List.nodup_append.1 hnd).2.2
        exact fun h => this c h c (List.mem_singleton_self c) rfl
      rw [comb_append_single hw, List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
        insert_empty_eq]
      exact binop_mem_Tsp (K := K) .bracket
        (Finset.disjoint_singleton_right.2 (by simpa using hc))
        (ih (List.nodup_append.1 hnd).1 hw) (X_mem_Tsp c)

variable (K) in
/-- **The product of the left-normed brackets** of blocks. -/
noncomputable def prodB (bs : List (List ℕ)) : W K := (bs.map (comb K)).prod

/-- **Products of left-normed brackets of disjoint blocks are values.** -/
theorem prodB_mem_Tsp : ∀ (bs : List (List ℕ)), bs ≠ [] → bs.flatten.Nodup → (∀ B ∈ bs, B ≠ []) →
    prodB K bs ∈ Tsp K bs.flatten.toFinset
  | [], h, _, _ => absurd rfl h
  | [B], _, hnd, hne => by
    simpa [prodB] using comb_mem_Tsp B (by simpa using hnd) (hne B (List.mem_singleton_self B))
  | B :: B' :: bs, _, hnd, hne => by
    rw [prodB, List.map_cons, List.prod_cons, List.flatten_cons, List.toFinset_append]
    have h1 := List.nodup_append.1 (List.flatten_cons ▸ hnd)
    refine binop_mem_Tsp (K := K) .mul ?_ (comb_mem_Tsp B h1.1 (hne B (by simp)))
      (prodB_mem_Tsp (B' :: bs) (by simp) h1.2.1 fun C hC => hne C (by simp [hC]))
    rw [List.disjoint_toFinset_iff_disjoint]
    exact fun a ha hb => h1.2.2 a ha a hb rfl

/-! ## Killing the bad words -/

/-- **A bad word**: one of its letters is less than the first. -/
def Bad (w : List ℕ) : Prop := ∃ a ∈ w, a < w.headI

instance (w : List ℕ) : Decidable (Bad w) := by unfold Bad; infer_instance

variable (K) in
/-- **The algebra map killing the bad words.** -/
noncomputable def killBad : W K →ₐ[K] W K := aeval fun w => if Bad w then 0 else X w

variable (K) in
/-- The span of the bad rearrangements of a word. -/
noncomputable def badSpan (w : List ℕ) : Submodule K (W K) :=
  Submodule.span K {p | ∃ u, u.Perm w ∧ Bad u ∧ p = X u}

lemma killBad_badSpan {w : List ℕ} {p : W K} (hp : p ∈ badSpan K w) : killBad K p = 0 := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, _, hu, rfl⟩ := hx
    rw [killBad, aeval_X, if_pos hu]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_smul, hx, smul_zero]

lemma bracket_X_X_word (u v : List ℕ) :
    bracket (wordBracket K) (X u) (X v) = X (u ++ v) - X (v ++ u) := by
  rw [bracket_X_X, wordBracket]

/-- **A left-normed bracket is its word plus bad rearrangements**, for a word whose first letter
is its least. -/
theorem comb_sub_mem : ∀ (w : List ℕ), w.Nodup → w ≠ [] → (∀ a ∈ w, w.headI ≤ a) →
    comb K w - X w ∈ badSpan K w := by
  intro w
  induction w using List.reverseRecOn with
  | nil => intro _ h; exact absurd rfl h
  | append_singleton w c ih =>
    intro hnd _ hmin
    by_cases hw : w = []
    · subst hw
      rw [List.nil_append, comb_single, sub_self]
      exact zero_mem _
    · have hc : c ∉ w := by
        have := (List.nodup_append.1 hnd).2.2
        exact fun h => this c h c (List.mem_singleton_self c) rfl
      have hhead : (w ++ [c]).headI = w.headI := by
        obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hw
        rfl
      have hmin' : ∀ a ∈ w, w.headI ≤ a := fun a ha => hhead ▸ hmin a (by simp [ha])
      have hlt : w.headI < c := by
        have hle := hhead ▸ hmin c (by simp)
        refine lt_of_le_of_ne hle fun h => hc ?_
        rw [← h]
        obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hw
        simp
      have ih' := ih (List.nodup_append.1 hnd).1 hw hmin'
      have key : comb K (w ++ [c]) - X (w ++ [c]) =
          bracket (wordBracket K) (comb K w - X w) (X [c]) - X ([c] ++ w) := by
        rw [comb_append_single hw, show bracket (wordBracket K) (comb K w - X w) (X [c]) =
          bracket (wordBracket K) (comb K w) (X [c]) - bracket (wordBracket K) (X w) (X [c])
          from map_sub _ _ _,
          bracket_X_X_word]
        abel
      rw [key]
      refine sub_mem ?_ (Submodule.subset_span ⟨[c] ++ w, List.perm_append_comm,
        ⟨w.headI, ?_, hlt⟩, rfl⟩)
      · -- the bracket of the bad rearrangements with the new letter
        refine Submodule.span_induction (p := fun p _ =>
          bracket (wordBracket K) p (X [c]) ∈ badSpan K (w ++ [c])) ?_ ?_ ?_ ?_ ih'
        · rintro _ ⟨u, hu, ⟨a, ha, hau⟩, rfl⟩
          have hune : u ≠ [] := fun h => hw (List.perm_nil.1 (h ▸ hu).symm)
          rw [bracket_X_X_word]
          refine sub_mem (Submodule.subset_span ⟨u ++ [c], hu.append_right _, ⟨a, by simp [ha],
            ?_⟩, rfl⟩) (Submodule.subset_span ⟨[c] ++ u, ?_, ⟨w.headI, ?_, hlt⟩, rfl⟩)
          · obtain ⟨b, rest, rfl⟩ := List.exists_cons_of_ne_nil hune
            exact hau
          · exact List.perm_append_comm.trans (hu.append_right _)
          · obtain ⟨b, rest, rfl⟩ := List.exists_cons_of_ne_nil hw
            exact List.mem_append_right _ (hu.symm.subset (List.mem_cons_self))
        · show bracket (wordBracket K) (0 : W K) (X [c]) ∈ _
          rw [show bracket (wordBracket K) (0 : W K) (X [c]) = 0 from map_zero _]
          exact zero_mem _
        · intro x y _ _ hx hy
          rw [bracket_add_left]
          exact add_mem hx hy
        · intro a x _ hx
          rw [bracket_smul_left]
          exact Submodule.smul_mem _ a hx
      · obtain ⟨b, rest, rfl⟩ := List.exists_cons_of_ne_nil hw
        simp

/-- **Killing the bad words in a left-normed bracket leaves its word.** -/
theorem killBad_comb (w : List ℕ) (hnd : w.Nodup) (hne : w ≠ []) (hmin : ∀ a ∈ w, w.headI ≤ a) :
    killBad K (comb K w) = X w := by
  have h := killBad_badSpan (K := K) (comb_sub_mem w hnd hne hmin)
  rw [map_sub, sub_eq_zero, killBad, aeval_X, if_neg] at h
  · exact h
  · rintro ⟨a, ha, hlt⟩
    exact absurd (hmin a ha) (not_le.2 hlt)

/-! ## Cutting a permutation before its left-to-right minima -/

/-- **The blocks of a word**, cut before its left-to-right minima: each block is a letter followed
by the larger letters after it. -/
def cut : List ℕ → List (List ℕ)
  | [] => []
  | a :: rest =>
    (a :: rest.takeWhile (fun b => decide (a < b))) :: cut (rest.dropWhile fun b => decide (a < b))
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_dropWhile_le _ _)

/-- **The blocks concatenate to the word.** -/
theorem flatten_cut : ∀ l : List ℕ, (cut l).flatten = l
  | [] => by simp [cut]
  | a :: rest => by
    rw [cut, List.flatten_cons, flatten_cut (rest.dropWhile _), List.cons_append,
      List.takeWhile_append_dropWhile]
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_dropWhile_le _ _)

/-- **The first letter of a block is its least.** -/
theorem mem_cut : ∀ (l : List ℕ), ∀ B ∈ cut l, B ≠ [] ∧ ∀ x ∈ B, B.headI ≤ x
  | [] => by simp [cut]
  | a :: rest => by
    intro B hB
    rw [cut, List.mem_cons] at hB
    rcases hB with rfl | hB
    · refine ⟨List.cons_ne_nil _ _, fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact le_rfl
      · have h1 : decide (a < x) = true := List.mem_takeWhile_imp (p := fun b => decide (a < b)) hx
        exact (of_decide_eq_true h1).le
    · exact mem_cut _ B hB
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_dropWhile_le _ _)

/-- **The first letters of the blocks decrease**, for a word without repetition. -/
theorem pairwise_cut : ∀ (l : List ℕ), l.Nodup →
    (cut l).Pairwise (fun B C => C.headI < B.headI) ∧ ∀ B ∈ cut l, B.headI ≤ l.headI
  | [] => by simp [cut]
  | a :: rest => by
    intro hnd
    set d := rest.dropWhile fun b => decide (a < b) with hd
    have hdnd : d.Nodup := (List.nodup_cons.1 hnd).2.sublist (List.dropWhile_sublist _)
    obtain ⟨ih₁, ih₂⟩ := pairwise_cut d hdnd
    have hlt : ∀ C ∈ cut d, C.headI < a := by
      intro C hC
      refine lt_of_le_of_lt (ih₂ C hC) ?_
      cases hdc : d with
      | nil => rw [hdc, cut] at hC; simp at hC
      | cons b d' =>
        have hb : ¬ a < b := by
          have := List.head_dropWhile_not (fun b => decide (a < b)) (l := rest)
            (by rw [← hd, hdc]; exact List.cons_ne_nil _ _)
          simp only [← hd, hdc, List.head_cons] at this
          simpa using this
        have hba : b ≠ a := by
          rintro rfl
          have : b ∈ rest := (List.dropWhile_sublist _).subset (by rw [← hd, hdc]; simp)
          exact (List.nodup_cons.1 hnd).1 this
        show b < a
        omega
    rw [cut, List.pairwise_cons]
    refine ⟨⟨fun C hC => hlt C hC, ih₁⟩, fun B hB => ?_⟩
    rcases List.mem_cons.1 hB with rfl | hB
    · exact le_rfl
    · exact (hlt B hB).le
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_dropWhile_le _ _)

/-- **A word without repetition is determined by the multiset of its blocks.** -/
theorem cut_injective {l l' : List ℕ} (hl : l.Nodup) (hl' : l'.Nodup)
    (h : ((cut l : List (List ℕ)) : Multiset (List ℕ)) = (cut l' : Multiset (List ℕ))) :
    l = l' := by
  have hp := Quotient.exact h
  have heq : cut l = cut l' := List.Perm.eq_of_pairwise
    (le := fun B C => C.headI < B.headI) (fun _ _ _ _ h₁ h₂ => absurd (h₁.trans h₂) (lt_irrefl _))
    (pairwise_cut l hl).1 (pairwise_cut l' hl').1 hp
  rw [← flatten_cut l, ← flatten_cut l', heq]

/-! ## Independence -/

lemma prod_X_eq_monomial : ∀ bs : List (List ℕ),
    (bs.map fun B => (X B : W K)).prod = monomial (Multiset.toFinsupp (bs : Multiset (List ℕ))) 1
  | [] => by simp
  | B :: bs => by
    rw [List.map_cons, List.prod_cons, prod_X_eq_monomial bs, ← Multiset.cons_coe,
      ← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, X,
      monomial_mul, one_mul]

lemma killBad_prodB : ∀ bs : List (List ℕ), (∀ B ∈ bs, B.Nodup ∧ B ≠ [] ∧ ∀ x ∈ B, B.headI ≤ x) →
    killBad K (prodB K bs) = (bs.map fun B => (X B : W K)).prod
  | [], _ => by simp [prodB]
  | B :: bs, h => by
    rw [prodB, List.map_cons, List.prod_cons, map_mul, ← prodB, killBad_prodB bs fun C hC =>
      h C (by simp [hC]), List.map_cons, List.prod_cons]
    obtain ⟨h₁, h₂, h₃⟩ := h B (by simp)
    rw [killBad_comb B h₁ h₂ h₃]

variable (K) in
/-- **The products of the left-normed brackets of the blocks of the permutations.** -/
noncomputable def lead (n : ℕ) (l : (List.range n).permutations.toFinset) : W K :=
  prodB K (cut l.1)

lemma nodup_of_mem {n : ℕ} (l : (List.range n).permutations.toFinset) : l.1.Nodup :=
  (List.mem_permutations.1 (List.mem_toFinset.1 l.2)).nodup_iff.2 (List.nodup_range)

lemma block_props {l : List ℕ} (hl : l.Nodup) :
    ∀ B ∈ cut l, B.Nodup ∧ B ≠ [] ∧ ∀ x ∈ B, B.headI ≤ x := fun B hB =>
  ⟨hl.sublist ((flatten_cut l) ▸ List.sublist_flatten_of_mem hB), mem_cut l B hB⟩

/-- **The products of the left-normed brackets of the blocks are independent.** -/
theorem linearIndependent_lead (n : ℕ) : LinearIndependent K (lead K n) := by
  refine LinearIndependent.of_comp (killBad K).toLinearMap ?_
  have hf : (killBad K).toLinearMap ∘ lead K n = fun l =>
      (basisMonomials (List ℕ) K) (Multiset.toFinsupp (cut l.1 : Multiset (List ℕ))) := by
    funext l
    rw [Function.comp_apply, AlgHom.toLinearMap_apply, lead, killBad_prodB _
      (block_props (nodup_of_mem l)), prod_X_eq_monomial, coe_basisMonomials]
  rw [hf]
  exact (basisMonomials (List ℕ) K).linearIndependent.comp _ fun l l' h =>
    Subtype.ext (cut_injective (nodup_of_mem l) (nodup_of_mem l')
      (Multiset.toFinsupp.injective h))

/-- **They are values of trees.** -/
theorem lead_mem_Tsp {n : ℕ} (hn : 0 < n) (l : (List.range n).permutations.toFinset) :
    lead K n l ∈ Tsp K (Finset.range n) := by
  have hl := nodup_of_mem l
  have hp : l.1.Perm (List.range n) := List.mem_permutations.1 (List.mem_toFinset.1 l.2)
  have h := prodB_mem_Tsp (K := K) (cut l.1) (fun h => by
      have hlen := hp.length_eq
      rw [← flatten_cut l.1, h] at hlen
      simp at hlen
      omega)
    (by rw [flatten_cut]; exact hl) fun B hB => (mem_cut l.1 B hB).1
  rwa [flatten_cut, List.toFinset_eq_of_perm _ _ hp, List.toFinset_range] at h

lemma card_perms (n : ℕ) : Fintype.card (List.range n).permutations.toFinset = n.factorial := by
  rw [Fintype.card_coe, List.toFinset_card_of_nodup (List.nodup_permutations _ List.nodup_range),
    List.length_permutations, List.length_range]

/-! ## The lower bound -/

variable (K) in
/-- The algebra over the Poisson operad of polynomials in words. -/
noncomputable def alg : SymAlgebra K (Pois K) (W K) :=
  (BinPres.algebraEquiv _ _).symm ⟨μ K,
    fun _ h => by
      rcases h with rfl | rfl
      · exact (BinRel.comm_iff _ _).2 (wordPoisAlg K).comm
      · exact (BinRel.antisymm_iff _ _).2 (wordPoisAlg K).antisymm,
    fun _ h => by
      rcases h with rfl | rfl | rfl
      · exact (BinRel.assoc_iff _ _).2 (wordPoisAlg K).assoc
      · exact (BinRel.jacobi_iff _ _).2 (wordPoisAlg K).jacobi
      · exact (BinRel.leibnizRule_iff _ _ _).2 (wordPoisAlg K).leibniz⟩

variable (K) in
/-- **Evaluation of the operations at the variables of the letters.** -/
noncomputable def evalOp (s : Finset ℕ) : Pois K s →ₗ[K] W K where
  toFun q := (alg K).app s q fun a => X [a.1]
  map_add' q q' := by rw [map_add]; rfl
  map_smul' c q := by rw [map_smul]; rfl

lemma evalOp_proj (s : Finset ℕ) (x : Syn (BinGen PoisOp) s) :
    evalOp K s ((SymOperadIdeal.span K (rel23 _ _)).proj s (Finsupp.single (Pres.mk x) 1)) =
      sval x fun a => X [a.1] := by
  show (alg K).app s _ _ = _
  simp only [alg, BinPres.algebraEquiv, Equiv.symm_trans_apply]
  erw [SymOperadIdeal.presHomEquiv_symm_proj]
  show (binHom (μ K)).app s _ _ = _
  rw [binHom_single]
  rfl

/-- **The Poisson operad has at least `n!` operations of arity `n`.** -/
theorem factorial_le_finrank {n : ℕ} (hn : 0 < n) [Module.Finite K (Pois K (Finset.range n))] :
    n.factorial ≤ Module.finrank K (Pois K (Finset.range n)) := by
  have hT : Tsp K (Finset.range n) ≤ LinearMap.range (evalOp K (Finset.range n)) :=
    Submodule.span_le.2 (by
      rintro _ ⟨x, rfl⟩
      exact ⟨_, evalOp_proj _ x⟩)
  choose q hq using fun l => hT (lead_mem_Tsp (K := K) hn l)
  have li : LinearIndependent K q :=
    LinearIndependent.of_comp (evalOp K _) (by
      convert linearIndependent_lead (K := K) n using 1
      funext l
      exact hq l)
  rw [← card_perms n]
  exact li.fintype_card_le_finrank

end PoisDim

end Operad
