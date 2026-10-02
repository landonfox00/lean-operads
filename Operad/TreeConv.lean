/-
# The convolution operad of the free binary operad

For a non-symmetric operad `Q`, the cochains on planar binary trees with values in `Q`,

  `TConv R E Q n = (binary trees with n leaves) → Q n`,

form a non-symmetric operad (`instNSOperadTConv`): the composite `f ∘ₐ g` evaluates `f` and `g`
at the two pieces of the unique factorization of a tree at the slot `a` (`BTree.graft_inj`), and
vanishes on trees that do not factor there (`compFun_eq`, `compFun_eq_zero`). It is the
convolution operad `Hom(𝒯ᶜ(E), Q)` of the cofree cooperad on the binary generators `E` with
coefficients in `Q`.

Everything the deformation theory of operads needs then comes for free from the signed total
space of this operad: the convolution product `⋆ₛ` is graded right pre-Lie
(`sstar_assoc_symm`), its commutator satisfies graded Jacobi (`jacobiS`), the twisted
differential `[α, -]` of a Maurer–Cartan element squares to zero (`dLin_dLin`), and its
cohomology is `Operad.cohomology`.

Cochains with values in an ideal of `Q` form an ideal (`TConv.valuedIn`): the coefficients may be
restricted to an ideal such as `ker Σ`.
-/
import Operad.BinaryTree
import Operad.Ideal

universe u v w

namespace Operad

open NSOperad BTree

/-- **Cochains on binary trees** with values in `Q`: the convolution operad of the cofree
cooperad on `E`. -/
@[nolint unusedArguments]
abbrev TConv (R : Type u) [CommRing R] (E : Type v) (Q : ℕ → Type w) (n : ℕ) : Type (max v w) :=
  OfArity E n → Q n

namespace TConv

variable {R : Type u} [CommRing R] {E : Type v} {Q : ℕ → Type w}
  [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)] [NSOperad R Q]

open scoped Classical in
/-- The composite of two cochains at a tree: the value at its factorization, if any. -/
noncomputable def compFun (a b : ℕ) {n : ℕ} (f : TConv R E Q (a + 1 + b)) (g : TConv R E Q n)
    (t : OfArity E (a + n + b)) : Q (a + n + b) :=
  if h : ∃ p : OfArity E (a + 1 + b) × OfArity E n, (OfArity.graft a b p.1 p.2).1 = t.1 then
    NSOperad.comp (R := R) a b (f (Classical.choose h).1) (g (Classical.choose h).2)
  else 0

/-- **The composite at a factored tree.** -/
lemma compFun_eq (a b : ℕ) {n : ℕ} (f : TConv R E Q (a + 1 + b)) (g : TConv R E Q n)
    {t : OfArity E (a + n + b)} (t₁ : OfArity E (a + 1 + b)) (t₂ : OfArity E n)
    (ht : t₁.1.graft a t₂.1 = t.1) :
    compFun a b f g t = NSOperad.comp (R := R) a b (f t₁) (g t₂) := by
  have h : ∃ p : OfArity E (a + 1 + b) × OfArity E n, (OfArity.graft a b p.1 p.2).1 = t.1 :=
    ⟨(t₁, t₂), ht⟩
  rw [compFun, dif_pos h]
  have hs := Classical.choose_spec h
  obtain ⟨h1, h2⟩ := OfArity.graft_inj a b (Subtype.ext (hs.trans ht.symm) :
    OfArity.graft a b (Classical.choose h).1 (Classical.choose h).2 = OfArity.graft a b t₁ t₂)
  rw [h1, h2]

/-- **The composite vanishes at a tree that does not factor.** -/
lemma compFun_eq_zero (a b : ℕ) {n : ℕ} (f : TConv R E Q (a + 1 + b)) (g : TConv R E Q n)
    {t : OfArity E (a + n + b)}
    (ht : ∀ (t₁ : OfArity E (a + 1 + b)) (t₂ : OfArity E n), t₁.1.graft a t₂.1 ≠ t.1) :
    compFun a b f g t = 0 :=
  dif_neg fun ⟨p, hp⟩ => ht p.1 p.2 hp

/-- Composition of cochains, bilinear. -/
noncomputable def compL (a b : ℕ) {n : ℕ} :
    TConv R E Q (a + 1 + b) →ₗ[R] TConv R E Q n →ₗ[R] TConv R E Q (a + n + b) :=
  LinearMap.mk₂ R (fun f g t => compFun a b f g t)
    (fun f f' g => funext fun t => by
      show compFun a b (f + f') g t = compFun a b f g t + compFun a b f' g t
      unfold compFun
      split_ifs
      · simp only [Pi.add_apply, map_add, LinearMap.add_apply]
      · simp)
    (fun c f g => funext fun t => by
      show compFun a b (c • f) g t = c • compFun a b f g t
      unfold compFun
      split_ifs
      · simp only [Pi.smul_apply, map_smul, LinearMap.smul_apply]
      · simp)
    (fun f g g' => funext fun t => by
      show compFun a b f (g + g') t = compFun a b f g t + compFun a b f g' t
      unfold compFun
      split_ifs
      · simp only [Pi.add_apply, map_add]
      · simp)
    (fun c f g => funext fun t => by
      show compFun a b f (c • g) t = c • compFun a b f g t
      unfold compFun
      split_ifs
      · simp only [Pi.smul_apply, map_smul]
      · simp)

@[simp] lemma compL_apply (a b : ℕ) {n : ℕ} (f : TConv R E Q (a + 1 + b)) (g : TConv R E Q n)
    (t : OfArity E (a + n + b)) : compL a b f g t = compFun a b f g t := rfl

omit [NSOperad R Q] in
lemma reindex_apply {m n : ℕ} (h : m = n) (f : TConv R E Q m) (t : OfArity E n) :
    reindex R (TConv R E Q) h f t = reindex R Q h (f (OfArity.cast h.symm t)) := by
  subst h
  rfl

/-- The leaf is the only tree of arity one. -/
lemma eq_one (t : OfArity E 1) : t = OfArity.one :=
  Subtype.ext (eq_leaf_of_arity_eq_one t.2)

end TConv

open TConv in
/-- **The convolution operad of the free binary operad.** -/
noncomputable instance instNSOperadTConv (R : Type u) [CommRing R] (E : Type v)
    (Q : ℕ → Type w) [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)] [NSOperad R Q] :
    NSOperad R (TConv R E Q) where
  one := fun _ => NSOperad.one (R := R)
  comp a b := compL a b
  comp_one_right a b α := funext fun t => by
    rw [compL_apply, compFun_eq a b α _ t OfArity.one (graft_leaf_right t.1 a)]
    exact NSOperad.comp_one_right a b (α t)
  comp_one_left α := funext fun t => by
    rw [reindex_apply, compL_apply,
      compFun_eq 0 0 _ α OfArity.one ⟨t.1, t.2⟩ (by rfl)]
    exact NSOperad.comp_one_left (R := R) (α t)
  comp_assoc_seq a b c d p α β γ := funext fun t => by
    rw [reindex_apply, compL_apply, compL_apply]
    by_cases hfac : ∃ (t₁ : OfArity E (a + 1 + b)) (t₂ : OfArity E (c + 1 + d))
        (t₃ : OfArity E p), t₁.1.graft a (t₂.1.graft c t₃.1) = t.1
    · obtain ⟨t₁, t₂, t₃, ht⟩ := hfac
      have hin : (OfArity.graft c d t₂ t₃).1 = t₂.1.graft c t₃.1 := rfl
      have hseq := graft_graft_seq t₁.1 a t₂.1 c t₃.1 (by rw [t₁.2]; omega) (by rw [t₂.2]; omega)
      rw [compFun_eq a b α _ t₁ (OfArity.graft c d t₂ t₃) (by rw [hin]; exact ht),
        compL_apply, compFun_eq c d β γ t₂ t₃ rfl,
        compFun_eq (a + c) (d + b) _ γ (OfArity.cast (by omega) (OfArity.graft a b t₁ t₂)) t₃
          (by rw [OfArity.cast_val, OfArity.graft_val, hseq]; exact ht),
        reindex_apply, compL_apply,
        compFun_eq a b α β (t := OfArity.cast _ (OfArity.cast _ (OfArity.graft a b t₁ t₂))) t₁ t₂
          rfl]
      exact NSOperad.comp_assoc_seq (R := R) a b c d (α t₁) (β t₂) (γ t₃)
    · push Not at hfac
      rw [show compFun a b α (compL c d β γ) t = 0 by
        by_cases h1 : ∃ (t₁ : OfArity E (a + 1 + b)) (v : OfArity E (c + p + d)),
            t₁.1.graft a v.1 = t.1
        · obtain ⟨t₁, v, hv⟩ := h1
          rw [compFun_eq a b α _ t₁ v hv, compL_apply,
            compFun_eq_zero c d β γ (fun t₂ t₃ h => hfac t₁ t₂ t₃ (by rw [h]; exact hv)),
            map_zero]
        · push Not at h1
          exact compFun_eq_zero a b α _ h1]
      rw [show compFun (a + c) (d + b) (reindex R (TConv R E Q) _ (compL a b α β)) γ
          (OfArity.cast _ t) = 0 by
        by_cases h1 : ∃ (u : OfArity E (a + c + 1 + (d + b))) (t₃ : OfArity E p),
            u.1.graft (a + c) t₃.1 = t.1
        · obtain ⟨u, t₃, hu⟩ := h1
          rw [compFun_eq (a + c) (d + b) _ γ u t₃ hu, reindex_apply, compL_apply,
            compFun_eq_zero a b α β (fun t₁ t₂ h => by
              have hseq := graft_graft_seq t₁.1 a t₂.1 c t₃.1 (by rw [t₁.2]; omega)
                (by rw [t₂.2]; omega)
              refine hfac t₁ t₂ t₃ ?_
              rw [← hseq, ← hu]
              exact congrArg (fun x => BTree.graft x (a + c) t₃.1) h)]
          simp only [map_zero, LinearMap.zero_apply]
        · push Not at h1
          exact compFun_eq_zero _ _ _ γ h1, map_zero]
  comp_assoc_par a b c n p α β γ := funext fun t => by
    rw [reindex_apply, compL_apply, compL_apply]
    by_cases hfac : ∃ (t₁ : OfArity E (a + 1 + b + 1 + c)) (t₂ : OfArity E n)
        (t₃ : OfArity E p), (t₁.1.graft (a + 1 + b) t₃.1).graft a t₂.1 = t.1
    · obtain ⟨t₁, t₂, t₃, ht⟩ := hfac
      have hpar := graft_graft_par t₁.1 a t₂.1 (a + 1 + b) t₃.1 (by omega) (by rw [t₁.2]; omega)
      rw [compFun_eq a (b + p + c) _ β
          (OfArity.cast (by omega) (OfArity.graft (a + 1 + b) c t₁ t₃)) t₂
          (by rw [OfArity.cast_val, OfArity.graft_val]; exact ht),
        reindex_apply, compL_apply,
        compFun_eq (a + 1 + b) c α γ (t := OfArity.cast _ (OfArity.cast _
          (OfArity.graft (a + 1 + b) c t₁ t₃))) t₁ t₃ rfl,
        compFun_eq (a + n + b) c _ γ
          (OfArity.cast (by omega) (OfArity.graft a (b + 1 + c) (OfArity.cast (by omega) t₁) t₂))
          t₃ (by
            simp only [OfArity.cast_val, OfArity.graft_val]
            rw [← ht, ← hpar, t₂.2]
            congr 1
            omega),
        reindex_apply, compL_apply,
        compFun_eq a (b + 1 + c) _ β (t := OfArity.cast _ (OfArity.cast _
          (OfArity.graft a (b + 1 + c) (OfArity.cast _ t₁) t₂))) (OfArity.cast (by omega) t₁) t₂
          rfl,
        reindex_apply]
      simp only [OfArity.cast_cast, OfArity.cast_self]
      exact NSOperad.comp_assoc_par (R := R) a b c (α t₁) (β t₂) (γ t₃)
    · push Not at hfac
      rw [show compFun a (b + p + c) (reindex R (TConv R E Q) _ (compL (a + 1 + b) c α γ)) β t
          = 0 by
        by_cases h1 : ∃ (u : OfArity E (a + 1 + (b + p + c))) (t₂ : OfArity E n),
            u.1.graft a t₂.1 = t.1
        · obtain ⟨u, t₂, hu⟩ := h1
          rw [compFun_eq a (b + p + c) _ β u t₂ hu, reindex_apply, compL_apply,
            compFun_eq_zero (a + 1 + b) c α γ (fun t₁ t₃ h => hfac t₁ t₂ t₃ (by
              rw [← hu]
              exact congrArg (fun x => BTree.graft x a t₂.1) h))]
          simp only [map_zero, LinearMap.zero_apply]
        · push Not at h1
          exact compFun_eq_zero _ _ _ β h1]
      rw [show compFun (a + n + b) c (reindex R (TConv R E Q) _ (compL a (b + 1 + c)
          (reindex R (TConv R E Q) _ α) β)) γ (OfArity.cast _ t) = 0 by
        by_cases h1 : ∃ (u : OfArity E (a + n + b + 1 + c)) (t₃ : OfArity E p),
            u.1.graft (a + n + b) t₃.1 = t.1
        · obtain ⟨u, t₃, hu⟩ := h1
          rw [compFun_eq (a + n + b) c _ γ u t₃ hu, reindex_apply, compL_apply,
            compFun_eq_zero a (b + 1 + c) _ β (fun t₁ t₂ h => by
              have hpar := graft_graft_par t₁.1 a t₂.1 (a + 1 + b) t₃.1 (by omega)
                (by rw [t₁.2]; omega)
              refine hfac (OfArity.cast (by omega) t₁) t₂ t₃ ?_
              rw [OfArity.cast_val, ← hpar, ← hu]
              congr 1
              rw [t₂.2]
              omega)]
          simp only [map_zero, LinearMap.zero_apply]
        · push Not at h1
          exact compFun_eq_zero _ _ _ γ h1, map_zero]

namespace TConv

variable {R : Type u} [CommRing R] {E : Type v} {Q : ℕ → Type w}
  [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)] [NSOperad R Q]

lemma comp_apply (a b : ℕ) {n : ℕ} (f : TConv R E Q (a + 1 + b)) (g : TConv R E Q n)
    (t : OfArity E (a + n + b)) :
    NSOperad.comp (R := R) (P := TConv R E Q) a b f g t = compFun a b f g t := rfl

/-- **Cochains with values in an ideal form an ideal** (the coefficients may be restricted to an
ideal of `Q`). -/
def valuedIn (I : OperadIdeal R Q) : OperadIdeal R (TConv R E Q) where
  carrier n :=
    { carrier := {f | ∀ t, f t ∈ I.carrier n}
      add_mem' := fun hf hg t => (I.carrier _).add_mem (hf t) (hg t)
      zero_mem' := fun _ => (I.carrier _).zero_mem
      smul_mem' := fun c _ hf t => (I.carrier _).smul_mem c (hf t) }
  comp_mem_left a b n f hf g t := by
    show compFun a b f g t ∈ I.carrier _
    unfold compFun
    split_ifs
    · exact I.comp_mem_left a b (hf _) _
    · exact (I.carrier _).zero_mem
  comp_mem_right a b n f g hg t := by
    show compFun a b f g t ∈ I.carrier _
    unfold compFun
    split_ifs
    · exact I.comp_mem_right a b _ (hg _)
    · exact (I.carrier _).zero_mem

end TConv

end Operad
