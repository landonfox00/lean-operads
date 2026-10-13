/-
# The Poincaré–Birkhoff–Witt theorem

For a Lie algebra `g` over a commutative ring `R` with a basis `b` indexed by a well-ordered type
`I`, **the products of the basis vectors along the nondecreasing words are a basis of the
universal enveloping algebra** (`PBW.basis`, `PBW.basis_apply`); in particular the canonical map
`g → U g` is injective for every Lie algebra which is free as a module (`PBW.ι_injective`).

This is the classical instance of inhomogeneous Koszul duality: the enveloping algebra is
presented by the quadratic-linear relations `b j b i = b i b j + [b j, b i]`, and the theorem says
that its associated graded algebra is the symmetric algebra, presented by their quadratic parts.
The proof is the diamond lemma for free algebras (`Words`):

* **the rules** (`PBW.rules`): the word `j i` reduces to `i j + [b j, b i]` for `i < j`, the
  bracket expanded in the basis as one-letter words (`PBW.lin`); the normal words are the
  nondecreasing ones (`PBW.normal_iff_isChain`);
* **the critical ambiguities** are the words `k j i` with `i < j < k`, and they are resolvable by
  the Jacobi identity (`PBW.overlap_res`, `PBW.res_critical`); so the nondecreasing words are a
  basis of the free module on the words modulo the ideal of the rules;
* **this quotient is the enveloping algebra** (`PBW.quotEquiv`): the products of the basis vectors
  kill the ideal (`PBW.ideal_le_ker`) and span; conversely the Lie algebra acts on the quotient by
  left multiplication of words (`PBW.ρ`), and the action of the enveloping algebra on the class of
  the empty word is a left inverse (`PBW.ψ_toQU`).
-/
import Operad.DiamondWords
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.Data.List.Chain
import Mathlib.SetTheory.Ordinal.Basic

namespace Operad

namespace PBW

open Finsupp Words STree UniversalEnvelopingAlgebra

variable (R : Type*) [CommRing R] {g : Type*} [LieRing g] [LieAlgebra R g]
  {I : Type*} (b : Module.Basis I R g)

/-! ## Words and the enveloping algebra -/

/-- **A Lie element as a combination of one-letter words.** -/
noncomputable def lin : g →ₗ[R] (List I →₀ R) :=
  lmapDomain R R (fun a => [a]) ∘ₗ b.repr.toLinearMap

lemma lin_apply (x : g) : lin R b x = mapDomain (fun a => [a]) (b.repr x) := rfl

lemma lin_basis (a : I) : lin R b (b a) = single [a] 1 := by
  rw [lin_apply, Module.Basis.repr_self, mapDomain_single]

/-- **The context** `w ↦ u ++ w ++ v`, as a linear map. -/
noncomputable def ctxL (u v : List I) : (List I →₀ R) →ₗ[R] (List I →₀ R) :=
  lmapDomain R R fun w => u ++ w ++ v

lemma ctxL_apply (u v : List I) (x : List I →₀ R) :
    ctxL R u v x = mapDomain (fun w => u ++ w ++ v) x := rfl

lemma ctxL_single (u v w : List I) (c : R) :
    ctxL R u v (single w c) = single (u ++ w ++ v) c :=
  mapDomain_single

lemma ctxL_nil : ctxL R ([] : List I) [] = LinearMap.id :=
  lhom_ext fun w c => by rw [ctxL_single, List.nil_append, List.append_nil]; rfl

lemma small_lists : ∀ {u v : List I}, u.length + v.length < 2 →
    (u = [] ∧ v = []) ∨ (u = [] ∧ ∃ d, v = [d]) ∨ (∃ c, u = [c] ∧ v = [])
  | [], [], _ => Or.inl ⟨rfl, rfl⟩
  | [], [d], _ => Or.inr (Or.inl ⟨rfl, d, rfl⟩)
  | [], _ :: _ :: _, h => by simp only [List.length_cons, List.length_nil] at h; omega
  | [c], [], _ => Or.inr (Or.inr ⟨c, rfl, rfl⟩)
  | [_], _ :: _, h => by simp only [List.length_cons, List.length_nil] at h; omega
  | _ :: _ :: _, _, h => by simp only [List.length_cons] at h; omega

/-- **The product of the basis vectors along a word.** -/
noncomputable def prodι (w : List I) : UniversalEnvelopingAlgebra R g :=
  (w.map fun a => ι R (b a)).prod

lemma prodι_append (u v : List I) : prodι R b (u ++ v) = prodι R b u * prodι R b v := by
  simp [prodι, List.map_append, List.prod_append]

lemma prodι_cons (a : I) (w : List I) : prodι R b (a :: w) = ι R (b a) * prodι R b w := by
  simp [prodι]

/-- **Words to the enveloping algebra.** -/
noncomputable def toU : (List I →₀ R) →ₗ[R] UniversalEnvelopingAlgebra R g :=
  linearCombination R (prodι R b)

lemma toU_single (w : List I) (c : R) : toU R b (single w c) = c • prodι R b w :=
  linearCombination_single R c w

lemma toU_ctxL (u v : List I) (x : List I →₀ R) :
    toU R b (ctxL R u v x) = prodι R b u * toU R b x * prodι R b v := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, mul_add, add_mul]
  | single w c =>
    rw [ctxL_single, toU_single, toU_single, prodι_append, prodι_append, mul_smul_comm,
      smul_mul_assoc]

lemma toU_lin (x : g) : toU R b (lin R b x) = ι R x := by
  have : toU R b ∘ₗ lin R b = (ι R : g →ₗ⁅R⁆ UniversalEnvelopingAlgebra R g).toLinearMap :=
    b.ext fun a => by simp [lin_basis, toU_single, prodι]
  exact LinearMap.congr_fun this x

lemma toU_rel (i j : I) :
    toU R b (single [j, i] 1 - single [i, j] 1 - lin R b ⁅b j, b i⁆) = 0 := by
  rw [map_sub, map_sub, toU_single, toU_single, toU_lin, one_smul, one_smul, LieHom.map_lie,
    LieRing.of_associative_ring_bracket]
  simp [prodι]


lemma ι_mul_toU (x : g) (y : List I →₀ R) :
    ι R x * toU R b y = toU R b (b.constr R (fun a => ctxL R [a] [] y) x) := by
  have : (LinearMap.mulRight R (toU R b y)) ∘ₗ
      (ι R : g →ₗ⁅R⁆ UniversalEnvelopingAlgebra R g).toLinearMap =
      toU R b ∘ₗ b.constr R (fun a => ctxL R [a] [] y) := b.ext fun a => by
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
      LieHom.coe_toLinearMap, Module.Basis.constr_basis, toU_ctxL]
    simp [prodι]
  exact LinearMap.congr_fun this x

/-- **The products of the basis vectors span the enveloping algebra.** -/
theorem toU_surjective : Function.Surjective (toU R b) := by
  let S := LinearMap.range (toU R b)
  have h1 : (1 : UniversalEnvelopingAlgebra R g) ∈ S := ⟨single [] 1, by simp [toU_single, prodι]⟩
  have hι : ∀ x : g, ∀ s ∈ S, ι R x * s ∈ S := by
    rintro x _ ⟨y, rfl⟩
    exact ⟨_, (ι_mul_toU R b x y).symm⟩
  let T : Subalgebra R (UniversalEnvelopingAlgebra R g) :=
    { carrier := {u | ∀ s ∈ S, u * s ∈ S}
      mul_mem' := fun {u v} hu hv s hs => by rw [mul_assoc]; exact hu _ (hv s hs)
      one_mem' := fun s hs => by rw [one_mul]; exact hs
      add_mem' := fun {u v} hu hv s hs => by rw [add_mul]; exact add_mem (hu s hs) (hv s hs)
      zero_mem' := fun s _ => by rw [zero_mul]; exact zero_mem _
      algebraMap_mem' := fun r s hs => by
        rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
        exact Submodule.smul_mem _ r hs }
  have hT : ∀ t, mkAlgHom R g t ∈ T := fun t => by
    induction t using TensorAlgebra.induction with
    | algebraMap r => rw [AlgHom.commutes]; exact T.algebraMap_mem r
    | ι x => rw [← ι_apply]; exact hι x
    | mul a c ha hc => rw [map_mul]; exact T.mul_mem ha hc
    | add a c ha hc => rw [map_add]; exact T.add_mem ha hc
  intro u
  obtain ⟨t, rfl⟩ := RingQuot.mkAlgHom_surjective R (Rel R g) u
  have := hT t 1 h1
  rw [mul_one] at this
  exact this

variable [LinearOrder I]

/-- A word which is not nondecreasing has a descent. -/
lemma exists_descent : ∀ {w : List I}, ¬ w.IsChain (· ≤ ·) →
    ∃ u x y v, w = u ++ [x, y] ++ v ∧ ¬ x ≤ y
  | [], h => absurd List.IsChain.nil h
  | [a], h => absurd (List.IsChain.singleton a) h
  | a :: c :: w, h => by
    rw [List.isChain_cons_cons] at h
    by_cases hac : a ≤ c
    · obtain ⟨u, x, y, v, hw, hxy⟩ := exists_descent fun h' => h ⟨hac, h'⟩
      exact ⟨a :: u, x, y, v, by rw [hw]; rfl, hxy⟩
    · exact ⟨[], a, c, w, rfl, hac⟩

variable [WellFoundedLT I]

/-! ## The rules -/

/-- **The pairs** `i < j`, which index the rules. -/
abbrev Pair (I : Type*) [LT I] := {p : I × I // p.1 < p.2}

/-- **The rules of the enveloping algebra**: the word `j i` reduces to `i j + [b j, b i]` for
`i < j`. -/
noncomputable def rules : Rules R (Pair I) (ctxOrder I) where
  src _ := ()
  lead r := [r.1.2, r.1.1]
  tail r := single [r.1.1, r.1.2] 1 + lin R b ⁅b r.1.2, b r.1.1⁆
  tail_lt r m hm := by
    classical
    rcases Finset.mem_union.1 (support_add hm) with h | h
    · rw [Finset.mem_singleton.1 (support_single_subset h)]
      exact Or.inr ⟨rfl, List.Lex.rel r.2⟩
    · rw [lin_apply] at h
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 (mapDomain_support h)
      exact Or.inl (by simp)

lemma lead_eq (r : Pair I) : (rules R b).lead r = [r.1.2, r.1.1] := rfl

lemma tail_eq (r : Pair I) :
    (rules R b).tail r = single [r.1.1, r.1.2] 1 + lin R b ⁅b r.1.2, b r.1.1⁆ := rfl

/-- **The normal words** are the nondecreasing ones. -/
lemma normal_iff_isChain (w : List I) :
    (rules R b).Normal (b := ()) w ↔ w.IsChain (· ≤ ·) := by
  rw [Words.normal_iff]
  constructor
  · intro h
    by_contra hc
    obtain ⟨u, x, y, v, rfl, hxy⟩ := exists_descent hc
    exact h ⟨(y, x), lt_of_not_ge hxy⟩ u v rfl
  · rintro hc r u v rfl
    have := hc.infix ⟨u, v, rfl⟩
    rw [lead_eq, List.isChain_pair] at this
    exact absurd r.2 (not_lt.2 this)

/-! ## Resolving the ambiguities -/

/-- **The rewriting system of the rules.** -/
noncomputable abbrev sys : Rewriting R (List I) := (rules R b).rw ()

lemma red_ctx (r : Pair I) (u v : List I) :
    ctxL R u v ((rules R b).tail r) ∈ (sys R b).red (u ++ [r.1.2, r.1.1] ++ v) :=
  ⟨r, fun w => u ++ w ++ v, ⟨u, v, fun _ => rfl⟩, rfl, rfl⟩

/-- **A reduction in a context.** -/
lemma rel_mem {s : Set (List I)} {i j : I} (h : i < j) (u v : List I)
    (hs : u ++ [j, i] ++ v ∈ s) :
    single (u ++ [j, i] ++ v) 1 - (single (u ++ [i, j] ++ v) 1 +
      ctxL R u v (lin R b ⁅b j, b i⁆)) ∈ (sys R b).idealOn s := by
  have := (sys R b).sub_mem_idealOn hs (red_ctx R b ⟨(i, j), h⟩ u v)
  rwa [tail_eq, map_add, ctxL_single] at this

/-- **Two letters commute up to their bracket**, modulo the rules at the words of length two. -/
lemma swap_mem {s : Set (List I)} (hs : ∀ w : List I, w.length = 2 → w ∈ s) (c a : I) :
    single [c, a] 1 - single [a, c] 1 - lin R b ⁅b c, b a⁆ ∈ (sys R b).idealOn s := by
  rcases lt_trichotomy a c with h | rfl | h
  · have := rel_mem R b h [] [] (hs _ rfl)
    simp only [List.nil_append, List.append_nil, ctxL_nil, LinearMap.id_apply] at this
    rwa [sub_add_eq_sub_sub] at this
  · simp
  · have := rel_mem R b h [] [] (hs _ rfl)
    simp only [List.nil_append, List.append_nil, ctxL_nil, LinearMap.id_apply] at this
    have e : single [c, a] 1 - single [a, c] 1 - lin R b ⁅b c, b a⁆ =
        -(single [a, c] 1 - (single [c, a] 1 + lin R b ⁅b a, b c⁆)) := by
      rw [← lie_skew (b a) (b c), map_neg]
      abel
    rw [e]
    exact neg_mem this

/-- **A letter commutes with a Lie element up to their bracket.** -/
lemma lin_swap {s : Set (List I)} (hs : ∀ w : List I, w.length = 2 → w ∈ s) (c : I) (x : g) :
    ctxL R [c] [] (lin R b x) - ctxL R [] [c] (lin R b x) - lin R b ⁅b c, x⁆ ∈
      (sys R b).idealOn s := by
  let F : g →ₗ[R] (List I →₀ R) := ctxL R [c] [] ∘ₗ lin R b - ctxL R [] [c] ∘ₗ lin R b -
    lin R b ∘ₗ (LieModule.toEnd R g g (b c) : g →ₗ[R] g)
  have hF : ⊤ ≤ ((sys R b).idealOn s).comap F := by
    rw [← b.span_eq, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    simp only [F, SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply,
      LinearMap.coe_comp, Function.comp_apply, LieModule.toEnd_apply_apply, lin_basis,
      ctxL_single, List.nil_append, List.append_nil, List.singleton_append]
    exact swap_mem R b hs c a
  exact hF Submodule.mem_top

/-- **The overlap `k j i` is resolvable**, by the Jacobi identity. -/
theorem overlap_res {i j k : I} (hij : i < j) (hjk : j < k) :
    ctxL R [] [i] ((rules R b).tail ⟨(j, k), hjk⟩) -
      ctxL R [k] [] ((rules R b).tail ⟨(i, j), hij⟩) ∈
        (sys R b).idealOn ((sys R b).below [k, j, i]) := by
  have hik := hij.trans hjk
  have h2 : ∀ w : List I, w.length = 2 → w ∈ (sys R b).below [k, j, i] :=
    fun w hw => Or.inl (by simp [hw])
  have ha := rel_mem R b hik [j] [] (s := (sys R b).below [k, j, i])
    (Or.inr ⟨rfl, List.Lex.rel hjk⟩)
  have hb := rel_mem R b hij [] [k] (s := (sys R b).below [k, j, i])
    (Or.inr ⟨rfl, List.Lex.rel hjk⟩)
  have hc := rel_mem R b hik [] [j] (s := (sys R b).below [k, j, i])
    (Or.inr ⟨rfl, List.Lex.cons (List.Lex.rel hij)⟩)
  have hd := rel_mem R b hjk [i] [] (s := (sys R b).below [k, j, i])
    (Or.inr ⟨rfl, List.Lex.rel hik⟩)
  have he₁ := lin_swap R b h2 j ⁅b k, b i⁆
  have he₂ := lin_swap R b h2 k ⁅b j, b i⁆
  have he₃ := lin_swap R b h2 i ⁅b k, b j⁆
  have hJ : lin R b ⁅b j, ⁅b k, b i⁆⁆ - lin R b ⁅b k, ⁅b j, b i⁆⁆ -
      lin R b ⁅b i, ⁅b k, b j⁆⁆ = 0 := by
    rw [← map_sub, ← map_sub, leibniz_lie (b k) (b j) (b i), ← lie_skew (b i) ⁅b k, b j⁆]
    rw [show ⁅b j, ⁅b k, b i⁆⁆ - (⁅⁅b k, b j⁆, b i⁆ + ⁅b j, ⁅b k, b i⁆⁆) - -⁅⁅b k, b j⁆, b i⁆ =
      (0 : g) by abel, map_zero]
  simp only [List.nil_append, List.append_nil, List.cons_append] at ha hb hc hd
  rw [tail_eq, tail_eq, map_add, map_add, ctxL_single, ctxL_single]
  simp only [List.nil_append, List.append_nil, List.cons_append]
  have key : single [j, k, i] 1 + ctxL R [] [i] (lin R b ⁅b k, b j⁆) -
      (single [k, i, j] 1 + ctxL R [k] [] (lin R b ⁅b j, b i⁆)) =
      (single [j, k, i] 1 - (single [j, i, k] 1 + ctxL R [j] [] (lin R b ⁅b k, b i⁆))) +
      (single [j, i, k] 1 - (single [i, j, k] 1 + ctxL R [] [k] (lin R b ⁅b j, b i⁆))) -
      (single [k, i, j] 1 - (single [i, k, j] 1 + ctxL R [] [j] (lin R b ⁅b k, b i⁆))) -
      (single [i, k, j] 1 - (single [i, j, k] 1 + ctxL R [i] [] (lin R b ⁅b k, b j⁆))) +
      (ctxL R [j] [] (lin R b ⁅b k, b i⁆) - ctxL R [] [j] (lin R b ⁅b k, b i⁆) -
        lin R b ⁅b j, ⁅b k, b i⁆⁆) -
      (ctxL R [k] [] (lin R b ⁅b j, b i⁆) - ctxL R [] [k] (lin R b ⁅b j, b i⁆) -
        lin R b ⁅b k, ⁅b j, b i⁆⁆) -
      (ctxL R [i] [] (lin R b ⁅b k, b j⁆) - ctxL R [] [i] (lin R b ⁅b k, b j⁆) -
        lin R b ⁅b i, ⁅b k, b j⁆⁆) +
      (lin R b ⁅b j, ⁅b k, b i⁆⁆ - lin R b ⁅b k, ⁅b j, b i⁆⁆ - lin R b ⁅b i, ⁅b k, b j⁆⁆) := by
    abel
  rw [key, hJ, add_zero]
  exact sub_mem (sub_mem (add_mem (sub_mem (sub_mem (add_mem ha hb) hc) hd) he₁) he₂) he₃

/-- **Every critical ambiguity is resolvable.** -/
theorem res_critical {r₁ r₂ : Pair I} (B : (rules R b).Amb () r₁ r₂)
    (hB : Critical (rules R b) B) : B.Res := by
  obtain ⟨a₁, b₁, a₂, b₂, h₁, h₂, ha, hb, hl⟩ := hB
  have ht₁ : B.top = a₁ ++ [r₁.1.2, r₁.1.1] ++ b₁ := h₁ _
  have ht₂ : B.top = a₂ ++ [r₂.1.2, r₂.1.1] ++ b₂ := B.eq.trans (h₂ _)
  have hl₁ : a₁.length + b₁.length < 2 := by
    rw [ht₁, lead_eq, lead_eq] at hl
    simp only [List.length_append, List.length_cons, List.length_nil] at hl
    omega
  have hl₂ : a₂.length + b₂.length = a₁.length + b₁.length := by
    have := congrArg List.length (ht₁.symm.trans ht₂)
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    omega
  obtain ⟨⟨i₁, j₁⟩, hr₁⟩ := r₁
  obtain ⟨⟨i₂, j₂⟩, hr₂⟩ := r₂
  have heq := ht₁.symm.trans ht₂
  rcases small_lists hl₁ with ⟨rfl, rfl⟩ | ⟨rfl, d, rfl⟩ | ⟨c, rfl, rfl⟩
  · -- the same occurrence
    obtain ⟨rfl, rfl⟩ : a₂ = [] ∧ b₂ = [] := by
      simp only [List.length_nil, add_zero] at hl₂
      exact ⟨List.eq_nil_of_length_eq_zero (by omega), List.eq_nil_of_length_eq_zero (by omega)⟩
    simp only [List.nil_append, List.append_nil, List.cons.injEq, and_true] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact B.res_of_eq (funext fun w => by rw [h₁, h₂])
  · -- the overlap `j₁ i₁ d`
    obtain ⟨rfl, c, rfl⟩ : b₂ = [] ∧ ∃ c, a₂ = [c] := by
      rcases hb with h | h
      · exact absurd h (List.cons_ne_nil _ _)
      · subst h
        simp only [List.length_nil, add_zero, List.length_singleton] at hl₂
        exact ⟨rfl, List.length_eq_one_iff.1 hl₂⟩
    simp only [List.nil_append, List.append_nil, List.cons_append, List.cons.injEq,
      and_true] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    have hf₁ : B.f₁ = fun w => [] ++ w ++ [d] := funext h₁
    have hf₂ : B.f₂ = fun w => [j₁] ++ w ++ [] := funext h₂
    rw [Rules.Amb.Res, hf₁, hf₂, ht₁]
    exact overlap_res R b hr₂ hr₁
  · -- the overlap `c j₁ i₁`, in the other order
    obtain ⟨rfl, d, rfl⟩ : a₂ = [] ∧ ∃ d, b₂ = [d] := by
      rcases ha with h | h
      · exact absurd h (List.cons_ne_nil _ _)
      · subst h
        simp only [List.length_nil, zero_add, add_zero, List.length_singleton] at hl₂
        exact ⟨rfl, List.length_eq_one_iff.1 hl₂⟩
    simp only [List.nil_append, List.append_nil, List.cons_append, List.cons.injEq,
      and_true] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    rw [← Rules.Amb.res_swap]
    have hf₁ : B.swap.f₁ = fun w => [] ++ w ++ [i₁] := funext h₂
    have hf₂ : B.swap.f₂ = fun w => [c] ++ w ++ [] := funext h₁
    rw [Rules.Amb.Res, hf₁, hf₂, Rules.Amb.swap_top, ht₁]
    exact overlap_res R b hr₁ hr₂

/-- **The rules of the enveloping algebra are confluent.** -/
theorem resolvable : (sys R b).Resolvable :=
  Words.resolvable_of_critical _ (fun _ => List.cons_ne_nil _ _)
    fun B hB => res_critical R b B hB

/-- **The products of the basis vectors kill the ideal of the rules.** -/
theorem ideal_le_ker : (sys R b).ideal ≤ LinearMap.ker (toU R b) := by
  rw [Rules.ideal_eq_span, Submodule.span_le]
  rintro _ ⟨r, f, ⟨u, v, hf⟩, rfl⟩
  have hf' : f = fun w => u ++ w ++ v := funext hf
  subst hf'
  show toU R b (ctxL R u v (single [r.1.2, r.1.1] 1 - (rules R b).tail r)) = 0
  rw [toU_ctxL, tail_eq, ← sub_sub, toU_rel, mul_zero, zero_mul]

/-- **The quotient of the free module on the words by the ideal of the rules.** -/
abbrev Q := (List I →₀ R) ⧸ (sys R b).ideal

/-- **The quotient to the enveloping algebra.** -/
noncomputable def toQU : Q R b →ₗ[R] UniversalEnvelopingAlgebra R g :=
  (sys R b).ideal.liftQ (toU R b) (ideal_le_ker R b)

lemma toQU_mk (x : List I →₀ R) : toQU R b (Submodule.Quotient.mk x) = toU R b x := rfl

/-- **Left multiplication by a letter** on the quotient. -/
noncomputable def lmul (a : I) : Module.End R (Q R b) :=
  (sys R b).ideal.mapQ (sys R b).ideal (ctxL R [a] [])
    fun _ hx => Rules.mapDomain_mem_ideal (rules R b) ⟨[a], [], fun _ => rfl⟩ hx

lemma lmul_mk (a : I) (x : List I →₀ R) :
    lmul R b a (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ctxL R [a] [] x) := rfl

/-- **The action of the Lie algebra** on the quotient, as a linear map. -/
noncomputable def ρ₀ : g →ₗ[R] Module.End R (Q R b) := b.constr R (lmul R b)

lemma ρ₀_basis (a : I) : ρ₀ R b (b a) = lmul R b a := b.constr_basis R _ a

lemma ρ₀_mk (y : g) (w : List I) :
    ρ₀ R b y (Submodule.Quotient.mk (single w 1)) =
      Submodule.Quotient.mk (ctxL R [] w (lin R b y)) := by
  have : LinearMap.applyₗ (Submodule.Quotient.mk (single w 1) : Q R b) ∘ₗ ρ₀ R b =
      (sys R b).ideal.mkQ ∘ₗ ctxL R [] w ∘ₗ lin R b := b.ext fun a => by
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.applyₗ_apply_apply,
      ρ₀_basis, lmul_mk, ctxL_single, lin_basis, Submodule.mkQ_apply, List.nil_append,
      List.append_nil, List.singleton_append]
  exact LinearMap.congr_fun this y

lemma ρ₀_lie (x y : g) : ρ₀ R b ⁅x, y⁆ = ρ₀ R b x * ρ₀ R b y - ρ₀ R b y * ρ₀ R b x := by
  let B₁ : g →ₗ[R] g →ₗ[R] Module.End R (Q R b) :=
    (LieModule.toEnd R g g : g →ₗ[R] Module.End R g).compr₂ (ρ₀ R b)
  let B₂ : g →ₗ[R] g →ₗ[R] Module.End R (Q R b) :=
    LinearMap.mk₂ R (fun x y => ρ₀ R b x * ρ₀ R b y - ρ₀ R b y * ρ₀ R b x)
      (fun x x' y => by simp only [map_add, add_mul, mul_add]; abel)
      (fun c x y => by simp only [map_smul, smul_mul_assoc, mul_smul_comm, smul_sub])
      (fun x y y' => by simp only [map_add, add_mul, mul_add]; abel)
      (fun c x y => by simp only [map_smul, smul_mul_assoc, mul_smul_comm, smul_sub])
  have h : B₁ = B₂ := LinearMap.ext_basis b b fun c a => by
    simp only [B₁, B₂, LinearMap.compr₂_apply, LinearMap.mk₂_apply, LieHom.coe_toLinearMap,
      LieModule.toEnd_apply_apply, ρ₀_basis]
    refine Submodule.linearMap_qext _ (lhom_ext fun w r => ?_)
    have key : ρ₀ R b ⁅b c, b a⁆ (Submodule.Quotient.mk (single w 1)) =
        (lmul R b c * lmul R b a - lmul R b a * lmul R b c)
          (Submodule.Quotient.mk (single w 1)) := by
      rw [ρ₀_mk, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, lmul_mk,
        lmul_mk, lmul_mk, lmul_mk]
      simp only [ctxL_single]
      rw [← Submodule.Quotient.mk_sub, Submodule.Quotient.eq]
      have hm := Rules.mapDomain_mem_ideal (rules R b) (a := ()) (b := ())
        (g := fun v => [] ++ v ++ w)
        ⟨[], w, fun _ => rfl⟩ (swap_mem R b (s := Set.univ) (fun _ _ => trivial) c a)
      have e : ctxL R [] w (lin R b ⁅b c, b a⁆) -
          (single ([c] ++ ([a] ++ w ++ []) ++ []) 1 - single ([a] ++ ([c] ++ w ++ []) ++ []) 1) =
          -mapDomain (fun v => [] ++ v ++ w)
            (single [c, a] 1 - single [a, c] 1 - lin R b ⁅b c, b a⁆) := by
        rw [mapDomain_sub, mapDomain_sub, mapDomain_single, mapDomain_single, ctxL_apply]
        simp only [List.nil_append, List.append_nil, List.cons_append]
        abel
      rw [e]
      exact neg_mem hm
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [← smul_single_one, Submodule.Quotient.mk_smul, map_smul, map_smul, key]
  have := LinearMap.congr_fun₂ h x y
  simpa only [B₁, B₂, LinearMap.compr₂_apply, LinearMap.mk₂_apply, LieHom.coe_toLinearMap,
    LieModule.toEnd_apply_apply] using this

/-- **The action of the Lie algebra on the quotient** by left multiplication. -/
noncomputable def ρ : g →ₗ⁅R⁆ Module.End R (Q R b) :=
  { ρ₀ R b with
    map_lie' := fun {x y} => by
      rw [LieRing.of_associative_ring_bracket]
      exact ρ₀_lie R b x y }

lemma ρ_basis (a : I) : ρ R b (b a) = lmul R b a := ρ₀_basis R b a

/-- **The action of the enveloping algebra on the class of the empty word.** -/
noncomputable def ψ : UniversalEnvelopingAlgebra R g →ₗ[R] Q R b :=
  LinearMap.applyₗ (Submodule.Quotient.mk (single [] 1) : Q R b) ∘ₗ
    (lift R (ρ R b)).toLinearMap

lemma ψ_prodι : ∀ w : List I, ψ R b (prodι R b w) = Submodule.Quotient.mk (single w 1)
  | [] => by simp [ψ, prodι]
  | a :: w => by
    have := ψ_prodι w
    simp only [ψ, LinearMap.coe_comp, Function.comp_apply, LinearMap.applyₗ_apply_apply,
      AlgHom.toLinearMap_apply] at this ⊢
    rw [prodι_cons, map_mul, Module.End.mul_apply, this, lift_ι_apply, ρ_basis, lmul_mk,
      ctxL_single, List.append_nil]
    rfl

/-- **The action on the empty word is a left inverse.** -/
theorem ψ_toQU (q : Q R b) : ψ R b (toQU R b q) = q := by
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
  rw [toQU_mk]
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, Submodule.Quotient.mk_add]
  | single w c => rw [toU_single, map_smul, ψ_prodι, ← Submodule.Quotient.mk_smul, smul_single_one]

theorem toQU_injective : Function.Injective (toQU R b) :=
  Function.LeftInverse.injective (ψ_toQU R b)

theorem toQU_surjective : Function.Surjective (toQU R b) := fun u => by
  obtain ⟨x, rfl⟩ := toU_surjective R b u
  exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- **The enveloping algebra is the quotient of the free module on the words by the ideal of the
rules.** -/
noncomputable def quotEquiv : Q R b ≃ₗ[R] UniversalEnvelopingAlgebra R g :=
  LinearEquiv.ofBijective (toQU R b) ⟨toQU_injective R b, toQU_surjective R b⟩

/-! ## The theorem -/

/-- **The Poincaré–Birkhoff–Witt theorem**: the products of the basis vectors along the
nondecreasing words are a basis of the universal enveloping algebra. -/
noncomputable def basis :
    Module.Basis {w : List I // w.IsChain (· ≤ ·)} R (UniversalEnvelopingAlgebra R g) :=
  ((resolvable R b).basis.map (quotEquiv R b)).reindex
    (Equiv.subtypeEquivRight fun w => ((rules R b).mem_irr_iff).trans (normal_iff_isChain R b w))

theorem basis_apply (w : {w : List I // w.IsChain (· ≤ ·)}) : basis R b w = prodι R b w.1 := by
  rw [basis, Module.Basis.reindex_apply, Module.Basis.map_apply, Rewriting.Resolvable.basis_apply,
    quotEquiv, LinearEquiv.ofBijective_apply, toQU_mk, toU_single, one_smul]
  rfl

include b in
/-- **The canonical map of a Lie algebra with a basis to its enveloping algebra is injective.** -/
theorem ι_injective_of_basis : Function.Injective (ι R : g → UniversalEnvelopingAlgebra R g) := by
  intro x y hxy
  rw [← sub_eq_zero]
  have hx : ι R (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  generalize x - y = z at hx ⊢
  have h0 : toQU R b (Submodule.Quotient.mk (lin R b z)) = 0 := by
    rw [toQU_mk, toU_lin]
    exact hx
  have hmem : lin R b z ∈ (sys R b).ideal :=
    (Submodule.Quotient.mk_eq_zero _).1 (toQU_injective R b (h0.trans (map_zero _).symm))
  have hsupp : lin R b z ∈ supported R R (sys R b).Irr := by
    rw [lin_apply, mem_supported]
    intro w hw
    classical
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 (mapDomain_support hw)
    exact (rules R b).mem_irr_iff.2 ((normal_iff_isChain R b _).2 (List.IsChain.singleton a))
  have hl : lin R b z = 0 :=
    Submodule.disjoint_def.1 (resolvable R b).disjoint _ hsupp hmem
  rw [lin_apply] at hl
  have := mapDomain_injective (fun a a' h => List.singleton_injective h)
    (hl.trans mapDomain_zero.symm)
  exact b.repr.injective (this.trans (map_zero _).symm)

end PBW

/-- **The canonical map of a Lie algebra which is free as a module to its enveloping algebra is
injective.** -/
theorem UniversalEnvelopingAlgebra.ι_injective_of_free (R : Type*) [CommRing R] (g : Type*)
    [LieRing g] [LieAlgebra R g] [Module.Free R g] :
    Function.Injective (UniversalEnvelopingAlgebra.ι R : g → UniversalEnvelopingAlgebra R g) := by
  classical
  let b := Module.Free.chooseBasis R g
  letI : LinearOrder (Module.Free.ChooseBasisIndex R g) := linearOrderOfSTO WellOrderingRel
  haveI : WellFoundedLT (Module.Free.ChooseBasisIndex R g) := ⟨WellOrderingRel.isWellOrder.wf⟩
  exact PBW.ι_injective_of_basis R b

end Operad
