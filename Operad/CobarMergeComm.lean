/-
# The cobar differential and the merge

For the cobar construction `ΩC` of the cut cooperad `C = FreeGrL R V`, with its differential `d`
and the merge-composition `⊛` of the merge structure on its generators (`Cobar.mM`), the
commutator `d (x ⊛ⱼ y) + d x ⊛ⱼ y + (-1)^{|x|} x ⊛ⱼ d y` of the generators `x = ι a`, `y = ι b` of
two trees is their composite `x ∘ⱼ y` (`Cobar.d_mM_ιL_bas`): the cuts of the composite tree
`a ∘ⱼ b` at the vertices of `a` are the merges of the cuts of `a` into `b`
(`Cobar.mM_starI_ιL`), those at the vertices of `b` other than its root the merges of `a` into the
cuts of `b` (`Cobar.mM_ιL_starI`), and the cut at the root of `b` gives back `a` and `b`.
-/
import Operad.BarCobarRes

universe u v

namespace Operad

open Sym GerBV TreeOfArity FreeGr
open scoped TensorProduct

namespace FreeGr

variable {T : ℕ → Type v} (gp : ∀ k, T k → Bool)
  {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype D]
  [DecidableEq D]

/-- **The sign cocycle of composites of labelled trees, sequentially.** -/
lemma cSgn_seq (i : A) (j : B) (x : Reg (TreeOfArity T) A) (y : Reg (TreeOfArity T) B)
    (z : Reg (TreeOfArity T) D) :
    xor (cSgn gp i x y) (cSgn gp (Sum.inr j) (SetOperad.comp i x y) z)
      = xor (cSgn gp j y z) (cSgn gp i x (SetOperad.comp j y z)) := by
  have h := SgnData.sgn_seq i j ((treeSgn gp).app A x) ((treeSgn gp).app B y)
    ((treeSgn gp).app D z)
  have e1 := (treeSgn gp).app_comp i x y
  have e2 := (treeSgn gp).app_comp j y z
  show xor (SgnData.sgn i ((treeSgn gp).app A x) ((treeSgn gp).app B y))
      (SgnData.sgn (Sum.inr j) ((treeSgn gp).app _ (SetOperad.comp i x y)) ((treeSgn gp).app D z))
    = xor (SgnData.sgn j ((treeSgn gp).app B y) ((treeSgn gp).app D z))
      (SgnData.sgn i ((treeSgn gp).app A x) ((treeSgn gp).app _ (SetOperad.comp j y z)))
  rw [e1, e2]
  exact h

/-- **The sign cocycle of composites of labelled trees, in parallel.** -/
lemma cSgn_par {i k : A} (hik : i ≠ k) (x : Reg (TreeOfArity T) A) (y : Reg (TreeOfArity T) B)
    (z : Reg (TreeOfArity T) D) :
    xor (cSgn gp i x y) (cSgn gp (Sum.inl ⟨k, Ne.symm hik⟩) (SetOperad.comp i x y) z)
      = xor (Tree.tpar gp (treeOf y) && Tree.tpar gp (treeOf z))
          (xor (cSgn gp k x z) (cSgn gp (Sum.inl ⟨i, hik⟩) (SetOperad.comp k x z) y)) := by
  have h := SgnData.sgn_par hik ((treeSgn gp).app A x) ((treeSgn gp).app B y)
    ((treeSgn gp).app D z)
  have e1 := (treeSgn gp).app_comp i x y
  have e2 := (treeSgn gp).app_comp k x z
  show xor (SgnData.sgn i ((treeSgn gp).app A x) ((treeSgn gp).app B y))
      (SgnData.sgn (Sum.inl ⟨k, Ne.symm hik⟩) ((treeSgn gp).app _ (SetOperad.comp i x y))
        ((treeSgn gp).app D z))
    = xor (((treeSgn gp).app B y).tot && ((treeSgn gp).app D z).tot)
      (xor (SgnData.sgn k ((treeSgn gp).app A x) ((treeSgn gp).app D z))
        (SgnData.sgn (Sum.inl ⟨i, hik⟩) ((treeSgn gp).app _ (SetOperad.comp k x z))
          ((treeSgn gp).app B y)))
  rw [e1, e2]
  exact h

/-- The sign of a composite only depends on the relabelled outer tree through the slot. -/
lemma cSgn_map_left {A' : Type} [Fintype A'] [DecidableEq A'] (e : A ≃ A') (i : A)
    (x : Reg (TreeOfArity T) A) (y : Reg (TreeOfArity T) B) :
    cSgn gp (e i) (SetOperad.map e x) y = cSgn gp i x y := by
  simp only [cSgn, treeOf_map, map_fst, LinOrd.rank_map, Equiv.symm_apply_apply]

/-- The sign of a composite does not see relabellings of the inner tree. -/
lemma cSgn_map_right {B' : Type} [Fintype B'] [DecidableEq B'] (e : B ≃ B') (i : A)
    (x : Reg (TreeOfArity T) A) (y : Reg (TreeOfArity T) B) :
    cSgn gp i x (SetOperad.map e y) = cSgn gp i x y := rfl

/-- The parity of a composite of labelled trees. -/
lemma tpar_comp (i : A) (x : Reg (TreeOfArity T) A) (y : Reg (TreeOfArity T) B) :
    Tree.tpar gp (treeOf (SetOperad.comp i x y))
      = xor (Tree.tpar gp (treeOf x)) (Tree.tpar gp (treeOf y)) := by
  rw [treeOf_comp]
  exact Tree.tpar_graft gp _ _ _ (rank_lt_arity x i)

end FreeGr

section Helpers

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C]
  [DecidableEq C]

lemma map_smul_map_smul (S : A ≃ B) (T : B ≃ C) (s k : R) (w : P A) :
    GrOperad.map (R := R) T (s • GrOperad.map (R := R) S (k • w))
      = (s * k) • GrOperad.map (R := R) T (GrOperad.map (R := R) S w) := by
  rw [map_smul, map_smul, map_smul, smul_smul]

lemma map_trans_smul (S : A ≃ B) (T : B ≃ C) (s : R) (w : P A) :
    GrOperad.map (R := R) (S.trans T) (s • w)
      = s • GrOperad.map (R := R) T (GrOperad.map (R := R) S w) := by
  rw [GrOperad.map_trans, map_smul, map_smul]

lemma map_smul_map_comp_left {D E : Type} [Fintype D] [DecidableEq D] [Fintype E]
    [DecidableEq E] (i : A) (S : Without A i ⊕ B ≃ D) (T : D ≃ E) (s a k : R) (x : P A)
    (y : P B) :
    GrOperad.map (R := R) T (s • GrOperad.map (R := R) S (a • GrOperad.comp (R := R) i (k • x) y))
      = (s * (a * k)) • GrOperad.map (R := R) T
          (GrOperad.map (R := R) S (GrOperad.comp (R := R) i x y)) := by
  simp only [map_smul, LinearMap.smul_apply, smul_smul]

lemma map_smul_map_comp_both {D E : Type} [Fintype D] [DecidableEq D] [Fintype E]
    [DecidableEq E] (i : A) (S : Without A i ⊕ B ≃ D) (T : D ≃ E) (s a k : R) (x : P A)
    (y : P B) :
    GrOperad.map (R := R) T (s • GrOperad.map (R := R) S (GrOperad.comp (R := R) i (a • x) (k • y)))
      = (s * (a * k)) • GrOperad.map (R := R) T
          (GrOperad.map (R := R) S (GrOperad.comp (R := R) i x y)) := by
  simp only [map_smul, LinearMap.smul_apply, smul_smul]
  congr 1
  ring

end Helpers

section Sums

variable {R : Type u} [CommRing R] {M N Q : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q]

lemma bilin_neg_sum_left (f : M →ₗ[R] N →ₗ[R] Q) (S : Finset ℕ) (x : ℕ → M) (y : N) :
    f (-∑ k ∈ S, x k) y = -∑ k ∈ S, f (x k) y := by
  rw [map_neg, LinearMap.neg_apply, map_sum, LinearMap.coe_sum, Finset.sum_apply]

lemma bilin_neg_sum_right (f : M →ₗ[R] N →ₗ[R] Q) (x : M) (S : Finset ℕ) (y : ℕ → N) :
    f x (-∑ k ∈ S, y k) = -∑ k ∈ S, f x (y k) := by
  rw [map_neg, map_sum]

lemma neg_sum_neg_smul (S : Finset ℕ) (g : ℕ → M) (s : R) :
    -∑ k ∈ S, (-s) • g k = s • ∑ k ∈ S, g k := by
  rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [neg_smul, neg_neg]

/-- The cancellation of the cuts of a composite tree against the merges of the cuts of its
factors. -/
lemma combine_cuts {n m v : ℕ} (hv1 : 1 ≤ v) (hv : v ≤ n) (hm : 1 ≤ m) (F : ℕ → M) (s t : R)
    (hst : s * t = -1) (c : M) (hF : F v = t • c) :
    s • -(∑ k ∈ Finset.Ico 1 (n + m), F k)
      + s • ∑ k ∈ Finset.Ico 1 n, F (k + if v ≤ k then m else 0)
      + s • ∑ k ∈ Finset.Ico 1 m, F (v + k) = c := by
  rw [sum_Ico_graft F hv1 hv hm, hF, smul_neg, smul_add, smul_add, smul_smul, hst, neg_one_smul]
  abel

end Sums


section Generators

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {A B D X : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype D]
  [DecidableEq D] [Fintype X] [DecidableEq X]

local notation "𝒞" => FreeGrL R V
local notation "𝒥" => GrOperadIdeal.span R (grLinRel R V)
local notation "𝔟" => SgnLin.bas (treeSgn (grGenPar R V)) R

namespace Cobar

lemma ιL_map' (e : A ≃ B) (x : 𝒞 A) :
    Cobar.ιL R 𝒞 B (GrOperad.map (R := R) e x) = GrOperad.map (R := R) e (Cobar.ιL R 𝒞 A x) := by
  obtain ⟨y, rfl⟩ := (𝒥).proj_surjective A x
  have h1 : Cobar.ιL R 𝒞 B (GrOperad.map (R := R) e ((𝒥).proj A y))
      = Cobar.ιL R 𝒞 B ((𝒥).proj B (GrOperad.map (R := R) e y)) :=
    congrArg (Cobar.ιL R 𝒞 B) (MergeSp.proj_map'' (R := R) (W := V) e y).symm
  have h2 : Cobar.ιL R 𝒞 B ((𝒥).proj B (GrOperad.map (R := R) e y))
      = GrOperad.map (R := R) e (Cobar.ιL R 𝒞 A ((𝒥).proj A y)) :=
    (ιL_proj_map (R := R) (V := V) e y).symm
  exact h1.trans h2

/-- **Merging two generators** composes them in the cut cooperad, on the parts without unit
component: `ι x ⊛ᵢ ι y = (-1)^{|ι x|} ι (x ∘ᵢ y)`. -/
lemma mM_ιL {c : 𝒞 A} {pa : Bool} (hc : GrOperad.par (R := R) pa c = c) (i : A) (c' : 𝒞 B) :
    mM R V i (Cobar.ιL R 𝒞 A c) (Cobar.ιL R 𝒞 B c')
      = σ R (!pa) • Cobar.ιL R 𝒞 _ (GrOperad.comp (R := R) i (FreeGrL.secC R V A c)
          (FreeGrL.secC R V B c')) := by
  obtain ⟨i₀, rfl⟩ := (Fintype.equivFin A).symm.surjective i
  have hcA : GrOperad.map (R := R) (Fintype.equivFin A).symm
      (GrOperad.map (R := R) (Fintype.equivFin A) c) = c := map_symm_map _ c
  have hcB : GrOperad.map (R := R) (Fintype.equivFin B).symm
      (GrOperad.map (R := R) (Fintype.equivFin B) c') = c' := map_symm_map _ c'
  have hc₀ : GrOperad.par (R := R) pa (GrOperad.map (R := R) (Fintype.equivFin A) c)
      = GrOperad.map (R := R) (Fintype.equivFin A) c := by
    rw [← GrOperad.map_par, hc]
  have l1 : GrOperad.map (R := R) (Fintype.equivFin A).symm
      (Cobar.ιL R 𝒞 _ (GrOperad.map (R := R) (Fintype.equivFin A) c)) = Cobar.ιL R 𝒞 A c :=
    (ιL_map' _ _).symm.trans (congrArg (Cobar.ιL R 𝒞 A) hcA)
  have l2 : GrOperad.map (R := R) (Fintype.equivFin B).symm
      (Cobar.ιL R 𝒞 _ (GrOperad.map (R := R) (Fintype.equivFin B) c')) = Cobar.ιL R 𝒞 B c' :=
    (ιL_map' _ _).symm.trans (congrArg (Cobar.ιL R 𝒞 B) hcB)
  have hi := (cobarMerge R V).mc_map (Fintype.equivFin A).symm (Fintype.equivFin B).symm i₀
    (Cobar.ιL R 𝒞 _ (GrOperad.map (R := R) (Fintype.equivFin A) c))
    (Cobar.ιL R 𝒞 _ (GrOperad.map (R := R) (Fintype.equivFin B) c'))
  have h3 := mM_ιL_fin hc₀ i₀ (GrOperad.map (R := R) (Fintype.equivFin B) c')
  have l4 : GrOperad.map (R := R)
      (compEquiv (Fintype.equivFin A).symm (Fintype.equivFin B).symm i₀)
      (GrOperad.comp (R := R) i₀
        (FreeGrL.secC R V _ (GrOperad.map (R := R) (Fintype.equivFin A) c))
        (FreeGrL.secC R V _ (GrOperad.map (R := R) (Fintype.equivFin B) c')))
      = GrOperad.comp (R := R) ((Fintype.equivFin A).symm i₀) (FreeGrL.secC R V A c)
          (FreeGrL.secC R V B c') := by
    rw [GrOperad.map_comp, ← FreeGrL.secC_map, ← FreeGrL.secC_map, hcA, hcB]
  refine (congrArg₂ (fun X Y => mM R V ((Fintype.equivFin A).symm i₀) X Y) l1.symm l2.symm).trans
    (hi.trans ((congrArg _ h3).trans ((map_smul _ _ _).trans ?_)))
  exact congrArg (fun z => σ R (!pa) • z) ((ιL_map' _ _).symm.trans (congrArg (Cobar.ιL R 𝒞 _) l4))

/-- The sign of merging a generator into a factorization. -/
lemma sgn_inner (x y c₀ c₁ c₂ c₃ : Bool) (h : xor c₁ c₃ = xor c₂ c₀) :
    σ R c₂ * σ R y * (σ R (!x) * σ R c₁) = -σ R c₀ * (σ R c₃ * σ R (xor x y)) := by
  cases x <;> cases y <;> cases c₀ <;> cases c₁ <;> cases c₂ <;> cases c₃ <;> simp at h ⊢

/-- The relabelling of the factorization of a composite at a factorization of its inner tree. -/
abbrev seqRel (j : A) {A₂ B₂ : Type} [DecidableEq A₂]
    (r₂ : A₂) (e₂ : Without A₂ r₂ ⊕ B₂ ≃ B) :
    Without (Without A j ⊕ A₂) (Sum.inr r₂) ⊕ B₂ ≃ Without A j ⊕ B :=
  (seqEquiv j r₂ B₂).trans (compEquiv (Equiv.refl A) e₂ j)

lemma map_seqRel (j : A) {A₂ B₂ : Type} [Fintype A₂] [DecidableEq A₂] [Fintype B₂]
    [DecidableEq B₂] (t₁ : Reg (TreeOfArity (GrGen R V)) A) (r₂ : A₂)
    (p₂ : Reg (TreeOfArity (GrGen R V)) A₂) (q₂ : Reg (TreeOfArity (GrGen R V)) B₂)
    (e₂ : Without A₂ r₂ ⊕ B₂ ≃ B) :
    SetOperad.map (seqRel j r₂ e₂) (SetOperad.comp (Sum.inr r₂) (SetOperad.comp j t₁ p₂) q₂)
      = SetOperad.comp j t₁ (SetOperad.map e₂ (SetOperad.comp r₂ p₂ q₂)) := by
  rw [seqRel, SetOperad.map_trans, SetOperad.comp_assoc_seq]
  refine (SetOperad.map_comp (Equiv.refl A) e₂ j t₁ (SetOperad.comp r₂ p₂ q₂)).trans ?_
  rw [SetOperad.map_refl]
  rfl

/-- **Merging a generator into a factorization of a tree** factors the composite tree. -/
lemma mM_ιL_repI {A₂ B₂ : Type} [Fintype A₂] [DecidableEq A₂] [Fintype B₂] [DecidableEq B₂]
    (j : A) (t₁ : Reg (TreeOfArity (GrGen R V)) A) (r₂ : A₂)
    (p₂ : Reg (TreeOfArity (GrGen R V)) A₂) (q₂ : Reg (TreeOfArity (GrGen R V)) B₂)
    (e₂ : Without A₂ r₂ ⊕ B₂ ≃ B) (h₁ : (treeOf t₁).isLeaf = false)
    (hp : (treeOf p₂).isLeaf = false) :
    mM R V j (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t₁))) (repI R V e₂ p₂ q₂)
      = -σ R (cSgn (grGenPar R V) j t₁ (SetOperad.comp r₂ p₂ q₂)) •
          repI R V (seqRel j r₂ e₂) (SetOperad.comp j t₁ p₂) q₂ := by
  have hpa : GrOperad.par (R := R) (Tree.tpar (grGenPar R V) (treeOf t₁)) ((𝒥).proj A (𝔟 t₁))
      = (𝒥).proj A (𝔟 t₁) := congrArg ((𝒥).proj A) (SgnLin.par_bas t₁)
  have e5 : GrOperad.comp (R := R) j (FreeGrL.secC R V A ((𝒥).proj A (𝔟 t₁)))
      (FreeGrL.secC R V A₂ ((𝒥).proj A₂ (𝔟 p₂)))
      = σ R (cSgn (grGenPar R V) j t₁ p₂) • (𝒥).proj _ (𝔟 (SetOperad.comp j t₁ p₂)) := by
    rw [FreeGrL.secC_of_unitCoeff (unitCoeffL_bas h₁),
      FreeGrL.secC_of_unitCoeff (unitCoeffL_bas hp)]
    show (𝒥).proj _ (GrOperad.comp (R := R) j _ _) = _
    rw [comp_bas_eq, map_smul]
  have m1 : mM R V j (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t₁))) (Cobar.ιL R 𝒞 A₂ ((𝒥).proj A₂ (𝔟 p₂)))
      = (σ R (!(Tree.tpar (grGenPar R V) (treeOf t₁))) * σ R (cSgn (grGenPar R V) j t₁ p₂)) •
          Cobar.ιL R 𝒞 _ ((𝒥).proj _ (𝔟 (SetOperad.comp j t₁ p₂))) := by
    rw [mM_ιL hpa, e5, map_smul, smul_smul]
  have m2 := (cobarMerge R V).comp_mc_outer j r₂ (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t₁)))
    (unitCoeffL_ιL ((𝒥).proj A₂ (𝔟 p₂))) (Cobar.ιL R 𝒞 B₂ ((𝒥).proj B₂ (𝔟 q₂)))
  have m3 := (cobarMerge R V).mc_map_right e₂ j (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t₁)))
    ((σ R (cSgn (grGenPar R V) r₂ p₂ q₂) * σ R (Tree.tpar (grGenPar R V) (treeOf p₂))) •
      GrOperad.comp (R := R) r₂ (Cobar.ιL R 𝒞 A₂ ((𝒥).proj A₂ (𝔟 p₂)))
        (Cobar.ιL R 𝒞 B₂ ((𝒥).proj B₂ (𝔟 q₂))))
  have l1 : mM R V j (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t₁))) (repI R V e₂ p₂ q₂)
      = GrOperad.map (R := R) (compEquiv (Equiv.refl A) e₂ j)
          ((σ R (cSgn (grGenPar R V) r₂ p₂ q₂) * σ R (Tree.tpar (grGenPar R V) (treeOf p₂))) •
            GrOperad.map (R := R) (seqEquiv j r₂ B₂)
              (GrOperad.comp (R := R) (Sum.inr r₂)
                (mM R V j (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t₁)))
                  (Cobar.ιL R 𝒞 A₂ ((𝒥).proj A₂ (𝔟 p₂))))
                (Cobar.ιL R 𝒞 B₂ ((𝒥).proj B₂ (𝔟 q₂))))) :=
    m3.trans (congrArg (GrOperad.map (R := R) (compEquiv (Equiv.refl A) e₂ j))
      ((map_smul _ _ _).trans (congrArg _ m2.symm)))
  have l2 := congrArg (fun z => GrOperad.map (R := R) (compEquiv (Equiv.refl A) e₂ j)
      ((σ R (cSgn (grGenPar R V) r₂ p₂ q₂) * σ R (Tree.tpar (grGenPar R V) (treeOf p₂))) •
        GrOperad.map (R := R) (seqEquiv j r₂ B₂) (GrOperad.comp (R := R) (Sum.inr r₂) z
          (Cobar.ιL R 𝒞 B₂ ((𝒥).proj B₂ (𝔟 q₂)))))) m1
  refine l1.trans (l2.trans ?_)
  have l3 := LinearMap.map_smul₂ (GrOperad.comp (R := R) (P := CobarGr R 𝒞) (Sum.inr r₂))
    (σ R (!(Tree.tpar (grGenPar R V) (treeOf t₁))) * σ R (cSgn (grGenPar R V) j t₁ p₂))
    (Cobar.ιL R 𝒞 _ ((𝒥).proj _ (𝔟 (SetOperad.comp j t₁ p₂))))
    (Cobar.ιL R 𝒞 B₂ ((𝒥).proj B₂ (𝔟 q₂)))
  refine (congrArg (fun z => GrOperad.map (R := R) (compEquiv (Equiv.refl A) e₂ j)
    ((σ R (cSgn (grGenPar R V) r₂ p₂ q₂) * σ R (Tree.tpar (grGenPar R V) (treeOf p₂))) •
      GrOperad.map (R := R) (seqEquiv j r₂ B₂) z)) l3).trans ?_
  refine (map_smul_map_smul _ _ _ _ _).trans ?_
  unfold repI
  refine Eq.trans ?_ (congrArg (fun z => -σ R (cSgn (grGenPar R V) j t₁ (SetOperad.comp r₂ p₂ q₂))
    • z) (map_trans_smul (seqEquiv j r₂ B₂) (compEquiv (Equiv.refl A) e₂ j) _ _).symm)
  refine Eq.trans ?_ (smul_smul _ _ _).symm
  congr 1
  rw [tpar_comp]
  exact sgn_inner _ _ _ _ _ _ (cSgn_seq (grGenPar R V) j r₂ t₁ p₂ q₂)

/-- **Merging a generator into the cut of a tree at a vertex** cuts the composite tree at that
vertex, with the sign of the composite. -/
theorem mM_ιL_starI (j : A) (t₁ : Reg (TreeOfArity (GrGen R V)) A)
    (t₂ : Reg (TreeOfArity (GrGen R V)) B) (h₁ : (treeOf t₁).isLeaf = false) {k : ℕ}
    (hk : k ∈ Finset.Ico 1 (treeOf t₂).weight) :
    mM R V j (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t₁))) (starI R V t₂ k)
      = -σ R (cSgn (grGenPar R V) j t₁ t₂) •
          starI R V (SetOperad.comp j t₁ t₂) (vert j t₁ + k) := by
  rw [Finset.mem_Ico] at hk
  obtain ⟨e, he⟩ := exists_rep t₂ hk.2
  have hq := Tree.isLeaf_cutV _ _ hk.2
  have hst := starI_eq (R := R) (V := V) he hq
  have hvert : vert ⟨((treeOf t₂).cutV k).2.2, Tree.lt_arity_cutV _ k hk.2⟩
      (stdT ((treeOf t₂).cutV k).1) = k := by
    show (treeOf (stdT _)).vb ((stdT _).1.rank _) = k
    rw [treeOf_stdT, rank_stdT]
    exact Tree.vb_cutV _ _ hk.2
  rw [hvert] at hst
  have hrep := map_seqRel j t₁ ⟨((treeOf t₂).cutV k).2.2, Tree.lt_arity_cutV _ k hk.2⟩
    (stdT ((treeOf t₂).cutV k).1) (stdT ((treeOf t₂).cutV k).2.1) e
  rw [he] at hrep
  have hst2 := starI_eq (R := R) (V := V) hrep hq
  rw [vert_comp_inr, hvert] at hst2
  have hc : cSgn (grGenPar R V) j t₁ t₂ = cSgn (grGenPar R V) j t₁
      (SetOperad.comp (⟨((treeOf t₂).cutV k).2.2, Tree.lt_arity_cutV _ k hk.2⟩ :
        Fin ((treeOf t₂).cutV k).1.arity)
        (stdT ((treeOf t₂).cutV k).1) (stdT ((treeOf t₂).cutV k).2.1)) :=
    (congrArg (cSgn (grGenPar R V) j t₁) he).symm
  refine (congrArg (mM R V j (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t₁)))) hst).trans
    ((mM_ιL_repI j t₁ _ _ _ e h₁ (Tree.isLeaf_cutV_fst hk.1 hk.2 rfl)).trans ?_)
  rw [hst2, hc]

/-- The sign of merging a factorization into a generator, above the cut. -/
lemma sgn_outer_inr (x y c₀ c₁ c₂ c₃ : Bool) (h : xor c₁ c₀ = xor c₂ c₃) :
    σ R c₁ * σ R x * (σ R (true && !x) * (σ R (!y) * σ R c₂))
      = -(σ R (!(xor x y)) * σ R c₀) * (σ R c₃ * σ R x) := by
  cases x <;> cases y <;> cases c₀ <;> cases c₁ <;> cases c₂ <;> cases c₃ <;> simp at h ⊢

/-- The sign of merging a factorization into a generator, beside the cut. -/
lemma sgn_outer_inl (x y z c₀ c₁ c₂ c₃ : Bool) (h : xor c₁ c₀ = xor (y && z) (xor c₂ c₃)) :
    σ R c₁ * σ R x * (σ R ((!y) && (!z)) * (σ R (!x) * σ R c₂))
      = -(σ R (!(xor x y)) * σ R c₀) * (σ R c₃ * σ R (xor x z)) := by
  cases x <;> cases y <;> cases z <;> cases c₀ <;> cases c₁ <;> cases c₂ <;> cases c₃ <;>
    simp at h ⊢

/-- The relabelling of the factorization of a composite at a factorization of its outer tree,
the composite being above the cut. -/
abbrev seqRel' {A₁ B₁ : Type} [DecidableEq A₁] [DecidableEq B₁]
    (r₁ : A₁) (w : B₁) (e₁ : Without A₁ r₁ ⊕ B₁ ≃ A) :
    Without A₁ r₁ ⊕ (Without B₁ w ⊕ B) ≃ Without A (e₁ (Sum.inr w)) ⊕ B :=
  (seqEquiv r₁ w B).symm.trans (compEquiv e₁ (Equiv.refl B) (Sum.inr w))

lemma map_seqRel' {A₁ B₁ : Type} [Fintype A₁] [DecidableEq A₁] [Fintype B₁] [DecidableEq B₁]
    (r₁ : A₁) (w : B₁) (e₁ : Without A₁ r₁ ⊕ B₁ ≃ A) (p₁ : Reg (TreeOfArity (GrGen R V)) A₁)
    (q₁ : Reg (TreeOfArity (GrGen R V)) B₁) (t₂ : Reg (TreeOfArity (GrGen R V)) B) :
    SetOperad.map (seqRel' (B := B) r₁ w e₁) (SetOperad.comp r₁ p₁ (SetOperad.comp w q₁ t₂))
      = SetOperad.comp (e₁ (Sum.inr w)) (SetOperad.map e₁ (SetOperad.comp r₁ p₁ q₁)) t₂ := by
  rw [seqRel', SetOperad.map_trans, ← SetOperad.comp_assoc_seq, SetOperad.map_symm_map]
  refine (SetOperad.map_comp e₁ (Equiv.refl B) (Sum.inr w) _ t₂).trans ?_
  rw [SetOperad.map_refl]

/-- The relabelling of the factorization of a composite at a factorization of its outer tree,
the composite being beside the cut. -/
abbrev parRel {A₁ B₁ : Type} [DecidableEq A₁] [DecidableEq B₁]
    {r₁ u : A₁} (hu : r₁ ≠ u) (e₁ : Without A₁ r₁ ⊕ B₁ ≃ A) :
    Without (Without A₁ u ⊕ B) (Sum.inl ⟨r₁, hu⟩) ⊕ B₁
      ≃ Without A (e₁ (Sum.inl ⟨u, Ne.symm hu⟩)) ⊕ B :=
  (parEquiv hu B₁ B).symm.trans (compEquiv e₁ (Equiv.refl B) (Sum.inl ⟨u, Ne.symm hu⟩))

lemma map_parRel {A₁ B₁ : Type} [Fintype A₁] [DecidableEq A₁] [Fintype B₁] [DecidableEq B₁]
    {r₁ u : A₁} (hu : r₁ ≠ u) (e₁ : Without A₁ r₁ ⊕ B₁ ≃ A)
    (p₁ : Reg (TreeOfArity (GrGen R V)) A₁) (q₁ : Reg (TreeOfArity (GrGen R V)) B₁)
    (t₂ : Reg (TreeOfArity (GrGen R V)) B) :
    SetOperad.map (parRel hu e₁) (SetOperad.comp (Sum.inl ⟨r₁, hu⟩) (SetOperad.comp u p₁ t₂) q₁)
      = SetOperad.comp (e₁ (Sum.inl ⟨u, Ne.symm hu⟩))
          (SetOperad.map e₁ (SetOperad.comp r₁ p₁ q₁)) t₂ := by
  rw [parRel, SetOperad.map_trans, ← SetOperad.comp_assoc_par, SetOperad.map_symm_map]
  refine (SetOperad.map_comp e₁ (Equiv.refl B) (Sum.inl ⟨u, Ne.symm hu⟩) _ t₂).trans ?_
  rw [SetOperad.map_refl]

/-- The generator of a tree is homogeneous, of the shifted parity of the tree. -/
lemma par_ιL_bas (t : Reg (TreeOfArity (GrGen R V)) A) :
    GrOperad.par (R := R) (!(Tree.tpar (grGenPar R V) (treeOf t)))
        (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t)))
      = Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t)) := by
  rw [← Cobar.ιL_par]
  exact congrArg (Cobar.ιL R 𝒞 A) (congrArg ((𝒥).proj A) (SgnLin.par_bas t))

/-- **Merging two generators of trees**: the generator of the composite tree, with the sign of the
composite and the shifted parity of the first tree. -/
lemma mM_ιL_bas (j : A) (t₁ : Reg (TreeOfArity (GrGen R V)) A)
    (t₂ : Reg (TreeOfArity (GrGen R V)) B) (h₁ : (treeOf t₁).isLeaf = false)
    (h₂ : (treeOf t₂).isLeaf = false) :
    mM R V j (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t₁))) (Cobar.ιL R 𝒞 B ((𝒥).proj B (𝔟 t₂)))
      = (σ R (!(Tree.tpar (grGenPar R V) (treeOf t₁))) * σ R (cSgn (grGenPar R V) j t₁ t₂)) •
          Cobar.ιL R 𝒞 _ ((𝒥).proj _ (𝔟 (SetOperad.comp j t₁ t₂))) := by
  have hpa : GrOperad.par (R := R) (Tree.tpar (grGenPar R V) (treeOf t₁)) ((𝒥).proj A (𝔟 t₁))
      = (𝒥).proj A (𝔟 t₁) := congrArg ((𝒥).proj A) (SgnLin.par_bas t₁)
  have e5 : GrOperad.comp (R := R) j (FreeGrL.secC R V A ((𝒥).proj A (𝔟 t₁)))
      (FreeGrL.secC R V B ((𝒥).proj B (𝔟 t₂)))
      = σ R (cSgn (grGenPar R V) j t₁ t₂) • (𝒥).proj _ (𝔟 (SetOperad.comp j t₁ t₂)) := by
    rw [FreeGrL.secC_of_unitCoeff (unitCoeffL_bas h₁),
      FreeGrL.secC_of_unitCoeff (unitCoeffL_bas h₂)]
    show (𝒥).proj _ (GrOperad.comp (R := R) j _ _) = _
    rw [comp_bas_eq, map_smul]
  rw [mM_ιL hpa, e5, map_smul, smul_smul]

/-- **Merging a factorization of a tree into a generator, above the cut**: the inner factor is
merged. -/
lemma mM_repI_ιL_inr {A₁ B₁ : Type} [Fintype A₁] [DecidableEq A₁] [Fintype B₁] [DecidableEq B₁]
    (r₁ : A₁) (p₁ : Reg (TreeOfArity (GrGen R V)) A₁) (q₁ : Reg (TreeOfArity (GrGen R V)) B₁)
    (e₁ : Without A₁ r₁ ⊕ B₁ ≃ A) (w : B₁) (t₂ : Reg (TreeOfArity (GrGen R V)) B)
    (hq : (treeOf q₁).isLeaf = false) (h₂ : (treeOf t₂).isLeaf = false) :
    mM R V (e₁ (Sum.inr w)) (repI R V e₁ p₁ q₁) (Cobar.ιL R 𝒞 B ((𝒥).proj B (𝔟 t₂)))
      = -(σ R (!(Tree.tpar (grGenPar R V) (treeOf (SetOperad.comp r₁ p₁ q₁))))
          * σ R (cSgn (grGenPar R V) (Sum.inr w) (SetOperad.comp r₁ p₁ q₁) t₂)) •
        repI R V (seqRel' (B := B) r₁ w e₁) p₁ (SetOperad.comp w q₁ t₂) := by
  have m1 := mM_ιL_bas w q₁ t₂ hq h₂
  have htw : GrOperad.tw (R := R) true (Cobar.ιL R 𝒞 A₁ ((𝒥).proj A₁ (𝔟 p₁)))
      = σ R (true && !(Tree.tpar (grGenPar R V) (treeOf p₁))) •
          Cobar.ιL R 𝒞 A₁ ((𝒥).proj A₁ (𝔟 p₁)) :=
    GrOperad.tw_hom true (par_ιL_bas p₁)
  have m2 := (cobarMerge R V).mc_comp_inner r₁ w (Cobar.ιL R 𝒞 A₁ ((𝒥).proj A₁ (𝔟 p₁)))
    (unitCoeffL_ιL ((𝒥).proj B₁ (𝔟 q₁))) (Cobar.ιL R 𝒞 B ((𝒥).proj B (𝔟 t₂)))
  have m2' := (map_symm_map (seqEquiv r₁ w B) _).symm.trans
    (congrArg (GrOperad.map (R := R) (seqEquiv r₁ w B).symm) m2)
  have m3 := (cobarMerge R V).mc_map_left e₁ (Sum.inr w)
    ((σ R (cSgn (grGenPar R V) r₁ p₁ q₁) * σ R (Tree.tpar (grGenPar R V) (treeOf p₁))) •
      GrOperad.comp (R := R) r₁ (Cobar.ιL R 𝒞 A₁ ((𝒥).proj A₁ (𝔟 p₁)))
        (Cobar.ιL R 𝒞 B₁ ((𝒥).proj B₁ (𝔟 q₁))))
    (Cobar.ιL R 𝒞 B ((𝒥).proj B (𝔟 t₂)))
  refine (m3.trans (congrArg (GrOperad.map (R := R) (compEquiv e₁ (Equiv.refl B) (Sum.inr w)))
    ((LinearMap.map_smul₂ _ _ _ _).trans (congrArg (fun z =>
      (σ R (cSgn (grGenPar R V) r₁ p₁ q₁) * σ R (Tree.tpar (grGenPar R V) (treeOf p₁))) • z)
        m2')))).trans ?_
  refine (congrArg₂ (fun x y => GrOperad.map (R := R) (compEquiv e₁ (Equiv.refl B) (Sum.inr w))
    ((σ R (cSgn (grGenPar R V) r₁ p₁ q₁) * σ R (Tree.tpar (grGenPar R V) (treeOf p₁))) •
      GrOperad.map (R := R) (seqEquiv r₁ w B).symm (GrOperad.comp (R := R) r₁ x y))) htw
        m1).trans ?_
  refine (map_smul_map_comp_both _ _ _ _ _ _ _ _).trans ?_
  unfold repI
  refine Eq.trans ?_ (congrArg (fun z => -(σ R (!(Tree.tpar (grGenPar R V)
    (treeOf (SetOperad.comp r₁ p₁ q₁)))) * σ R (cSgn (grGenPar R V) (Sum.inr w)
      (SetOperad.comp r₁ p₁ q₁) t₂)) • z) (map_trans_smul (seqEquiv r₁ w B).symm
        (compEquiv e₁ (Equiv.refl B) (Sum.inr w)) _ _).symm)
  refine Eq.trans ?_ (smul_smul _ _ _).symm
  congr 1
  rw [tpar_comp]
  exact sgn_outer_inr _ _ _ _ _ _ (cSgn_seq (grGenPar R V) r₁ w p₁ q₁ t₂)

/-- **Merging a factorization of a tree into a generator, beside the cut**: the outer factor is
merged. -/
lemma mM_repI_ιL_inl {A₁ B₁ : Type} [Fintype A₁] [DecidableEq A₁] [Fintype B₁] [DecidableEq B₁]
    {r₁ u : A₁} (hu : r₁ ≠ u) (p₁ : Reg (TreeOfArity (GrGen R V)) A₁)
    (q₁ : Reg (TreeOfArity (GrGen R V)) B₁) (e₁ : Without A₁ r₁ ⊕ B₁ ≃ A)
    (t₂ : Reg (TreeOfArity (GrGen R V)) B) (hp : (treeOf p₁).isLeaf = false)
    (h₂ : (treeOf t₂).isLeaf = false) :
    mM R V (e₁ (Sum.inl ⟨u, Ne.symm hu⟩)) (repI R V e₁ p₁ q₁)
        (Cobar.ιL R 𝒞 B ((𝒥).proj B (𝔟 t₂)))
      = -(σ R (!(Tree.tpar (grGenPar R V) (treeOf (SetOperad.comp r₁ p₁ q₁))))
          * σ R (cSgn (grGenPar R V) (Sum.inl ⟨u, Ne.symm hu⟩) (SetOperad.comp r₁ p₁ q₁) t₂)) •
        repI R V (parRel (B := B) hu e₁) (SetOperad.comp u p₁ t₂) q₁ := by
  have m1 := mM_ιL_bas u p₁ t₂ hp h₂
  have m2 := (cobarMerge R V).mc_comp_par hu (Cobar.ιL R 𝒞 A₁ ((𝒥).proj A₁ (𝔟 p₁)))
    (par_ιL_bas q₁) (par_ιL_bas t₂)
  have m2' := (map_symm_map (parEquiv hu B₁ B) _).symm.trans
    (congrArg (GrOperad.map (R := R) (parEquiv hu B₁ B).symm) m2)
  have m3 := (cobarMerge R V).mc_map_left e₁ (Sum.inl ⟨u, Ne.symm hu⟩)
    ((σ R (cSgn (grGenPar R V) r₁ p₁ q₁) * σ R (Tree.tpar (grGenPar R V) (treeOf p₁))) •
      GrOperad.comp (R := R) r₁ (Cobar.ιL R 𝒞 A₁ ((𝒥).proj A₁ (𝔟 p₁)))
        (Cobar.ιL R 𝒞 B₁ ((𝒥).proj B₁ (𝔟 q₁))))
    (Cobar.ιL R 𝒞 B ((𝒥).proj B (𝔟 t₂)))
  refine (m3.trans (congrArg (GrOperad.map (R := R)
    (compEquiv e₁ (Equiv.refl B) (Sum.inl ⟨u, Ne.symm hu⟩)))
    ((LinearMap.map_smul₂ _ _ _ _).trans (congrArg (fun z =>
      (σ R (cSgn (grGenPar R V) r₁ p₁ q₁) * σ R (Tree.tpar (grGenPar R V) (treeOf p₁))) • z)
        m2')))).trans ?_
  refine (congrArg (fun x => GrOperad.map (R := R)
    (compEquiv e₁ (Equiv.refl B) (Sum.inl ⟨u, Ne.symm hu⟩))
    ((σ R (cSgn (grGenPar R V) r₁ p₁ q₁) * σ R (Tree.tpar (grGenPar R V) (treeOf p₁))) •
      GrOperad.map (R := R) (parEquiv hu B₁ B).symm
        (σ R ((!Tree.tpar (grGenPar R V) (treeOf q₁)) && !Tree.tpar (grGenPar R V) (treeOf t₂)) •
          GrOperad.comp (R := R) (Sum.inl ⟨r₁, hu⟩) x
            (Cobar.ιL R 𝒞 B₁ ((𝒥).proj B₁ (𝔟 q₁)))))) m1).trans ?_
  refine (map_smul_map_comp_left _ _ _ _ _ _ _ _).trans ?_
  unfold repI
  refine Eq.trans ?_ (congrArg (fun z => -(σ R (!(Tree.tpar (grGenPar R V)
    (treeOf (SetOperad.comp r₁ p₁ q₁)))) * σ R (cSgn (grGenPar R V) (Sum.inl ⟨u, Ne.symm hu⟩)
      (SetOperad.comp r₁ p₁ q₁) t₂)) • z) (map_trans_smul (parEquiv hu B₁ B).symm
        (compEquiv e₁ (Equiv.refl B) (Sum.inl ⟨u, Ne.symm hu⟩)) _ _).symm)
  refine Eq.trans ?_ (smul_smul _ _ _).symm
  congr 1
  rw [tpar_comp, tpar_comp]
  exact sgn_outer_inl _ _ _ _ _ _ _ (cSgn_par (grGenPar R V) hu p₁ q₁ t₂)

/-- **Merging a factorization of a tree into a generator** cuts the composite tree. -/
lemma mM_repI_ιL {A₁ B₁ : Type} [Fintype A₁] [DecidableEq A₁] [Fintype B₁] [DecidableEq B₁]
    (r : A₁) (p : Reg (TreeOfArity (GrGen R V)) A₁) (q : Reg (TreeOfArity (GrGen R V)) B₁)
    (e : Without A₁ r ⊕ B₁ ≃ A) (hp : (treeOf p).isLeaf = false)
    (hq : (treeOf q).isLeaf = false) (j : A) (t₂ : Reg (TreeOfArity (GrGen R V)) B)
    (h₂ : (treeOf t₂).isLeaf = false) {t₁ : Reg (TreeOfArity (GrGen R V)) A}
    (he : SetOperad.map e (SetOperad.comp r p q) = t₁) {k : ℕ} (hk : vert r p = k) :
    mM R V j (repI R V e p q) (Cobar.ιL R 𝒞 B ((𝒥).proj B (𝔟 t₂)))
      = -(σ R (!(Tree.tpar (grGenPar R V) (treeOf t₁))) * σ R (cSgn (grGenPar R V) j t₁ t₂)) •
        starI R V (SetOperad.comp j t₁ t₂)
          (k + if vert j t₁ ≤ k then (treeOf t₂).weight else 0) := by
  subst he hk
  obtain ⟨j', rfl⟩ := e.surjective j
  rw [cSgn_map_left]
  rcases j' with ⟨u, hu⟩ | w
  · refine (mM_repI_ιL_inl (Ne.symm hu) p q e t₂ hp h₂).trans ?_
    have hst2 := starI_eq (R := R) (V := V) (map_parRel (B := B) (Ne.symm hu) e p q t₂) hq
    rw [vert_comp_inl] at hst2
    have hif : (if vert (e (Sum.inl ⟨u, hu⟩)) (SetOperad.map e (SetOperad.comp r p q)) ≤ vert r p
        then (treeOf t₂).weight else 0)
        = (if p.1.rank u < p.1.rank r then (treeOf t₂).weight else 0) := by
      rcases p.1.total u r hu with h | h
      · rw [if_pos (vert_le_of_inl_lt rfl hu (e.symm_apply_apply _) h),
          if_pos (p.1.rank_lt_rank h)]
      · rw [if_neg (not_le.2 (vert_lt_of_inl_gt rfl hq hu (e.symm_apply_apply _) h)),
          if_neg (not_lt.2 (p.1.rank_lt_rank h).le)]
    exact (congrArg _ ((congrArg (fun n => starI R V _ (vert r p + n)) hif).trans hst2)).symm
  · refine (mM_repI_ιL_inr r p q e w t₂ hq h₂).trans ?_
    have hq' : (treeOf (SetOperad.comp w q t₂)).isLeaf = false := by
      rw [treeOf_comp]
      exact Tree.isLeaf_graft_left hq _ _
    have hst2 := starI_eq (R := R) (V := V) (map_seqRel' (B := B) r w e p q t₂) hq'
    have hlt := vert_lt_of_inr (rfl : SetOperad.map e (SetOperad.comp r p q) = _) hq
      (j := e (Sum.inr w)) (b := w) (e.symm_apply_apply _)
    have hne : ¬ vert (e (Sum.inr w)) (SetOperad.map e (SetOperad.comp r p q)) ≤ vert r p := by
      omega
    have h3 : (vert r p + if vert (e (Sum.inr w)) (SetOperad.map e (SetOperad.comp r p q))
        ≤ vert r p then (treeOf t₂).weight else 0) = vert r p := by
      rw [if_neg hne, Nat.add_zero]
    rw [treeOf_map]
    exact (congrArg _ ((congrArg (starI R V _) h3).trans hst2)).symm

/-- **Merging the cut of a tree at a vertex into a generator** cuts the composite tree at that
vertex, shifted by the vertices of the inner tree when it comes after the graft point. -/
theorem mM_starI_ιL (j : A) (t₁ : Reg (TreeOfArity (GrGen R V)) A)
    (t₂ : Reg (TreeOfArity (GrGen R V)) B) (h₂ : (treeOf t₂).isLeaf = false) {k : ℕ}
    (hk : k ∈ Finset.Ico 1 (treeOf t₁).weight) :
    mM R V j (starI R V t₁ k) (Cobar.ιL R 𝒞 B ((𝒥).proj B (𝔟 t₂)))
      = -(σ R (!(Tree.tpar (grGenPar R V) (treeOf t₁))) * σ R (cSgn (grGenPar R V) j t₁ t₂)) •
          starI R V (SetOperad.comp j t₁ t₂)
            (k + if vert j t₁ ≤ k then (treeOf t₂).weight else 0) := by
  rw [Finset.mem_Ico] at hk
  obtain ⟨e, he⟩ := exists_rep t₁ hk.2
  have hst := starI_eq (R := R) (V := V) he (Tree.isLeaf_cutV _ _ hk.2)
  have hvert : vert (⟨((treeOf t₁).cutV k).2.2, Tree.lt_arity_cutV _ k hk.2⟩ :
      Fin ((treeOf t₁).cutV k).1.arity) (stdT ((treeOf t₁).cutV k).1) = k := by
    show (treeOf (stdT _)).vb ((stdT _).1.rank _) = k
    rw [treeOf_stdT, rank_stdT]
    exact Tree.vb_cutV _ _ hk.2
  rw [hvert] at hst
  exact (congrArg (fun z => mM R V j z (Cobar.ιL R 𝒞 B ((𝒥).proj B (𝔟 t₂)))) hst).trans
    (mM_repI_ιL _ (stdT ((treeOf t₁).cutV k).1) (stdT ((treeOf t₁).cutV k).2.1) e
      (Tree.isLeaf_cutV_fst hk.1 hk.2 rfl) (Tree.isLeaf_cutV _ _ hk.2) j t₂ h₂ he hvert)

/-- The sign at the root of the inner tree. -/
lemma sgn_root (x c : Bool) : σ R (!x) * σ R c * (σ R c * σ R x) = -1 := by
  cases x <;> cases c <;> simp

/-- **The commutator of the cobar differential and the merge on two generators of trees** is their
composite: `d (x ⊛ⱼ y) + d x ⊛ⱼ y + (-1)^{|x|} x ⊛ⱼ d y = x ∘ⱼ y` for the generators `x`, `y` of
two trees with vertices, none of them nullary. -/
theorem d_mM_ιL_bas (j : A) (t₁ : Reg (TreeOfArity (GrGen R V)) A)
    (t₂ : Reg (TreeOfArity (GrGen R V)) B) (h₁ : (treeOf t₁).isLeaf = false)
    (h₂ : (treeOf t₂).isLeaf = false) (hn₁ : (treeOf t₁).NoNull) (hn₂ : (treeOf t₂).NoNull) :
    (Cobar.d R 𝒞).app _ (mM R V j (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t₁)))
        (Cobar.ιL R 𝒞 B ((𝒥).proj B (𝔟 t₂))))
      + mM R V j ((Cobar.d R 𝒞).app A (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t₁))))
          (Cobar.ιL R 𝒞 B ((𝒥).proj B (𝔟 t₂)))
      + mM R V j (GrOperad.tw (R := R) true (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t₁))))
          ((Cobar.d R 𝒞).app B (Cobar.ιL R 𝒞 B ((𝒥).proj B (𝔟 t₂))))
      = GrOperad.comp (R := R) j (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t₁)))
          (Cobar.ιL R 𝒞 B ((𝒥).proj B (𝔟 t₂))) := by
  have hw : (treeOf (SetOperad.comp j t₁ t₂)).weight
      = (treeOf t₁).weight + (treeOf t₂).weight := by
    rw [treeOf_comp]
    exact Tree.weight_graft _ _ _ (rank_lt_arity t₁ j)
  have hn : (treeOf (SetOperad.comp j t₁ t₂)).NoNull := (noNull_comp j t₁ t₂).2 ⟨hn₁, hn₂⟩
  have hd := d_ιL_bas (R := R) (V := V) (SetOperad.comp j t₁ t₂) hn
  rw [hw] at hd
  have hi := (congrArg ((Cobar.d R 𝒞).app _) (mM_ιL_bas j t₁ t₂ h₁ h₂)).trans
    ((map_smul _ _ _).trans (congrArg (fun z =>
      (σ R (!(Tree.tpar (grGenPar R V) (treeOf t₁))) * σ R (cSgn (grGenPar R V) j t₁ t₂)) • z)
        hd))
  have hii : mM R V j ((Cobar.d R 𝒞).app A (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t₁))))
        (Cobar.ιL R 𝒞 B ((𝒥).proj B (𝔟 t₂)))
      = (σ R (!(Tree.tpar (grGenPar R V) (treeOf t₁))) * σ R (cSgn (grGenPar R V) j t₁ t₂)) •
          ∑ k ∈ Finset.Ico 1 (treeOf t₁).weight, starI R V (SetOperad.comp j t₁ t₂)
            (k + if vert j t₁ ≤ k then (treeOf t₂).weight else 0) := by
    refine (congrArg (fun z => mM R V j z (Cobar.ιL R 𝒞 B ((𝒥).proj B (𝔟 t₂))))
      (d_ιL_bas t₁ hn₁)).trans ?_
    refine (bilin_neg_sum_left (mM R V j) _ _ _).trans ?_
    refine Eq.trans ?_ (neg_sum_neg_smul _ _ _)
    exact congrArg Neg.neg (Finset.sum_congr rfl fun k hk => mM_starI_ιL j t₁ t₂ h₂ hk)
  have hiii : mM R V j (GrOperad.tw (R := R) true (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t₁))))
        ((Cobar.d R 𝒞).app B (Cobar.ιL R 𝒞 B ((𝒥).proj B (𝔟 t₂))))
      = (σ R (!(Tree.tpar (grGenPar R V) (treeOf t₁))) * σ R (cSgn (grGenPar R V) j t₁ t₂)) •
          ∑ k ∈ Finset.Ico 1 (treeOf t₂).weight,
            starI R V (SetOperad.comp j t₁ t₂) (vert j t₁ + k) := by
    have htw : GrOperad.tw (R := R) true (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t₁)))
        = σ R (true && !(Tree.tpar (grGenPar R V) (treeOf t₁))) •
            Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t₁)) :=
      GrOperad.tw_hom true (par_ιL_bas t₁)
    refine (congrArg₂ (fun z y => mM R V j z y) htw (d_ιL_bas t₂ hn₂)).trans ?_
    refine (LinearMap.map_smul₂ _ _ _ _).trans ?_
    refine (congrArg _ (bilin_neg_sum_right (mM R V j) _ _ _)).trans ?_
    refine (congrArg _ (congrArg Neg.neg
      (Finset.sum_congr rfl fun k hk => mM_ιL_starI j t₁ t₂ h₁ hk))).trans ?_
    refine (congrArg _ (neg_sum_neg_smul _ _ _)).trans ?_
    exact smul_smul _ _ _
  have hiv : starI R V (SetOperad.comp j t₁ t₂) (vert j t₁)
      = (σ R (cSgn (grGenPar R V) j t₁ t₂) * σ R (Tree.tpar (grGenPar R V) (treeOf t₁))) •
          GrOperad.comp (R := R) j (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t₁)))
            (Cobar.ιL R 𝒞 B ((𝒥).proj B (𝔟 t₂))) :=
    (starI_eq (R := R) (V := V) (SetOperad.map_refl (SetOperad.comp j t₁ t₂)) h₂).trans
      (GrOperad.map_refl _)
  refine (congrArg₂ (· + ·) (congrArg₂ (· + ·) hi hii) hiii).trans ?_
  exact combine_cuts (Tree.one_le_vb h₁ _) (Tree.vb_le_weight _ _) (Tree.one_le_weight h₂)
    (fun k => starI R V (SetOperad.comp j t₁ t₂) k) _ _ (sgn_root _ _) _ hiv

end Cobar

end Generators

end Operad
