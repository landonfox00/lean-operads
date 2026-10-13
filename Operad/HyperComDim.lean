/-
# The hypercommutative operad in arities at most three

The operations of `HyperCom` with at most three inputs: **`dim HyperCom(n) = 0, 1, 1, 2` for
`n = 0, 1, 2, 3`** (`HyperCom.subsingleton_of_card`, `HyperCom.finrank_one`, `HyperCom.finrank_two`,
`HyperCom.finrank_three`), over any field. In arity three the two operations are `m₃` and the
iterated product `m₂ ∘ m₂`, all of whose relabellings agree by the symmetry of `m₂` and the WDVV
relations (`HyperCom.map_c22_eq_all`).

* **Upper bound.** The relabellings of the unit, of `m₂`, of `m₃` and of `m₂ ∘₀ m₂` span, together
  with everything of arity at least four, a suboperad (`HyperCom.truncSub`); it contains the
  generators, so it is everything (`SymSuboperad.mem_of_presGen`).
* **Lower bound.** For any scalars `cₙ`, the operations `μₙ(v) = cₙ v₁ ⋯ vₙ` on the ground ring
  make a hypercommutative algebra (`HCAlg.scal`): the WDVV sums only depend on the sizes of the
  sets `S`, and transposing `j` and `k` exchanges the two sides. With `c₂ = 1` the operation `m₃`
  vanishes and `m₂ ∘ m₂` does not; with `c₃ = 1` the reverse.

The next dimension, `dim HyperCom(4) = 7`, is not formalized.
-/
import Operad.HyperCom
import Operad.SymSuboperad
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

universe u v

namespace Operad

open Sym Finset

/-! ## Scalar hypercommutative algebras -/

namespace HCAlg

variable (R : Type u) [CommRing R]

/-- **Scalar operations** on the ground ring: `μₙ(v) = cₙ v₁ ⋯ vₙ`. -/
@[nolint unusedArguments]
noncomputable def scalOps (c : ℕ → R) (n : ℕ) (_ : 2 ≤ n) : EndOp R R (Fin n) :=
  c n • MultilinearMap.mkPiAlgebra R (Fin n) R

variable {R}

lemma scalOps_apply (c : ℕ → R) {n : ℕ} (h : 2 ≤ n) (v : Fin n → R) :
    scalOps R c n h v = c n * ∏ i, v i := by
  simp [scalOps, MultilinearMap.mkPiAlgebra_apply]

lemma prod_orderEmbOfFin {n : ℕ} (S : Finset (Fin n)) (v : Fin n → R) :
    ∏ t, v (S.orderEmbOfFin rfl t) = ∏ a ∈ S, v a := by
  refine (Fintype.prod_equiv (S.orderIsoOfFin rfl).toEquiv (fun t => v (S.orderEmbOfFin rfl t))
    (fun x : S => v x) fun t => ?_).trans (Finset.prod_coe_sort S v)
  simp

/-- **A WDVV composite of scalar operations** is a multiple of the product of the inputs, by a
scalar only depending on the size of the set. -/
lemma wVal_scal (c : ℕ → R) {n : ℕ} (S : Finset (Fin n)) (v : Fin n → R) :
    HyperCom.wVal R (scalOps R c) S v
      = (if 2 ≤ S.card ∧ 1 ≤ Sᶜ.card then c (Sᶜ.card + 1) * c S.card else 0) * ∏ i, v i := by
  unfold HyperCom.wVal
  split_ifs with h
  · rw [scalOps_apply, Fin.prod_cons, scalOps_apply, prod_orderEmbOfFin, prod_orderEmbOfFin,
      ← Finset.prod_mul_prod_compl S v]
    ring
  · rw [zero_mul]

/-- **Scalar operations make a hypercommutative algebra.** -/
noncomputable def scal (c : ℕ → R) : HCAlg R R where
  μ := scalOps R c
  symm n h σ v := by
    rw [scalOps_apply, scalOps_apply, Equiv.prod_comp σ v]
  wdvv n i j k hij hik hjk v := by
    simp only [wVal_scal]
    refine Finset.sum_equiv (Equiv.finsetCongr (Equiv.swap j k)) (fun S => ?_) (fun S _ => ?_)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.finsetCongr_apply,
        Finset.mem_map_equiv, Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hij hik,
        Equiv.swap_apply_left, Equiv.swap_apply_right]
    · simp only [Equiv.finsetCongr_apply, Finset.card_map, Finset.card_compl,
        Fintype.card_fin]

end HCAlg

/-! ## The operations of arity at most three -/

namespace HyperCom

variable {R : Type u} [CommRing R]

local notation "I" => SymOperadIdeal.span R (hcRel R)

/-- **The generator** `mₙ`, in the hypercommutative operad. -/
noncomputable def opGen (n : ℕ) (h : 2 ≤ n) : HyperComOp R (Fin n) :=
  (I).proj _ (Finsupp.single (Pres.gen (⟨h⟩ : HCGen n)) 1)

/-- **The generators are totally symmetric.** -/
lemma map_opGen {n : ℕ} (h : 2 ≤ n) (σ : Equiv.Perm (Fin n)) :
    SymOperad.map (R := R) σ (opGen (R := R) n h) = opGen n h := by
  have hrel : mono (R := R) n h σ - mono n h 1 ∈ (I).sub (Fin n) :=
    SymOperadIdeal.subset_span (R := R) n (Or.inl ⟨h, σ, rfl⟩)
  rw [← SymOperadIdeal.proj_eq_zero_iff, map_sub, sub_eq_zero] at hrel
  have h1 : SymOperad.map (R := R) σ (Finsupp.single (Pres.gen (⟨h⟩ : HCGen n)) (1 : R))
      = mono n h σ := by
    show Lin.mapL R σ _ = _
    rw [Lin.mapL_single]
    rfl
  have h2 : mono (R := R) n h 1 = Finsupp.single (Pres.gen (⟨h⟩ : HCGen n)) 1 := by
    unfold mono
    congr 1
    exact SetOperad.map_refl (Pres.mk (gen n h))
  unfold opGen
  rw [← SymOperadIdeal.projHom_app, ← SymOperadHom.app_map, SymOperadIdeal.projHom_app, h1,
    hrel, h2]
  rfl

/-- The inputs of `m₂ ∘₀ m₂`. -/
abbrev W := Without (Fin 2) 0 ⊕ Fin 2

/-- The input of the outer operation of `m₂ ∘₀ m₂`. -/
def outer : W := Sum.inl ⟨1, by decide⟩

lemma card_W : Fintype.card W = 3 := rfl

variable (R) in
/-- **The iterated product** `m₂ ∘₀ m₂`. -/
noncomputable def c22 : HyperComOp R W :=
  SymOperad.comp (R := R) (0 : Fin 2) (opGen 2 le_rfl) (opGen 2 le_rfl)

lemma perm_W (f : Equiv.Perm W) (hf : f outer = outer) :
    f = 1 ∨ f = Equiv.swap (Sum.inr 0) (Sum.inr 1) := by
  revert f
  decide

lemma map_c22_swap :
    SymOperad.map (R := R) (Equiv.swap (Sum.inr 0 : W) (Sum.inr 1)) (c22 R) = c22 R := by
  have hs : Equiv.swap (Sum.inr 0 : W) (Sum.inr 1)
      = compEquiv (Equiv.refl (Fin 2)) (Equiv.swap 0 1) 0 := by
    ext w
    revert w
    decide
  have := SymOperad.map_comp (R := R) (Equiv.refl (Fin 2)) (Equiv.swap (0 : Fin 2) 1) 0
    (opGen (R := R) 2 le_rfl) (opGen 2 le_rfl)
  rw [SymOperad.map_refl, map_opGen] at this
  rw [hs]
  exact this

/-- **A relabelling of `m₂ ∘₀ m₂` only depends on where the outer input goes**, by the symmetry
of `m₂`. -/
lemma map_c22_eq {A : Type} [Fintype A] [DecidableEq A] (e e' : W ≃ A)
    (h : e outer = e' outer) :
    SymOperad.map (R := R) e (c22 R) = SymOperad.map (R := R) e' (c22 R) := by
  have he : e = (e.trans e'.symm).trans e' := by
    ext w
    simp
  rw [he, SymOperad.map_trans]
  rcases perm_W (e.trans e'.symm) (by simp [h]) with hf | hf
  · rw [hf]
    exact congrArg _ (SymOperad.map_refl (R := R) _)
  · rw [hf, map_c22_swap]

/-- **A WDVV composite in arity three** is a relabelling of `m₂ ∘₀ m₂`, the outer input going out
of the set. -/
lemma wTerm_eq (S : Finset (Fin 3)) (hS : S.card = 2) :
    ∃ e : W ≃ Fin 3, wTerm (R := R) S = SymOperad.map (R := R) e (SymOperad.comp (R := R)
      (0 : Fin 2) (Finsupp.single (Pres.gen (⟨le_rfl⟩ : HCGen 2)) 1)
      (Finsupp.single (Pres.gen (⟨le_rfl⟩ : HCGen 2)) 1)) ∧ e outer ∉ S := by
  have hc : Sᶜ.card = 1 := by rw [Finset.card_compl, hS]; rfl
  have key : ∀ (a b : ℕ) (_ : a = 1) (_ : b = 2) (E : Without (Fin (a + 1)) 0 ⊕ Fin b ≃ Fin 3)
      (h1 : 2 ≤ a + 1) (h2 : 2 ≤ b), (∀ x, E (Sum.inl x) ∉ S) →
      ∃ e : W ≃ Fin 3, (Finsupp.single (Pres.mk (.map E (.comp 0 (gen (a + 1) h1) (gen b h2))))
        (1 : R) : FreeHC R (Fin 3)) = SymOperad.map (R := R) (P := FreeHC R) e
          (SymOperad.comp (R := R) (0 : Fin 2) (Finsupp.single (Pres.gen (⟨le_rfl⟩ : HCGen 2)) 1)
          (Finsupp.single (Pres.gen (⟨le_rfl⟩ : HCGen 2)) 1)) ∧ e outer ∉ S := by
    rintro a b rfl rfl E h1 h2 hE
    refine ⟨E, ?_, hE _⟩
    show _ = Lin.mapL R E (Lin.compL R 0 _ _)
    rw [Lin.compL_single, Lin.mapL_single, mul_one]
    rfl
  unfold wTerm
  rw [dif_pos ⟨by omega, by omega⟩]
  exact key _ _ hc hS (wEquiv S) _ _ fun x => by
    rw [wEquiv_inl]
    exact Finset.mem_compl.1 (Finset.orderEmbOfFin_mem _ _ _)

lemma proj_wTerm (S : Finset (Fin 3)) (hS : S.card = 2) :
    ∃ e : W ≃ Fin 3, (I).proj _ (wTerm (R := R) S) = SymOperad.map (R := R) e (c22 R) ∧
      e outer ∉ S := by
  obtain ⟨e, he, hS⟩ := wTerm_eq (R := R) S hS
  refine ⟨e, ?_, hS⟩
  rw [he, ← SymOperadIdeal.projHom_app, SymOperadHom.app_map, SymOperadHom.app_comp]
  rfl

lemma filter_pair (p q r : Fin 3) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    univ.filter (fun S : Finset (Fin 3) => p ∈ S ∧ q ∈ S ∧ r ∉ S) = {{p, q}} := by
  revert p q r
  decide

lemma eq_of_not_mem_pair {p q r x : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hx : x ∉ ({p, q} : Finset (Fin 3))) : x = r := by
  revert p q r x
  decide

/-- **All relabellings of `m₂ ∘₀ m₂` agree**, by the WDVV relations. -/
lemma map_c22_eq_all (e e' : W ≃ Fin 3) :
    SymOperad.map (R := R) e (c22 R) = SymOperad.map (R := R) e' (c22 R) := by
  by_cases h : e outer = e' outer
  · exact map_c22_eq e e' h
  obtain ⟨i, hij, hik⟩ : ∃ i : Fin 3, i ≠ e' outer ∧ i ≠ e outer := by
    revert h
    generalize e outer = k
    generalize e' outer = j
    revert j k
    decide
  have hrel : wdvv (R := R) i (e' outer) (e outer) ∈ (I).sub (Fin 3) :=
    SymOperadIdeal.subset_span (R := R) 3
      (Or.inr ⟨i, e' outer, e outer, hij, hik, Ne.symm h, rfl⟩)
  rw [← SymOperadIdeal.proj_eq_zero_iff, wdvv, filter_pair _ _ _ hij hik (Ne.symm h),
    filter_pair _ _ _ hik hij h, Finset.sum_singleton, Finset.sum_singleton, map_sub,
    sub_eq_zero] at hrel
  obtain ⟨e₁, he₁, hS₁⟩ := proj_wTerm (R := R) {i, e' outer} (Finset.card_pair hij)
  obtain ⟨e₂, he₂, hS₂⟩ := proj_wTerm (R := R) {i, e outer} (Finset.card_pair hik)
  rw [he₁, he₂] at hrel
  rw [map_c22_eq e e₁ (eq_of_not_mem_pair hij hik (Ne.symm h) hS₁).symm, hrel,
    map_c22_eq e₂ e' (eq_of_not_mem_pair hik hij h hS₂)]

/-! ## The truncated suboperad -/

variable (R) in
/-- **The basic operations** with inputs `A`: the relabellings of the unit, of `m₂`, of `m₃` and of
`m₂ ∘₀ m₂`. -/
def basic (A : Type) [Fintype A] [DecidableEq A] : Set (HyperComOp R A) :=
  {x | (∃ e : Unit ≃ A, x = SymOperad.map (R := R) e (SymOperad.one R)) ∨
    (∃ e : Fin 2 ≃ A, x = SymOperad.map (R := R) e (opGen 2 le_rfl)) ∨
    (∃ e : Fin 3 ≃ A, x = SymOperad.map (R := R) e (opGen 3 (by norm_num))) ∨
    (∃ e : W ≃ A, x = SymOperad.map (R := R) e (c22 R))}

variable (R) in
/-- **The truncated suboperad**: spanned by the basic operations in arities at most three, and
everything in higher arities. -/
noncomputable def truncSp (A : Type) [Fintype A] [DecidableEq A] : Submodule R (HyperComOp R A) :=
  if 4 ≤ Fintype.card A then ⊤ else Submodule.span R (basic R A)

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

lemma mem_truncSp_of_card (h : 4 ≤ Fintype.card A) (x : HyperComOp R A) : x ∈ truncSp R A := by
  rw [truncSp, if_pos h]
  exact Submodule.mem_top

lemma mem_truncSp_of_basic {x : HyperComOp R A} (hx : x ∈ basic R A) : x ∈ truncSp R A := by
  unfold truncSp
  split_ifs
  · exact Submodule.mem_top
  · exact Submodule.subset_span hx

lemma map_mem_basic (e : A ≃ B) {x : HyperComOp R A} (hx : x ∈ basic R A) :
    SymOperad.map (R := R) e x ∈ basic R B := by
  rcases hx with ⟨f, rfl⟩ | ⟨f, rfl⟩ | ⟨f, rfl⟩ | ⟨f, rfl⟩
  · exact Or.inl ⟨f.trans e, (SymOperad.map_trans (R := R) f e _).symm⟩
  · exact Or.inr (Or.inl ⟨f.trans e, (SymOperad.map_trans (R := R) f e _).symm⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f.trans e, (SymOperad.map_trans (R := R) f e _).symm⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨f.trans e, (SymOperad.map_trans (R := R) f e _).symm⟩))

lemma map_mem_truncSp (e : A ≃ B) {x : HyperComOp R A} (hx : x ∈ truncSp R A) :
    SymOperad.map (R := R) e x ∈ truncSp R B := by
  have hc := Fintype.card_congr e
  unfold truncSp at hx ⊢
  split_ifs at hx ⊢ with h₁ h₂ h₂
  · exact Submodule.mem_top
  · exact absurd (hc ▸ h₁) h₂
  · exact absurd (hc ▸ h₂) h₁
  · refine (Submodule.span_le.2 ?_ : Submodule.span R (basic R A) ≤
      (Submodule.span R (basic R B)).comap (SymOperad.map (R := R) e)) hx
    exact fun y hy => Submodule.subset_span (map_mem_basic e hy)

lemma nonempty_of_basic {x : HyperComOp R A} (hx : x ∈ basic R A) : Nonempty A := by
  rcases hx with ⟨f, -⟩ | ⟨f, -⟩ | ⟨f, -⟩ | ⟨f, -⟩
  exacts [⟨f ()⟩, ⟨f 0⟩, ⟨f 0⟩, ⟨f (Sum.inr 0)⟩]

lemma card_comp {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] (j : X) :
    Fintype.card (Without X j ⊕ Y) + 1 = Fintype.card X + Fintype.card Y := by
  rw [Fintype.card_sum, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have := Fintype.card_pos_iff.2 ⟨j⟩
  omega

/-- Compositions of relabellings are relabellings of compositions. -/
lemma comp_map_mem {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (g : HyperComOp R X) (g' : HyperComOp R Y)
    (H : ∀ j : X, SymOperad.comp (R := R) j g g' ∈ truncSp R (Without X j ⊕ Y))
    (e : X ≃ A) (f : Y ≃ B) (i : A) :
    SymOperad.comp (R := R) i (SymOperad.map (R := R) e g) (SymOperad.map (R := R) f g')
      ∈ truncSp R (Without A i ⊕ B) := by
  obtain ⟨j, rfl⟩ := e.surjective i
  rw [← SymOperad.map_comp]
  exact map_mem_truncSp _ (H j)

lemma comp_one_left {Y : Type} [Fintype Y] [DecidableEq Y] {g' : HyperComOp R Y}
    (hg' : g' ∈ truncSp R Y) (j : Unit) :
    SymOperad.comp (R := R) j (SymOperad.one R) g' ∈ truncSp R (Without Unit j ⊕ Y) := by
  have := congrArg (SymOperad.map (R := R) (leftUnitEquiv Y).symm)
    (SymOperad.one_comp (R := R) g')
  rw [SymOperad.map_symm_map] at this
  rw [this]
  exact map_mem_truncSp _ hg'

lemma comp_one_right {X : Type} [Fintype X] [DecidableEq X] {g : HyperComOp R X}
    (hg : g ∈ truncSp R X) (j : X) :
    SymOperad.comp (R := R) j g (SymOperad.one R) ∈ truncSp R (Without X j ⊕ Unit) := by
  have := congrArg (SymOperad.map (R := R) (rightUnitEquiv j).symm)
    (SymOperad.comp_one (R := R) j g)
  rw [SymOperad.map_symm_map] at this
  rw [this]
  exact map_mem_truncSp _ hg

lemma comp_m2_m2 (j : Fin 2) :
    SymOperad.comp (R := R) j (opGen 2 le_rfl) (opGen 2 le_rfl)
      ∈ truncSp R (Without (Fin 2) j ⊕ Fin 2) := by
  obtain ⟨σ, rfl⟩ : ∃ σ : Equiv.Perm (Fin 2), σ 0 = j := ⟨Equiv.swap 0 j, Equiv.swap_apply_left _ _⟩
  have := SymOperad.map_comp (R := R) σ (Equiv.refl (Fin 2)) 0 (opGen (R := R) 2 le_rfl)
    (opGen 2 le_rfl)
  rw [map_opGen, SymOperad.map_refl] at this
  rw [← this]
  exact mem_truncSp_of_basic (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩)))

lemma comp_big {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (h : 5 ≤ Fintype.card X + Fintype.card Y) (g : HyperComOp R X) (g' : HyperComOp R Y)
    (j : X) : SymOperad.comp (R := R) j g g' ∈ truncSp R (Without X j ⊕ Y) :=
  mem_truncSp_of_card (by have := card_comp (Y := Y) j; omega) _

lemma one_mem_truncSp : SymOperad.one R ∈ truncSp R Unit :=
  mem_truncSp_of_basic (Or.inl ⟨Equiv.refl _, (SymOperad.map_refl (R := R) _).symm⟩)

lemma m2_mem_truncSp : opGen (R := R) 2 le_rfl ∈ truncSp R (Fin 2) :=
  mem_truncSp_of_basic (Or.inr (Or.inl ⟨Equiv.refl _, (SymOperad.map_refl (R := R) _).symm⟩))

lemma m3_mem_truncSp : opGen (R := R) 3 (by norm_num) ∈ truncSp R (Fin 3) :=
  mem_truncSp_of_basic
    (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, (SymOperad.map_refl (R := R) _).symm⟩)))

lemma c22_mem_truncSp : c22 R ∈ truncSp R W :=
  mem_truncSp_of_basic
    (Or.inr (Or.inr (Or.inr ⟨Equiv.refl _, (SymOperad.map_refl (R := R) _).symm⟩)))

lemma comp_mem_truncSp (i : A) {x : HyperComOp R A} {y : HyperComOp R B}
    (hx : x ∈ truncSp R A) (hy : y ∈ truncSp R B) :
    SymOperad.comp (R := R) i x y ∈ truncSp R (Without A i ⊕ B) := by
  by_cases h4 : 4 ≤ Fintype.card (Without A i ⊕ B)
  · exact mem_truncSp_of_card h4 _
  have hc := card_comp (Y := B) i
  have hA1 := Fintype.card_pos_iff.2 ⟨i⟩
  have hyS : y ∈ Submodule.span R (basic R B) := by
    unfold truncSp at hy
    rwa [if_neg (by omega)] at hy
  by_cases hA : 4 ≤ Fintype.card A
  · have hB : Fintype.card B = 0 := by omega
    haveI := Fintype.card_eq_zero_iff.1 hB
    have hT : basic R B = ∅ := Set.eq_empty_of_forall_notMem fun z hz =>
      (nonempty_of_basic hz).elim isEmptyElim
    rw [hT, Submodule.span_empty, Submodule.mem_bot] at hyS
    rw [hyS, map_zero]
    exact zero_mem _
  have hxS : x ∈ Submodule.span R (basic R A) := by
    unfold truncSp at hx
    rwa [if_neg hA] at hx
  have hm := Submodule.apply_mem_map₂ (SymOperad.comp (R := R) i) hxS hyS
  rw [Submodule.map₂_span_span] at hm
  refine (Submodule.span_le.2 ?_) hm
  rintro _ ⟨x, hx, y, hy, rfl⟩
  rcases hx with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ <;>
  rcases hy with ⟨f, rfl⟩ | ⟨f, rfl⟩ | ⟨f, rfl⟩ | ⟨f, rfl⟩ <;>
  refine comp_map_mem _ _ ?_ e f i
  · exact comp_one_left one_mem_truncSp
  · exact comp_one_left m2_mem_truncSp
  · exact comp_one_left m3_mem_truncSp
  · exact comp_one_left c22_mem_truncSp
  · exact comp_one_right m2_mem_truncSp
  · exact comp_m2_m2
  · exact comp_big (by simp) _ _
  · exact comp_big (by simp) _ _
  · exact comp_one_right m3_mem_truncSp
  · exact comp_big (by simp) _ _
  · exact comp_big (by simp) _ _
  · exact comp_big (by simp) _ _
  · exact comp_one_right c22_mem_truncSp
  · exact comp_big (by simp) _ _
  · exact comp_big (by simp) _ _
  · exact comp_big (by simp) _ _

variable (R) in
/-- **The truncated suboperad.** -/
noncomputable def truncSub : SymSuboperad R (HyperComOp R) where
  sub := truncSp R
  map_mem e _ hx := map_mem_truncSp e hx
  one_mem := one_mem_truncSp
  comp_mem i _ _ hx hy := comp_mem_truncSp i hx hy

/-- **Every operation is in the truncated suboperad**: it contains the generators. -/
theorem mem_truncSp (x : HyperComOp R A) : x ∈ truncSp R A := by
  refine SymSuboperad.mem_of_presGen (truncSub R) (fun n g => ?_) x
  obtain ⟨hg⟩ := g
  obtain rfl | rfl | h4 : n = 2 ∨ n = 3 ∨ 4 ≤ n := by omega
  · exact m2_mem_truncSp
  · exact m3_mem_truncSp
  · exact mem_truncSp_of_card (by simpa using h4) _

/-- **In arities at most three, the operations are spanned by the basic operations.** -/
theorem mem_span_basic (hA : Fintype.card A ≤ 3) (x : HyperComOp R A) :
    x ∈ Submodule.span R (basic R A) := by
  have := mem_truncSp x
  unfold truncSp at this
  rwa [if_neg (by omega)] at this

/-! ## The upper bounds -/

/-- **There are no operations without inputs.** -/
theorem subsingleton_of_card (hA : Fintype.card A = 0) : Subsingleton (HyperComOp R A) := by
  haveI := Fintype.card_eq_zero_iff.1 hA
  have h : ∀ z : HyperComOp R A, z = 0 := fun z => by
    have := mem_span_basic (by omega) z
    rwa [show basic R A = ∅ from Set.eq_empty_of_forall_notMem fun z hz =>
      (nonempty_of_basic hz).elim isEmptyElim, Submodule.span_empty, Submodule.mem_bot] at this
  exact ⟨fun x y => by rw [h x, h y]⟩

variable (R) in
/-- The unit, with inputs `Fin 1`. -/
noncomputable def unit1 : HyperComOp R (Fin 1) :=
  SymOperad.map (R := R) (Equiv.ofUnique Unit (Fin 1)) (SymOperad.one R)

variable (R) in
/-- **The iterated product** `m₂(m₂(x₀, x₁), x₂)`, up to relabelling, with inputs `Fin 3`. -/
noncomputable def t3 : HyperComOp R (Fin 3) :=
  SymOperad.map (R := R) (Fintype.equivFinOfCardEq card_W) (c22 R)

lemma basic_one : basic R (Fin 1) ⊆ {unit1 R} := by
  rintro _ (⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩)
  · rw [Set.mem_singleton_iff, unit1, Subsingleton.elim e]
  · exact absurd (Fintype.card_congr e) (by simp)
  · exact absurd (Fintype.card_congr e) (by simp)
  · exact absurd (Fintype.card_congr e) (by simp)

lemma basic_two : basic R (Fin 2) ⊆ {opGen 2 le_rfl} := by
  rintro _ (⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩)
  · exact absurd (Fintype.card_congr e) (by simp)
  · exact map_opGen le_rfl e
  · exact absurd (Fintype.card_congr e) (by simp)
  · exact absurd (Fintype.card_congr e) (by simp)

lemma basic_three : basic R (Fin 3) ⊆ Set.range ![opGen 3 (by norm_num), t3 R] := by
  rintro _ (⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩)
  · exact absurd (Fintype.card_congr e) (by simp)
  · exact absurd (Fintype.card_congr e) (by simp)
  · exact ⟨0, (map_opGen _ e).symm⟩
  · exact ⟨1, map_c22_eq_all _ _⟩

/-! ## The lower bounds -/

/-- **The generators act by the operations**, in an algebra. -/
lemma alg_opGen {V : Type v} [AddCommGroup V] [Module R V] (a : HCAlg R V) {n : ℕ} (h : 2 ≤ n) :
    ((HyperComOp.algebraEquiv R V).symm a).app (Fin n) (opGen n h) = a.μ n h := by
  show (hcHom V a.μ).app (Fin n) (Finsupp.single (Pres.mk (.gen ⟨h⟩)) 1) = _
  rw [hcHom_single]
  rfl

/-- The generators in a scalar hypercommutative algebra. -/
lemma scal_opGen (c : ℕ → R) {n : ℕ} (h : 2 ≤ n) (v : Fin n → R) :
    ((HyperComOp.algebraEquiv R R).symm (HCAlg.scal c)).app (Fin n) (opGen n h) v
      = c n * ∏ i, v i := by
  rw [alg_opGen]
  exact HCAlg.scalOps_apply c h v

/-- The iterated product in a scalar hypercommutative algebra. -/
lemma scal_t3 (c : ℕ → R) :
    ((HyperComOp.algebraEquiv R R).symm (HCAlg.scal c)).app (Fin 3) (t3 R) (fun _ => 1)
      = c 2 * c 2 := by
  rw [t3, SymOperadHom.app_map, c22, SymOperadHom.app_comp, alg_opGen]
  show HCAlg.scalOps R c 2 le_rfl (feed 0 _ (HCAlg.scalOps R c 2 le_rfl _)) = _
  rw [HCAlg.scalOps_apply, HCAlg.scalOps_apply, Fin.prod_univ_two, Fin.prod_univ_two, feed_self,
    feed_of_ne (by decide)]
  simp

/-- The unit in a scalar hypercommutative algebra. -/
lemma scal_unit1 (c : ℕ → R) :
    ((HyperComOp.algebraEquiv R R).symm (HCAlg.scal c)).app (Fin 1) (unit1 R) (fun _ => 1)
      = 1 := by
  rw [unit1, SymOperadHom.app_map, SymOperadHom.app_one]
  rfl

/-! ## The dimensions -/

variable (K : Type u) [Field K]

/-- **`m₃` and `m₂ ∘ m₂` are linearly independent**: the scalar algebra with `c₂ = 1` separates
them from the one with `c₃ = 1`. -/
theorem linearIndependent_three :
    LinearIndependent K ![opGen (R := K) 3 (by norm_num), t3 K] := by
  refine LinearIndependent.pair_iff.2 fun s t hst => ?_
  have e₂ := congrArg (fun x => ((HyperComOp.algebraEquiv K K).symm
    (HCAlg.scal fun n => if n = 2 then 1 else 0)).app (Fin 3) x (fun _ => 1)) hst
  have e₃ := congrArg (fun x => ((HyperComOp.algebraEquiv K K).symm
    (HCAlg.scal fun n => if n = 3 then 1 else 0)).app (Fin 3) x (fun _ => 1)) hst
  simp only [map_add, map_smul, MultilinearMap.add_apply, MultilinearMap.smul_apply, scal_opGen,
    scal_t3, map_zero, MultilinearMap.zero_apply, smul_eq_mul] at e₂ e₃
  simp at e₂ e₃
  exact ⟨e₃, e₂⟩

lemma opGen_two_ne_zero : opGen (R := K) 2 le_rfl ≠ 0 := fun h => by
  have := congrArg (fun x => ((HyperComOp.algebraEquiv K K).symm
    (HCAlg.scal fun _ => 1)).app (Fin 2) x (fun _ => 1)) h
  simp [scal_opGen] at this

lemma unit1_ne_zero : unit1 K ≠ 0 := fun h => by
  have := congrArg (fun x => ((HyperComOp.algebraEquiv K K).symm
    (HCAlg.scal fun _ => 1)).app (Fin 1) x (fun _ => 1)) h
  simp [scal_unit1] at this

theorem finrank_fin_one : Module.finrank K (HyperComOp K (Fin 1)) = 1 := by
  have htop : Submodule.span K {unit1 K} = ⊤ :=
    eq_top_iff.2 fun x _ => Submodule.span_mono basic_one (mem_span_basic (by simp) x)
  rw [← finrank_top, ← htop, finrank_span_singleton (unit1_ne_zero K)]

theorem finrank_fin_two : Module.finrank K (HyperComOp K (Fin 2)) = 1 := by
  have htop : Submodule.span K {opGen (R := K) 2 le_rfl} = ⊤ :=
    eq_top_iff.2 fun x _ => Submodule.span_mono basic_two (mem_span_basic (by simp) x)
  rw [← finrank_top, ← htop, finrank_span_singleton (opGen_two_ne_zero K)]

theorem finrank_fin_three : Module.finrank K (HyperComOp K (Fin 3)) = 2 := by
  have htop : Submodule.span K (Set.range ![opGen (R := K) 3 (by norm_num), t3 K]) = ⊤ :=
    eq_top_iff.2 fun x _ => Submodule.span_mono basic_three (mem_span_basic (by simp) x)
  rw [← finrank_top, ← htop, finrank_span_eq_card (linearIndependent_three K)]
  simp

variable {K}

/-- **The hypercommutative operad has one operation of arity one**, the unit. -/
theorem finrank_one (hA : Fintype.card A = 1) : Module.finrank K (HyperComOp K A) = 1 := by
  rw [← (SymOperad.mapEquiv (R := K) (P := HyperComOp K)
    (Fintype.equivFinOfCardEq hA).symm).finrank_eq, finrank_fin_one]

/-- **The hypercommutative operad has one operation of arity two**, the product `m₂`. -/
theorem finrank_two (hA : Fintype.card A = 2) : Module.finrank K (HyperComOp K A) = 1 := by
  rw [← (SymOperad.mapEquiv (R := K) (P := HyperComOp K)
    (Fintype.equivFinOfCardEq hA).symm).finrank_eq, finrank_fin_two]

/-- **The hypercommutative operad has two operations of arity three**, `m₃` and `m₂ ∘ m₂`. -/
theorem finrank_three (hA : Fintype.card A = 3) : Module.finrank K (HyperComOp K A) = 2 := by
  rw [← (SymOperad.mapEquiv (R := K) (P := HyperComOp K)
    (Fintype.equivFinOfCardEq hA).symm).finrank_eq, finrank_fin_three]

end HyperCom

end Operad
