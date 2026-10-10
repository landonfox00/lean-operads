/-
# The Gerstenhaber operad inside the BV operad

WIP
-/
import Operad.InnerDer
import Operad.GerOperad
import Operad.GrSuboperad

universe u v

namespace Operad

open Sym GerBV GrOperad

/-! ## The inner derivation of a unary operation, positionally -/

section Positional

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]

/-- A unary operation on the standard one-element type, on `Unit`. -/
abbrev toUnit (d : P (Fin 1)) : P Unit := map (R := R) unitFinOne.symm d

lemma map_finCongr_self {n : ℕ} (h : n = n) (x : P (Fin n)) : map (R := R) (finCongr h) x = x := by
  rw [finCongr_refl, map_refl]

lemma lcomp_eq_nsc (d : P (Fin 1)) {n : ℕ} (x : P (Fin n)) :
    lcomp R (toUnit (R := R) d) x = map (R := R) (finCongr (by omega)) (nsc R 0 0 d x) := by
  rw [lcomp_apply, toUnit, comp_map_left unitFinOne.symm (⟨0, by omega⟩ : Fin (0 + 1 + 0)) ()
    rfl, ← map_trans, nsc, ← map_trans]
  refine congrArg (fun e => map (R := R) e _) (Equiv.ext fun z => ?_)
  rcases z with ⟨⟨k, hk⟩, hne⟩ | j
  · exact absurd (Fin.ext (by omega)) hne
  · refine Fin.ext ?_
    show (j : ℕ) = 0 + (j : ℕ)
    omega

lemma rcomp_eq_nsc (d : P (Fin 1)) (a b : ℕ) (i : Fin (a + 1 + b)) (hi : i.val = a)
    (x : P (Fin (a + 1 + b))) :
    rcomp R (toUnit (R := R) d) i x = nsc R a b x d := by
  obtain rfl : i = ⟨a, by clear hi; omega⟩ := Fin.ext hi
  rw [rcomp_apply, toUnit, comp_map_right]
  erw [← map_trans]
  rw [nsc]
  refine congrArg (fun e => map (R := R) e _) (Equiv.ext fun z => ?_)
  rcases z with ⟨⟨k, hk⟩, hne⟩ | j
  · have hka : k ≠ a := fun e => hne (Fin.ext e)
    refine Fin.ext ?_
    rw [Equiv.trans_apply, insertEquiv_inl_val]
    show k = _
    dsimp only
    split_ifs <;> omega
  · refine Fin.ext ?_
    show a = a + (j : ℕ)
    have := j.isLt
    omega

/-- **The inner derivation is a derivation of the planar compositions.** -/
lemma innerL_nsc (D : P Unit) (hD : par (R := R) true D = D) (a b : ℕ) {n : ℕ}
    (x : P (Fin (a + 1 + b))) (y : P (Fin n)) :
    innerL R D (nsc R a b x y)
      = nsc R a b (innerL R D x) y + nsc R a b (tw (R := R) true x) (innerL R D y) := by
  rw [nsc, innerL_map, innerL_comp D hD, map_add]
  rfl

end Positional

namespace BVGer

variable (R : Type u) [CommRing R]

/-- The product of `BV`. -/
noncomputable abbrev mB : BVOp R (Fin 2) := FreeGr.presGen (BV.rel R) BVGen.mul

/-- The operator of `BV`. -/
noncomputable abbrev dB : BVOp R (Fin 1) := FreeGr.presGen (BV.rel R) BVGen.op

/-- The operator of `BV`, with its input on `Unit`. -/
noncomputable abbrev DB : BVOp R Unit := toUnit (R := R) (dB R)

/-- **The bracket of `BV`**: the deviation of the operator from being a derivation. -/
noncomputable abbrev bB : BVOp R (Fin 2) := BV.devOf R (mB R) (dB R)

/-- **The relators vanish in `BV`.** -/
lemma relOf_eq_zero {n : ℕ} (r : BV.Rel n) : BV.relOf R (mB R) (dB R) r = 0 := by
  rw [show mB R = (GrOperadIdeal.span R (BV.rel R)).projHom.app _ (BV.μ R) from rfl,
    show dB R = (GrOperadIdeal.span R (BV.rel R)).projHom.app _ (BV.Δ R) from rfl,
    ← BV.app_relOf]
  exact ((GrOperadIdeal.span R (BV.rel R)).proj_eq_zero_iff _).2
    (GrOperadIdeal.subset_span _ ⟨r, rfl⟩)

lemma par_mB : par (R := R) false (mB R) = mB R := FreeGr.par_presGen (gp := bvPar) BVGen.mul

lemma par_dB : par (R := R) true (dB R) = dB R := FreeGr.par_presGen (gp := bvPar) BVGen.op

lemma par_DB : par (R := R) true (DB R) = DB R := by
  rw [DB, toUnit, ← map_par, par_dB]

/-- **`Δ ∘ Δ = 0`.** -/
lemma DB_DB : comp (R := R) () (DB R) (DB R) = 0 := by
  have h1 : comp (R := R) (⟨0, by omega⟩ : Fin (0 + 1 + 0)) (dB R) (dB R) = 0 := by
    have h := congrArg (map (R := R) (insertEquiv 0 0 1).symm) (relOf_eq_zero R BV.Rel.sq)
    rwa [BV.relOf, nsc, ← map_trans, Equiv.self_trans_symm, map_refl,
      map_zero (map (R := R) (insertEquiv 0 0 1).symm)] at h
  show comp (R := R) (unitFinOne.symm ⟨0, by omega⟩) (map (R := R) unitFinOne.symm (dB R))
    (map (R := R) unitFinOne.symm (dB R)) = 0
  rw [← map_comp, h1]
  exact map_zero _

/-- **The bracket is the inner derivation of the product.** -/
lemma bB_eq : bB R = innerL R (DB R) (mB R) := by
  have h0 : lcomp R (DB R) (mB R) = nsc R 0 0 (dB R) (mB R) :=
    (lcomp_eq_nsc (dB R) (mB R)).trans (map_finCongr_self _ _)
  have h1 : rcomp R (DB R) 0 (mB R) = nsc R 0 1 (mB R) (dB R) :=
    rcomp_eq_nsc (dB R) 0 1 0 rfl (mB R)
  have h2 : rcomp R (DB R) 1 (mB R) = nsc R 1 0 (mB R) (dB R) :=
    rcomp_eq_nsc (dB R) 1 0 1 rfl (mB R)
  show BV.devOf R (mB R) (dB R) = _
  rw [innerL_apply, tw_hom true (par_mB R), Bool.true_and, σ_false, one_smul, Fin.sum_univ_two,
    h0, h1, h2, BV.devOf, sub_sub]

lemma par_bB : par (R := R) true (bB R) = bB R := by
  have h := innerL_hom (DB R) (par_DB R) (par_mB R)
  rwa [← bB_eq] at h

lemma innerL_bB : innerL R (DB R) (bB R) = 0 := by
  have h := innerL_innerL (DB R) (par_DB R) (DB_DB R) (mB R)
  rwa [← bB_eq] at h

/-- **The Gerstenhaber relators vanish on the product and the bracket of `BV`.** -/
theorem ger_relOf_eq_zero {n : ℕ} (r : Ger.Rel n) : Ger.relOf R (mB R) (bB R) r = 0 := by
  cases r
  · exact relOf_eq_zero R BV.Rel.comm
  · have h := congrArg (innerL R (DB R)) (relOf_eq_zero R BV.Rel.comm)
    rw [BV.relOf, map_sub, innerL_map, ← bB_eq, map_zero] at h
    exact h
  · exact relOf_eq_zero R BV.Rel.assoc
  · exact relOf_eq_zero R BV.Rel.order
  · have h := congrArg (innerL R (DB R)) (relOf_eq_zero R BV.Rel.order)
    rw [BV.relOf, map_sub, map_sub, innerL_map] at h
    have e1 : innerL R (DB R) (A := Fin 3) (nsc R 1 0 (bB R) (mB R))
        = nsc R 1 0 (innerL R (DB R) (bB R)) (mB R)
          + nsc R 1 0 (tw (R := R) true (bB R)) (innerL R (DB R) (mB R)) :=
      innerL_nsc (DB R) (par_DB R) 1 0 (bB R) (mB R)
    have e2 : innerL R (DB R) (A := Fin 3) (nsc R 0 1 (mB R) (bB R))
        = nsc R 0 1 (innerL R (DB R) (mB R)) (bB R)
          + nsc R 0 1 (tw (R := R) true (mB R)) (innerL R (DB R) (bB R)) :=
      innerL_nsc (DB R) (par_DB R) 0 1 (mB R) (bB R)
    have e3 : innerL R (DB R) (A := Fin 3) (nsc R 1 0 (mB R) (bB R))
        = nsc R 1 0 (innerL R (DB R) (mB R)) (bB R)
          + nsc R 1 0 (tw (R := R) true (mB R)) (innerL R (DB R) (bB R)) :=
      innerL_nsc (DB R) (par_DB R) 1 0 (mB R) (bB R)
    rw [e1, e2, e3] at h
    rw [← bB_eq, innerL_bB,
      tw_hom true (par_mB R), tw_hom true (par_bB R), map_zero] at h
    simp only [Bool.true_and, σ_false, σ_true, one_smul, neg_one_smul] at h
    rw [Ger.relOf, ← neg_eq_zero, ← h]
    simp only [nsc, map_zero, map_neg, LinearMap.zero_apply, LinearMap.neg_apply, zero_add,
      add_zero]
    abel

/-- **The morphism `Ger → BV`**: the product to the product, the bracket to the deviation of the
operator. -/
noncomputable def gerToBV : GrOperadHom R (GerOp R) (BVOp R) :=
  FreeGr.presHomEquiv.symm ⟨⟨Ger.genVal (X := fun k => BVOp R (Fin k)) (mB R) (bB R), by
    intro k e
    cases e
    · exact par_mB R
    · exact par_bB R⟩, by
    rintro n _ ⟨r, rfl⟩
    rw [Ger.app_relOf, Ger.μ, Ger.β, FreeGr.homEquiv_symm_gen, FreeGr.homEquiv_symm_gen]
    exact ger_relOf_eq_zero R r⟩

lemma gerToBV_mul :
    (gerToBV R).app _ (FreeGr.presGen (Ger.rel R) GerGen.mul) = mB R := by
  rw [gerToBV, FreeGr.presHomEquiv_symm_gen]
  rfl

lemma gerToBV_br :
    (gerToBV R).app _ (FreeGr.presGen (Ger.rel R) GerGen.br) = bB R := by
  rw [gerToBV, FreeGr.presHomEquiv_symm_gen]
  rfl

/-! ## The image of `Ger` is stable under the inner derivation -/

/-- The operations of `Ger` whose image has its inner derivation in the image. -/
noncomputable def innerSub : GrSuboperad R (GerOp R) where
  sub A _ _ := ((gerToBV R).range.sub A).comap (innerL R (DB R) ∘ₗ (gerToBV R).app A)
  par_mem b x hx := by
    rw [Submodule.mem_comap, LinearMap.comp_apply, GrOperadHom.app_par,
      innerL_par _ (par_DB R)]
    exact (gerToBV R).range.par_mem _ hx
  map_mem e x hx := by
    rw [Submodule.mem_comap, LinearMap.comp_apply, GrOperadHom.app_map, innerL_map]
    exact (gerToBV R).range.map_mem e hx
  one_mem := by
    rw [Submodule.mem_comap, LinearMap.comp_apply, GrOperadHom.app_one, innerL_one]
    exact zero_mem _
  comp_mem i x y hx hy := by
    rw [Submodule.mem_comap, LinearMap.comp_apply, GrOperadHom.app_comp,
      innerL_comp _ (par_DB R)]
    refine add_mem ((gerToBV R).range.comp_mem i hx ⟨y, rfl⟩) ?_
    refine (gerToBV R).range.comp_mem i ⟨tw (R := R) true x, ?_⟩ hy
    exact GrOperadHom.app_tw _ _ _

/-- **The inner derivation of an operation of the image of `Ger` is in the image.** -/
lemma innerL_mem_range {A : Type} [Fintype A] [DecidableEq A] (q : GerOp R A) :
    ∃ q', (gerToBV R).app A q' = innerL R (DB R) ((gerToBV R).app A q) := by
  have h : q ∈ (innerSub R).sub A := FreeGr.mem_of_presGen (innerSub R) (fun k e => by
    cases e
    · show ∃ q', (gerToBV R).app _ q'
        = innerL R (DB R) ((gerToBV R).app _ (FreeGr.presGen (Ger.rel R) GerGen.mul))
      refine ⟨FreeGr.presGen (Ger.rel R) GerGen.br, ?_⟩
      rw [gerToBV_mul, gerToBV_br, bB_eq]
    · show ∃ q', (gerToBV R).app _ q'
        = innerL R (DB R) ((gerToBV R).app _ (FreeGr.presGen (Ger.rel R) GerGen.br))
      refine ⟨0, ?_⟩
      rw [gerToBV_br, innerL_bB, map_zero]) q
  exact h

/-! ## Spanning: the image of `Ger` with the operator at some inputs -/

section Span

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **The operator at the inputs of a list.** -/
noncomputable def Rl : List A → BVOp R A →ₗ[R] BVOp R A
  | [] => LinearMap.id
  | a :: l => rcomp R (DB R) a ∘ₗ Rl l

variable {R}

lemma Rl_nil (x : BVOp R A) : Rl R [] x = x := rfl

lemma Rl_cons (a : A) (l : List A) (x : BVOp R A) :
    Rl R (a :: l) x = rcomp R (DB R) a (Rl R l x) := rfl

lemma Rl_map {A' : Type} [Fintype A'] [DecidableEq A'] (e : A ≃ A') :
    ∀ (l : List A) (x : BVOp R A), map (R := R) e (Rl R l x) = Rl R (l.map e) (map (R := R) e x)
  | [], _ => rfl
  | a :: l, x => by rw [Rl_cons, List.map_cons, Rl_cons, ← Rl_map e l, rcomp_map]

lemma par_rcomp {p : Bool} {x : BVOp R A} (hx : par (R := R) p x = x) (a : A) :
    par (R := R) (!p) (rcomp R (DB R) a x) = rcomp R (DB R) a x := by
  rw [rcomp_apply, ← map_par, par_comp_hom a (Bool.xor_true p) hx (par_DB R)]

lemma par_Rl : ∀ (l : List A) {p : Bool} {x : BVOp R A}, par (R := R) p x = x →
    ∃ p', par (R := R) p' (Rl R l x) = Rl R l x
  | [], p, _, hx => ⟨p, hx⟩
  | a :: l, _, _, hx => by
    obtain ⟨p', h⟩ := par_Rl l hx
    exact ⟨!p', par_rcomp h a⟩

variable (R) in
/-- **The span of the operations of `Ger` with the operator at some inputs.** -/
noncomputable def SB (A : Type) [Fintype A] [DecidableEq A] : Submodule R (BVOp R A) :=
  Submodule.span R {y | ∃ (l : List A) (q : GerOp R A) (p : Bool),
    par (R := R) p q = q ∧ y = Rl R l ((gerToBV R).app A q)}

lemma gen_mem_SB (l : List A) {q : GerOp R A} {p : Bool} (hq : par (R := R) p q = q) :
    Rl R l ((gerToBV R).app A q) ∈ SB R A :=
  Submodule.subset_span ⟨l, q, p, hq, rfl⟩

lemma app_mem_SB (l : List A) (q : GerOp R A) : Rl R l ((gerToBV R).app A q) ∈ SB R A := by
  rw [← par_add (R := R) q, map_add, map_add]
  exact add_mem (gen_mem_SB l (par_par_self false q)) (gen_mem_SB l (par_par_self true q))

/-- A property of the generators of `SB` extends to `SB`. -/
lemma SB_le {A' : Type} [Fintype A'] [DecidableEq A'] (f : BVOp R A →ₗ[R] BVOp R A')
    (h : ∀ (l : List A) (q : GerOp R A) (p : Bool), par (R := R) p q = q →
      f (Rl R l ((gerToBV R).app A q)) ∈ SB R A') {x : BVOp R A} (hx : x ∈ SB R A) :
    f x ∈ SB R A' := by
  refine (Submodule.span_le.2 ?_ : SB R A ≤ (SB R A').comap f) hx
  rintro _ ⟨l, q, p, hq, rfl⟩
  exact h l q p hq

lemma par_mem_SB (b : Bool) {x : BVOp R A} (hx : x ∈ SB R A) :
    par (R := R) b x ∈ SB R A := by
  refine SB_le (par (R := R) b) (fun l q p hq => ?_) hx
  have hq' : par (R := R) p ((gerToBV R).app A q) = (gerToBV R).app A q := by
    rw [← GrOperadHom.app_par, hq]
  obtain ⟨p', h⟩ := par_Rl l hq'
  rw [← h, par_par]
  split_ifs
  · rw [h]
    exact gen_mem_SB l hq
  · exact zero_mem _

lemma rcomp_mem_SB (a : A) {x : BVOp R A} (hx : x ∈ SB R A) :
    rcomp R (DB R) a x ∈ SB R A :=
  SB_le _ (fun l _ _ hq => gen_mem_SB (a :: l) hq) hx

lemma Rl_mem_SB : ∀ (l : List A) {x : BVOp R A}, x ∈ SB R A → Rl R l x ∈ SB R A
  | [], _, hx => hx
  | a :: l, _, hx => rcomp_mem_SB a (Rl_mem_SB l hx)

lemma tw_mem_SB {x : BVOp R A} (hx : x ∈ SB R A) : tw (R := R) true x ∈ SB R A := by
  rw [tw_true]
  exact sub_mem (par_mem_SB false hx) (par_mem_SB true hx)

lemma map_mem_SB {A' : Type} [Fintype A'] [DecidableEq A'] (e : A ≃ A') {x : BVOp R A}
    (hx : x ∈ SB R A) : map (R := R) e x ∈ SB R A' := by
  refine SB_le (map (R := R) e) (fun l q p hq => ?_) hx
  rw [Rl_map, ← GrOperadHom.app_map]
  exact gen_mem_SB _ (by rw [← map_par, hq])

lemma lcomp_Rl : ∀ (l : List A) (x : BVOp R A),
    lcomp R (DB R) (Rl R l x) = Rl R l (lcomp R (DB R) x)
  | [], _ => rfl
  | a :: l, x => by rw [Rl_cons, lcomp_rcomp, lcomp_Rl l, Rl_cons]

lemma lcomp_mem_SB {x : BVOp R A} (hx : x ∈ SB R A) : lcomp R (DB R) x ∈ SB R A := by
  refine SB_le _ (fun l q p hq => ?_) hx
  rw [lcomp_Rl]
  refine Rl_mem_SB l ?_
  have h := innerL_apply (R := R) (DB R) ((gerToBV R).app A q)
  rw [eq_sub_iff_add_eq] at h
  rw [← h]
  obtain ⟨q', hq'⟩ := innerL_mem_range R q
  rw [← hq']
  refine add_mem (app_mem_SB ([] : List A) q') (sum_mem fun a _ => ?_)
  rw [← GrOperadHom.app_tw]
  exact app_mem_SB [a] _

lemma comp_gen_mem_SB (i : A) (q : GerOp R A) {y : BVOp R B} (hy : y ∈ SB R B) :
    comp (R := R) i ((gerToBV R).app A q) y ∈ SB R (Without A i ⊕ B) := by
  refine SB_le (comp (R := R) i ((gerToBV R).app A q)) (fun l q' p hq => ?_) hy
  have key : ∀ l : List B, comp (R := R) i ((gerToBV R).app A q)
      (Rl R l ((gerToBV R).app B q'))
        = Rl R (l.map Sum.inr) ((gerToBV R).app _ (comp (R := R) i q q')) := by
    intro l
    induction l with
    | nil => exact (GrOperadHom.app_comp _ i q q').symm
    | cons b l ih => rw [Rl_cons, ← rcomp_comp_inr, ih, List.map_cons, Rl_cons]
  rw [key]
  exact app_mem_SB _ _

lemma comp_mem_SB (i : A) {x : BVOp R A} (hx : x ∈ SB R A) {y : BVOp R B} (hy : y ∈ SB R B) :
    comp (R := R) i x y ∈ SB R (Without A i ⊕ B) := by
  have key : ∀ (l : List A) (q : GerOp R A) {y : BVOp R B}, y ∈ SB R B →
      comp (R := R) i (Rl R l ((gerToBV R).app A q)) y ∈ SB R (Without A i ⊕ B) := by
    intro l q
    induction l with
    | nil => exact fun hy => comp_gen_mem_SB i q hy
    | cons a l ih =>
      intro y hy
      by_cases hai : a = i
      · subst hai
        rw [Rl_cons, comp_rcomp_self]
        exact ih (lcomp_mem_SB hy)
      · rw [Rl_cons, ← tw_tw (R := R) true y, ← rcomp_comp_inl _ (par_DB R) hai]
        exact rcomp_mem_SB _ (ih (tw_mem_SB hy))
  refine (Submodule.span_le.2 ?_ :
    SB R A ≤ (SB R (Without A i ⊕ B)).comap ((comp (R := R) i).flip y)) hx
  rintro _ ⟨l, q, -, -, rfl⟩
  exact key l q hy

/-- `SB` is a graded suboperad. -/
noncomputable def SBsub : GrSuboperad R (BVOp R) where
  sub A _ _ := SB R A
  par_mem b _ hx := par_mem_SB b hx
  map_mem e _ hx := map_mem_SB e hx
  one_mem := by
    rw [← (gerToBV R).app_one]
    exact app_mem_SB (R := R) ([] : List Unit) (one (R := R) (P := GerOp R))
  comp_mem i _ _ hx hy := comp_mem_SB i hx hy

lemma rcomp_one (D : BVOp R Unit) : rcomp R D () (one (R := R) (P := BVOp R)) = D := by
  have he : rightUnitEquiv () = leftUnitEquiv Unit := Equiv.ext fun _ => Subsingleton.elim _ _
  rw [rcomp_apply, he, one_comp]

/-- **Every operation of `BV` is a combination of operations of `Ger` with the operator at some
inputs.** -/
theorem mem_SB (x : BVOp R A) : x ∈ SB R A := by
  refine FreeGr.mem_of_presGen (SBsub (R := R)) (fun k e => ?_) x
  cases e
  · show mB R ∈ SB R (Fin 2)
    rw [← gerToBV_mul R]
    exact app_mem_SB (R := R) ([] : List (Fin 2)) (FreeGr.presGen (Ger.rel R) GerGen.mul)
  · show dB R ∈ SB R (Fin 1)
    have h : dB R = map (R := R) unitFinOne (DB R) := by
      rw [DB, toUnit, ← map_trans, Equiv.symm_trans_self, map_refl]
    rw [h]
    refine map_mem_SB _ ?_
    rw [← rcomp_one (DB R), ← (gerToBV R).app_one]
    exact app_mem_SB [()] _

end Span

end BVGer

end Operad
