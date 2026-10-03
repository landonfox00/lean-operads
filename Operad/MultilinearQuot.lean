/-
# Multilinear maps on free modules and on quotient modules

Two general tools for defining multilinear maps, used for the Schur functor of an operad.

* **On free modules** (`ML.finsuppLift`): a multilinear map `(X →₀ R)^ι → W` is given by
  arbitrary values on tuples of basis vectors, and is determined by them (`ML.finsupp_ext`). It
  vanishes when one argument lies in a submodule `N` as soon as, the other arguments being basis
  vectors, the induced linear map in the remaining argument kills `N`
  (`ML.finsuppLift_eq_zero`).
* **On direct sums of free modules** (`ML.dsLift`): the same, the arguments being basis vectors
  of given summands (`ML.dsLift_lof_single`, `ML.ds_ext`), with the vanishing criterion for
  submodules spanned by relators of the summands (`ML.dsLift_eq_zero`).
* **On quotient modules** (`ML.liftQ`): a multilinear map `M^ι → W` vanishing whenever one
  argument lies in `N` descends to `(M ⧸ N)^ι` (`ML.liftQ_mk`). It only depends on the arguments
  modulo `N` (`ML.eq_of_sub_mem`), argument by argument, and is determined by its values on
representatives (`ML.quot_ext`).
-/
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Finsupp
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Multilinear.DirectSum

namespace Operad

namespace ML

open Function

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {W : Type*} [AddCommGroup W] [Module R W]

/-! ## Free modules -/

section Finsupp

variable {X : Type*}

/-- **Multilinear maps on free modules agree when they agree on tuples of basis vectors.** -/
theorem finsupp_ext {f g : MultilinearMap R (fun _ : ι => X →₀ R) W}
    (h : ∀ t : ι → X, f (fun i => Finsupp.single (t i) 1) = g (fun i => Finsupp.single (t i) 1)) :
    f = g := by
  classical
  ext x
  have hx : x = fun i => ∑ y ∈ (x i).support, (x i) y • Finsupp.single y (1 : R) := by
    funext i
    conv_lhs => rw [← Finsupp.sum_single (x i)]
    simp only [Finsupp.sum, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hx, MultilinearMap.map_sum_finset, MultilinearMap.map_sum_finset]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [MultilinearMap.map_smul_univ, MultilinearMap.map_smul_univ, h]

/-- **The multilinear map on free modules with given values on tuples of basis vectors.** -/
noncomputable def finsuppLift (g : (ι → X) → W) : MultilinearMap R (fun _ : ι => X →₀ R) W :=
  haveI := Classical.decEq R
  haveI := Classical.decEq X
  ((Finsupp.lift W R (ι → X) g).comp
    (PiTensorProduct.ofFinsuppEquiv' (R := R) (κ := fun _ : ι => X)).toLinearMap).compMultilinearMap
    (PiTensorProduct.tprod R)

@[simp] lemma finsuppLift_single (g : (ι → X) → W) (t : ι → X) :
    finsuppLift (R := R) g (fun i => Finsupp.single (t i) 1) = g t := by
  haveI := Classical.decEq R
  haveI := Classical.decEq X
  unfold finsuppLift
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    PiTensorProduct.ofFinsuppEquiv'_tprod_single, Finset.prod_const_one, Finsupp.lift_apply,
    Finsupp.sum_single_index, one_smul, zero_smul]

/-- **Vanishing on a submodule in one argument**: the other arguments being basis vectors, it
suffices that the induced linear map in the remaining argument kills the submodule. -/
theorem finsuppLift_eq_zero [Nonempty X] (g : (ι → X) → W) (N : Submodule R (X →₀ R))
    (hg : ∀ (t : ι → X) (i : ι),
      N ≤ LinearMap.ker (Finsupp.lift W R X fun y => g (update t i y)))
    (x : ι → X →₀ R) (i : ι) (hx : x i ∈ N) : finsuppLift (R := R) g x = 0 := by
  classical
  set m := finsuppLift (R := R) g
  -- inserting `x i` at the coordinate `i` through a linear map
  let ℓ : (X →₀ R) →ₗ[R] (X →₀ R) := Finsupp.lift (X →₀ R) R X fun _ => x i
  let F := m.compLinearMap fun j => if j = i then ℓ else LinearMap.id
  have hF : F = 0 := by
    refine finsupp_ext fun t => ?_
    have hupd : (fun j => (if j = i then ℓ else LinearMap.id) (Finsupp.single (t j) (1 : R)))
        = update (fun j => Finsupp.single (t j) (1 : R)) i (x i) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [ℓ]
      · simp [hj]
    show m _ = 0
    rw [hupd]
    have hlin : (m.toLinearMap (fun j => Finsupp.single (t j) (1 : R)) i)
        = Finsupp.lift W R X fun y => g (update t i y) := by
      refine Finsupp.lhom_ext fun y c => ?_
      rw [MultilinearMap.toLinearMap_apply, Finsupp.lift_apply, Finsupp.sum_single_index
        (by simp), ← Finsupp.smul_single_one, MultilinearMap.map_update_smul]
      congr 1
      rw [show update (fun j => Finsupp.single (t j) (1 : R)) i (Finsupp.single y 1)
          = fun j => Finsupp.single (update t i y j) 1 from by
        funext j
        by_cases hj : j = i
        · subst hj
          simp
        · simp [hj]]
      exact finsuppLift_single g _
    have := congrArg (fun L => L (x i)) hlin
    simp only [MultilinearMap.toLinearMap_apply] at this
    rw [this]
    exact hg t i hx
  obtain ⟨y₀⟩ := ‹Nonempty X›
  have hx' : x = fun j => (if j = i then ℓ else LinearMap.id)
      (update x i (Finsupp.single y₀ 1) j) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [ℓ]
    · simp [hj]
  rw [hx']
  exact congrArg (fun G : MultilinearMap R (fun _ : ι => X →₀ R) W =>
    G (update x i (Finsupp.single y₀ 1))) hF

end Finsupp


/-! ## Families of free modules, and direct sums of them -/

section FinsuppDep

variable {X : ι → Type*}

/-- **Multilinear maps on a family of free modules agree when they agree on tuples of basis
vectors.** -/
theorem finsupp_ext' {f g : MultilinearMap R (fun i => X i →₀ R) W}
    (h : ∀ t : ∀ i, X i,
      f (fun i => Finsupp.single (t i) 1) = g (fun i => Finsupp.single (t i) 1)) :
    f = g := by
  classical
  ext x
  have hx : x = fun i => ∑ y ∈ (x i).support, (x i) y • Finsupp.single y (1 : R) := by
    funext i
    conv_lhs => rw [← Finsupp.sum_single (x i)]
    simp only [Finsupp.sum, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hx, MultilinearMap.map_sum_finset, MultilinearMap.map_sum_finset]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [MultilinearMap.map_smul_univ, MultilinearMap.map_smul_univ, h]

/-- **The multilinear map on a family of free modules with given values on tuples of basis
vectors.** -/
noncomputable def finsuppLift' (g : (∀ i, X i) → W) : MultilinearMap R (fun i => X i →₀ R) W :=
  haveI := Classical.decEq R
  haveI := fun i => Classical.decEq (X i)
  ((Finsupp.lift W R (∀ i, X i) g).comp
    (PiTensorProduct.ofFinsuppEquiv' (R := R) (κ := X)).toLinearMap).compMultilinearMap
    (PiTensorProduct.tprod R)

@[simp] lemma finsuppLift'_single (g : (∀ i, X i) → W) (t : ∀ i, X i) :
    finsuppLift' (R := R) g (fun i => Finsupp.single (t i) 1) = g t := by
  haveI := Classical.decEq R
  haveI := fun i => Classical.decEq (X i)
  unfold finsuppLift'
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    PiTensorProduct.ofFinsuppEquiv'_tprod_single, Finset.prod_const_one, Finsupp.lift_apply,
    Finsupp.sum_single_index, one_smul, zero_smul]

/-- In one argument, the others being basis vectors, the multilinear map is the linear map with
the corresponding values on basis vectors. -/
lemma finsuppLift'_update (g : (∀ i, X i) → W) (t : ∀ i, X i) (i : ι) (z : X i →₀ R) :
    finsuppLift' (R := R) g (update (fun j => Finsupp.single (t j) 1) i z)
      = Finsupp.lift W R (X i) (fun y => g (update t i y)) z := by
  have h := congrArg (fun L : (X i →₀ R) →ₗ[R] W => L z)
    (show (finsuppLift' (R := R) g).toLinearMap (fun j => Finsupp.single (t j) 1) i
        = Finsupp.lift W R (X i) (fun y => g (update t i y)) from
      Finsupp.lhom_ext fun y c => by
        rw [MultilinearMap.toLinearMap_apply, Finsupp.lift_apply, Finsupp.sum_single_index
          (by simp), ← Finsupp.smul_single_one, MultilinearMap.map_update_smul]
        congr 1
        rw [show update (fun j => Finsupp.single (t j) (1 : R)) i (Finsupp.single y 1)
            = fun j => Finsupp.single (update t i y j) 1 from by
          funext j
          by_cases hj : j = i
          · subst hj
            simp
          · simp [hj]]
        exact finsuppLift'_single g _)
  simpa only [MultilinearMap.toLinearMap_apply] using h

end FinsuppDep

section DirectSum

open DirectSum

variable {κ : Type*} [DecidableEq κ] {X : κ → Type*}

/-- **The multilinear map on a direct sum of free modules** with given values on tuples of basis
vectors of given summands. -/
@[irreducible] noncomputable def dsLift (g : ∀ n : ι → κ, (∀ i, X (n i)) → W) :
    MultilinearMap R (fun _ : ι => ⨁ k, (X k →₀ R)) W :=
  MultilinearMap.fromDirectSumEquiv (R := R) (κ := fun _ : ι => κ)
    (M := fun _ k => X k →₀ R) fun n => finsuppLift' (X := fun i => X (n i)) (g n)

@[simp] lemma dsLift_lof (g : ∀ n : ι → κ, (∀ i, X (n i)) → W) (n : ι → κ)
    (y : ∀ i, X (n i) →₀ R) :
    dsLift (R := R) g (fun i => lof R κ (fun k => X k →₀ R) (n i) (y i))
      = finsuppLift' (R := R) (X := fun i => X (n i)) (g n) y := by
  unfold dsLift
  exact MultilinearMap.fromDirectSumEquiv_lof (R := R) (κ := fun _ : ι => κ)
    (M := fun _ k => X k →₀ R) _ n y

lemma dsLift_lof_single (g : ∀ n : ι → κ, (∀ i, X (n i)) → W) (n : ι → κ) (t : ∀ i, X (n i)) :
    dsLift (R := R) g (fun i => lof R κ (fun k => X k →₀ R) (n i) (Finsupp.single (t i) 1))
      = g n t := by
  rw [dsLift_lof, finsuppLift'_single]

/-- **Multilinear maps on a direct sum of free modules agree when they agree on tuples of basis
vectors of given summands.** -/
theorem ds_ext {f g : MultilinearMap R (fun _ : ι => ⨁ k, (X k →₀ R)) W}
    (h : ∀ (n : ι → κ) (t : ∀ i, X (n i)),
      f (fun i => lof R κ (fun k => X k →₀ R) (n i) (Finsupp.single (t i) 1))
        = g (fun i => lof R κ (fun k => X k →₀ R) (n i) (Finsupp.single (t i) 1))) :
    f = g :=
  MultilinearMap.directSum_ext fun n => finsupp_ext' fun t => h n t

omit [Fintype ι] in
lemma update_lof (n : ι → κ) (y : ∀ j, X (n j) →₀ R) (i : ι) (z : X (n i) →₀ R) :
    update (fun j => lof R κ (fun k => X k →₀ R) (n j) (y j)) i
        (lof R κ (fun k => X k →₀ R) (n i) z)
      = fun j => lof R κ (fun k => X k →₀ R) (n j) (update y i z j) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

/-- In one argument lying in its summand, the others being basis vectors of theirs, the
multilinear map is the linear map with the corresponding values on basis vectors. -/
lemma dsLift_update (g : ∀ n : ι → κ, (∀ i, X (n i)) → W) (n : ι → κ) (t : ∀ i, X (n i))
    (i : ι) (z : X (n i) →₀ R) :
    dsLift (R := R) g (update (fun j => lof R κ (fun k => X k →₀ R) (n j)
      (Finsupp.single (t j) 1)) i (lof R κ (fun k => X k →₀ R) (n i) z))
      = Finsupp.lift W R (X (n i)) (fun y => g n (update t i y)) z := by
  rw [update_lof, dsLift_lof]
  exact finsuppLift'_update (X := fun i => X (n i)) (g n) t i z

/-- **Vanishing on generated submodules**: the multilinear map vanishes when one argument lies in
the span of relators of the summands, as soon as, the other arguments being basis vectors, the
induced linear map in the remaining argument kills the relators. -/
theorem dsLift_eq_zero (g : ∀ n : ι → κ, (∀ i, X (n i)) → W) (S : ∀ k, Set (X k →₀ R))
    (hg : ∀ (n : ι → κ) (t : ∀ i, X (n i)) (i : ι),
      S (n i) ⊆ LinearMap.ker (Finsupp.lift W R (X (n i)) fun y => g n (update t i y)))
    (x : ι → ⨁ k, (X k →₀ R)) (i : ι)
    (hx : x i ∈ Submodule.span R (⋃ k, lof R κ (fun k => X k →₀ R) k '' S k)) :
    dsLift (R := R) g x = 0 := by
  classical
  have key : ∀ k (ρ : X k →₀ R), ρ ∈ S k → ∀ x : ι → ⨁ k, (X k →₀ R),
      dsLift (R := R) g (update x i (lof R κ (fun k => X k →₀ R) k ρ)) = 0 := by
    intro k ρ hρ x
    rcases isEmpty_or_nonempty (X k) with hX | ⟨⟨y₀⟩⟩
    · rw [show ρ = 0 from Subsingleton.elim _ _, map_zero, MultilinearMap.map_update_zero]
    let φ : (⨁ k, (X k →₀ R)) →ₗ[R] R :=
      (Finsupp.lapply y₀).comp (component R κ (fun k => X k →₀ R) k)
    let ℓ : (⨁ k, (X k →₀ R)) →ₗ[R] (⨁ k, (X k →₀ R)) :=
      LinearMap.smulRight φ (lof R κ (fun k => X k →₀ R) k ρ)
    let F : MultilinearMap R (fun _ : ι => ⨁ k, (X k →₀ R)) W :=
      (dsLift (R := R) g).compLinearMap fun j => if j = i then ℓ else LinearMap.id
    have hFapp : ∀ z, F z = dsLift (R := R) g (update z i (ℓ (z i))) := by
      intro z
      simp only [F, MultilinearMap.compLinearMap_apply]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj]
    have hF : F = 0 := by
      refine MultilinearMap.directSum_ext fun n => ?_
      refine finsupp_ext' fun t => ?_
      show F (fun j => lof R κ (fun k => X k →₀ R) (n j) (Finsupp.single (t j) 1)) = 0
      rw [hFapp]
      by_cases hk : n i = k
      · subst hk
        rw [show ℓ (lof R κ (fun k => X k →₀ R) (n i) (Finsupp.single (t i) 1))
            = (Finsupp.single (t i) (1 : R)) y₀ • lof R κ (fun k => X k →₀ R) (n i) ρ by
              simp [ℓ, φ],
          ← map_smul, dsLift_update, map_smul, LinearMap.mem_ker.1 (hg n t i hρ), smul_zero]
      · rw [show ℓ (lof R κ (fun k => X k →₀ R) (n i) (Finsupp.single (t i) 1)) = 0 by
              simp [ℓ, φ, component.of, hk],
          MultilinearMap.map_update_zero]
    have hℓ : ℓ (lof R κ (fun k => X k →₀ R) k (Finsupp.single y₀ 1))
        = lof R κ (fun k => X k →₀ R) k ρ := by
      simp [ℓ, φ]
    have h := hFapp (update x i (lof R κ (fun k => X k →₀ R) k (Finsupp.single y₀ 1)))
    rw [hF, MultilinearMap.zero_apply, update_idem, update_self, hℓ] at h
    exact h.symm
  have h := Submodule.span_induction
    (p := fun z _ => ∀ x : ι → ⨁ k, (X k →₀ R), dsLift (R := R) g (update x i z) = 0)
    (fun z hz x => by
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hz
      obtain ⟨ρ, hρ, rfl⟩ := hk
      exact key k ρ hρ x)
    (fun x => MultilinearMap.map_update_zero _ _ _)
    (fun z z' _ _ hz hz' x => by rw [MultilinearMap.map_update_add, hz, hz', add_zero])
    (fun c z _ hz x => by rw [MultilinearMap.map_update_smul, hz, smul_zero]) hx
  simpa using h x

end DirectSum

/-! ## Quotient modules -/

section Quot

variable {M : Type*} [AddCommGroup M] [Module R M] (N : Submodule R M)

/-- **A multilinear map vanishing on `N` in each argument only depends on its arguments modulo
`N`.** -/
theorem eq_of_sub_mem (f : MultilinearMap R (fun _ : ι => M) W)
    (hf : ∀ (x : ι → M) (i : ι), x i ∈ N → f x = 0) (x y : ι → M)
    (h : ∀ i, x i - y i ∈ N) : f x = f y := by
  suffices key : ∀ s : Finset ι, ∀ x y : ι → M, (∀ i, x i - y i ∈ N) →
      (∀ i ∉ s, x i = y i) → f x = f y from
    key Finset.univ x y h fun i hi => absurd (Finset.mem_univ i) hi
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro x y _ hs
    exact congrArg f (funext fun i => hs i (Finset.notMem_empty i))
  | insert j s hj ih =>
    intro x y hxy hs
    have h1 : f (update x j (y j)) = f y := by
      refine ih _ _ (fun i => ?_) (fun i hi => ?_)
      · by_cases hij : i = j
        · subst hij
          simp
        · rw [update_of_ne hij]
          exact hxy i
      · by_cases hij : i = j
        · subst hij
          simp
        · rw [update_of_ne hij]
          exact hs i (by simp [hij, hi])
    have h2 : f x - f (update x j (y j)) = 0 := by
      rw [← hf (update x j (x j - y j)) j (by simpa using hxy j),
        MultilinearMap.map_update_sub, update_eq_self]
    rw [← h1, ← sub_eq_zero, h2]

/-- A representative of a class. -/
noncomputable def rep (q : M ⧸ N) : M := Function.surjInv (Submodule.mkQ_surjective N) q

lemma mkQ_rep (q : M ⧸ N) : N.mkQ (rep N q) = q :=
  Function.surjInv_eq (Submodule.mkQ_surjective N) q

omit [Fintype ι] [DecidableEq ι] in
/-- **Multilinear maps on a quotient module agree when they agree on representatives.** -/
theorem quot_ext {f g : MultilinearMap R (fun _ : ι => M ⧸ N) W}
    (h : ∀ x : ι → M, f (fun i => N.mkQ (x i)) = g (fun i => N.mkQ (x i))) : f = g := by
  ext y
  have hy : y = fun i => N.mkQ (rep N (y i)) := funext fun i => (mkQ_rep N (y i)).symm
  rw [hy]
  exact h _

lemma rep_add_sub_mem (a b : M ⧸ N) : rep N (a + b) - (rep N a + rep N b) ∈ N := by
  rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_add]
  simp only [← Submodule.mkQ_apply, mkQ_rep, sub_self]

lemma rep_smul_sub_mem (c : R) (a : M ⧸ N) : rep N (c • a) - c • rep N a ∈ N := by
  rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
  simp only [← Submodule.mkQ_apply, mkQ_rep, sub_self]

lemma rep_mkQ_sub_mem (x : M) : rep N (N.mkQ x) - x ∈ N := by
  rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
  simp only [← Submodule.mkQ_apply, mkQ_rep, sub_self]

/-- **A multilinear map vanishing on `N` in each argument descends to the quotient.** -/
noncomputable def liftQ (f : MultilinearMap R (fun _ : ι => M) W)
    (hf : ∀ (x : ι → M) (i : ι), x i ∈ N → f x = 0) :
    MultilinearMap R (fun _ : ι => M ⧸ N) W where
  toFun q := f fun i => rep N (q i)
  map_update_add' q i a b := by
    have e : ∀ c : M ⧸ N, (fun j => rep N (update q i c j)) = update (fun j => rep N (q j)) i
        (rep N c) := fun c => by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj]
    rw [e, e, e, ← MultilinearMap.map_update_add]
    refine eq_of_sub_mem N f hf _ _ fun j => ?_
    by_cases hj : j = i
    · subst hj
      simpa using rep_add_sub_mem N a b
    · simp [hj]
  map_update_smul' q i c a := by
    have e : ∀ c : M ⧸ N, (fun j => rep N (update q i c j)) = update (fun j => rep N (q j)) i
        (rep N c) := fun c => by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj]
    rw [e, e, ← MultilinearMap.map_update_smul]
    refine eq_of_sub_mem N f hf _ _ fun j => ?_
    by_cases hj : j = i
    · subst hj
      simpa using rep_smul_sub_mem N c a
    · simp [hj]

lemma liftQ_mkQ (f : MultilinearMap R (fun _ : ι => M) W)
    (hf : ∀ (x : ι → M) (i : ι), x i ∈ N → f x = 0) (x : ι → M) :
    liftQ N f hf (fun i => N.mkQ (x i)) = f x :=
  eq_of_sub_mem N f hf _ _ fun i => rep_mkQ_sub_mem N (x i)

@[simp] lemma liftQ_mk (f : MultilinearMap R (fun _ : ι => M) W)
    (hf : ∀ (x : ι → M) (i : ι), x i ∈ N → f x = 0) (x : ι → M) :
    liftQ N f hf (fun i => Submodule.Quotient.mk (x i)) = f x :=
  liftQ_mkQ N f hf x

end Quot

end ML

end Operad
