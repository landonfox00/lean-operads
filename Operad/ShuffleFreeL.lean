/-
# The free operad on a linear species is a free shuffle operad

Step one of the bridge between symmetric and shuffle operads for presentations by a linear
species (Dotsenko–Khoroshkin). Let `V` be a linear species over a commutative ring `R` and
`b k : Module.Basis (B k) R (V (Fin k))` a basis of each `V (Fin k)`, with no basis vectors in
arity zero (`[IsEmpty (B 0)]`, equivalently `V (Fin 0) = 0`). Forgetting the action of the
symmetric groups, the free operad `FreeL R V` is the free shuffle operad `FreeSh R B` on the basis.

* **The operad presented by a basis** (`Operad.FreeL.BPres`): the free operad on the basis vectors
  modulo the relators `σ · β = (σ · b β)` written in the basis (`Operad.FreeL.basisRel`). It is
  isomorphic to `FreeL R V` as a symmetric operad (`Operad.FreeL.toBP`, `Operad.FreeL.fromBP`,
  `Operad.FreeL.fromBP_comp_toBP`, `Operad.FreeL.toBP_comp_fromBP`), for every basis, arity zero
  included.
* **The comparison** (`Operad.FreeL.toFreeSh`, `Operad.FreeL.ofFreeSh`): mutually inverse
  morphisms of shuffle operads between `Shuf (FreeL R V)` and `FreeSh R B`
  (`Operad.FreeL.toFreeSh_comp_ofFreeSh`, `Operad.FreeL.ofFreeSh_comp_toFreeSh`). A generator goes
  to its expansion in the basis (`Operad.FreeL.toFreeSh_ι`), so the generator of `b k β` goes to
  the shuffle generator `genM β` (`Operad.FreeL.toFreeSh_ι_basis`), and back
  (`Operad.FreeL.ofFreeSh_genM`). The route: `Operad.FreeSet.presToSh` presents `BPres` as the
  free shuffle operad on the relabelled basis vectors `B k × Perm (Fin k)` modulo the sorted
  relators; taking coordinates (`Operad.FreeL.coordSh`, a relabelled basis vector `(β, σ)` going
  to `σ⁻¹ · b β` in the basis) kills them, and the two composites are identities by the uniqueness
  parts of the universal properties (`Operad.FreeSh.hom_ext`,
  `Operad.SymOperadIdeal.shuffle_hom_ext`).
* **The arity-wise equivalence** `FreeL R V A ≃ₗ[R] FreeSh R B A` on every finite linear order
  (`Operad.FreeL.shuffleEquiv`), and **the shuffle-monomial basis**
  (`Operad.FreeL.shuffleBasis`, indexed by `SMono B (Finset.range (Fintype.card A))`), with the
  dimension the number of monomials when it is finite (`Operad.FreeL.finrank_eq_card`).
* **Generators of arity two** (`Operad.FreeL.binBasis`): when `B = BinGen G`, for instance the
  basis `Operad.FreeL.binBasisOf` of a species concentrated in arity two with `V (Fin 2)` free on
  `G`, the basis is indexed by the binary shuffle trees `Operad.LTree.monomials`
  (`Operad.LTree.binMonoEquiv`), and the dimension in arity `n + 1` is `(2n - 1)!! |G|ⁿ`
  (`Operad.FreeL.finrank_eq_doubleFactorial`).
* `Operad.ShuffleOperadHom.ker`: the kernel of a morphism of shuffle operads, an ideal; a
  morphism killing generators kills the ideal they generate
  (`Operad.ShuffleOperadHom.app_eq_zero_of_mem_span`).
-/
import Operad.FreeSpecies
import Operad.ShuffleFreeBin

universe u v w

namespace Operad

open Sym STree

/-! ## Kernels of morphisms of shuffle operads -/

namespace ShuffleOperadHom

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [LinearOrder A] → Type v}
  [∀ (A : Type) [Fintype A] [LinearOrder A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [LinearOrder A], Module R (P A)] [ShuffleOperad R P]
  {Q : (A : Type) → [Fintype A] → [LinearOrder A] → Type w}
  [∀ (A : Type) [Fintype A] [LinearOrder A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [LinearOrder A], Module R (Q A)] [ShuffleOperad R Q]

/-- **The kernel of a morphism of shuffle operads**, an ideal. -/
def ker (φ : ShuffleOperadHom R P Q) : ShuffleOperadIdeal R P where
  sub A _ _ := LinearMap.ker (φ.app A)
  map_mem e := fun {x} hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [φ.app_map, hx, map_zero]
  comp_mem_left i e he := fun {x} y hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [φ.app_comp, hx, map_zero, LinearMap.zero_apply]
  comp_mem_right i e he := fun x {y} hy => by
    rw [LinearMap.mem_ker] at hy ⊢
    rw [φ.app_comp, hy, map_zero]

/-- **A morphism killing generators kills the shuffle ideal they generate.** -/
lemma app_eq_zero_of_mem_span (φ : ShuffleOperadHom R P Q)
    {r : ∀ (A : Type) [Fintype A] [LinearOrder A], Set (P A)}
    (hφ : ∀ (A : Type) [Fintype A] [LinearOrder A], ∀ x ∈ r A, φ.app A x = 0)
    {A : Type} [Fintype A] [LinearOrder A] {x : P A}
    (hx : x ∈ (ShuffleOperadIdeal.span R r).sub A) :
    φ.app A x = 0 :=
  LinearMap.mem_ker.1 (ShuffleOperadIdeal.span_le (I := φ.ker).2
    (fun A _ _ y hy => LinearMap.mem_ker.2 (hφ A y hy)) A hx)

end ShuffleOperadHom

/-! ## Binary shuffle trees as shuffle monomials on binary generators -/

namespace LTree

variable {G : Type w}

/-- **A binary shuffle tree as a shuffle tree** on the binary generators decorating its vertices. -/
def toBinSTree : LTree G → STree (BinGen G)
  | leaf a => STree.leaf a
  | node e l r => STree.node (BinGen.op e) ![toBinSTree l, toBinSTree r]

/-- **A shuffle tree on binary generators as a binary tree.** -/
def ofBinSTree : STree (BinGen G) → LTree G
  | STree.leaf a => leaf a
  | STree.node (BinGen.op g) c => node g (ofBinSTree (c 0)) (ofBinSTree (c 1))

lemma ofBinSTree_toBinSTree : ∀ t : LTree G, ofBinSTree (toBinSTree t) = t
  | leaf _ => rfl
  | node e l r => by
    show node e (ofBinSTree (toBinSTree l)) (ofBinSTree (toBinSTree r)) = node e l r
    rw [ofBinSTree_toBinSTree l, ofBinSTree_toBinSTree r]

lemma toBinSTree_ofBinSTree : ∀ m : STree (BinGen G), toBinSTree (ofBinSTree m) = m
  | STree.leaf _ => rfl
  | STree.node (BinGen.op g) c => by
    show STree.node (BinGen.op g) ![toBinSTree (ofBinSTree (c 0)), toBinSTree (ofBinSTree (c 1))] =
      STree.node (BinGen.op g) c
    rw [toBinSTree_ofBinSTree (c 0), toBinSTree_ofBinSTree (c 1)]
    congr 1
    funext j
    fin_cases j <;> rfl

lemma labels_toBinSTree : ∀ t : LTree G, (toBinSTree t).labels = (t.labels : Multiset ℕ)
  | leaf _ => rfl
  | node e l r => by
    show (STree.node (BinGen.op e) ![toBinSTree l, toBinSTree r]).labels = _
    rw [STree.labels_node, Fin.sum_univ_two, labels_node, ← Multiset.coe_add]
    exact congrArg₂ (· + ·) (labels_toBinSTree l) (labels_toBinSTree r)

lemma first_toBinSTree : ∀ t : LTree G, t.IsShuffle → (toBinSTree t).first = t.minLabel
  | leaf _, _ => rfl
  | node e l r, h => by
    show (STree.node (BinGen.op e) ![toBinSTree l, toBinSTree r]).first = _
    rw [STree.first_node _ _ (by omega), minLabel_node_of_shuffle h]
    exact first_toBinSTree l h.2.1

lemma isShuffle_toBinSTree : ∀ t : LTree G, t.IsShuffle → (toBinSTree t).IsShuffle
  | leaf _, _ => trivial
  | node e l r, h => by
    refine ⟨by omega, fun i => ?_, Fin.strictMono_iff_lt_succ.2 fun i => ?_⟩
    · fin_cases i
      · exact isShuffle_toBinSTree l h.2.1
      · exact isShuffle_toBinSTree r h.2.2
    · fin_cases i
      show (toBinSTree l).first < (toBinSTree r).first
      rw [first_toBinSTree l h.2.1, first_toBinSTree r h.2.2]
      exact h.1

lemma isShuffle_of_toBinSTree : ∀ t : LTree G, (toBinSTree t).IsShuffle → t.IsShuffle
  | leaf _, _ => trivial
  | node e l r, h => by
    have hl := isShuffle_of_toBinSTree l (h.child 0)
    have hr := isShuffle_of_toBinSTree r (h.child 1)
    refine ⟨?_, hl, hr⟩
    have := h.mono (show (0 : Fin 2) < 1 by decide)
    change (toBinSTree l).first < (toBinSTree r).first at this
    rwa [first_toBinSTree l hl, first_toBinSTree r hr] at this

/-- **The binary shuffle monomials are the shuffle monomials on binary generators.** -/
def binMonoEquiv [Fintype G] [DecidableEq G] (n : ℕ) :
    {t // t ∈ monomials (E := G) n} ≃ SMono (BinGen G) (Finset.range n) where
  toFun t := ⟨toBinSTree t.1, isShuffle_toBinSTree _ ((mem_monomials n t.1).1 t.2).1, by
    rw [labels_toBinSTree, Finset.range_val, ← Multiset.coe_range]
    exact Multiset.coe_eq_coe.2 ((mem_monomials n t.1).1 t.2).2⟩
  invFun m := ⟨ofBinSTree m.1, (mem_monomials n _).2 ⟨isShuffle_of_toBinSTree _ (by
      rw [toBinSTree_ofBinSTree]
      exact m.isShuffle), by
    have h1 : ((ofBinSTree m.1).labels : Multiset ℕ) = Multiset.range n := by
      rw [← labels_toBinSTree, toBinSTree_ofBinSTree]
      exact m.labels_eq
    exact Multiset.coe_eq_coe.1 (h1.trans (Multiset.coe_range n).symm)⟩⟩
  left_inv t := Subtype.ext (ofBinSTree_toBinSTree t.1)
  right_inv m := Subtype.ext (toBinSTree_ofBinSTree m.1)

end LTree

namespace FreeL

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [SymSpecies R V]
  {B : ℕ → Type w} (b : ∀ k, Module.Basis (B k) R (V (Fin k)))

/-! ## The operad presented by a basis -/

/-- **A vector in the basis generators**: a vector of `V (Fin k)` written in the basis `b k`, each
basis vector replaced by its generator in the free operad on the basis. -/
noncomputable def expSym (k : ℕ) : V (Fin k) →ₗ[R] Lin R (FreeSet B) (Fin k) :=
  (b k).constr R fun β => Finsupp.single (Pres.gen β) 1

omit [SymSpecies R V] in
@[simp] lemma expSym_basis {k : ℕ} (β : B k) :
    expSym b k (b k β) = Finsupp.single (Pres.gen β) 1 :=
  (b k).constr_basis R _ β

omit [SymSpecies R V] in
lemma map_single_gen {n : ℕ} (τ : Equiv.Perm (Fin n)) (β : B n) :
    SymOperad.map (R := R) (P := Lin R (FreeSet B)) τ (Finsupp.single (Pres.gen β) (1 : R)) =
      Finsupp.single (SetOperad.map τ (Pres.gen β)) 1 :=
  Lin.mapL_single _ _ _

/-- **The basis relators**: a basis generator relabelled along a permutation is the relabelled
basis vector, written in the basis. -/
def basisRel (n : ℕ) : Set (Lin R (FreeSet B) (Fin n)) :=
  {x | ∃ (σ : Equiv.Perm (Fin n)) (β : B n), x = Finsupp.single (SetOperad.map σ (Pres.gen β)) 1 -
    expSym b n (SymSpecies.map (R := R) σ (b n β))}

/-- **The operad presented by a basis**: the free operad on the basis vectors, modulo the action
of the symmetric groups written in the basis. -/
abbrev BPres := (SymOperadIdeal.span R (basisRel b)).Quot

lemma proj_single_map (n : ℕ) (σ : Equiv.Perm (Fin n)) (β : B n) :
    (SymOperadIdeal.span R (basisRel b)).proj (Fin n)
        (Finsupp.single (SetOperad.map σ (Pres.gen β)) 1) =
      (SymOperadIdeal.span R (basisRel b)).proj (Fin n)
        (expSym b n (SymSpecies.map (R := R) σ (b n β))) := by
  rw [← sub_eq_zero, ← map_sub, SymOperadIdeal.proj_eq_zero_iff]
  exact SymOperadIdeal.subset_span n ⟨σ, β, rfl⟩

lemma proj_expSym_map (n : ℕ) (σ : Equiv.Perm (Fin n)) (v : V (Fin n)) :
    (SymOperadIdeal.span R (basisRel b)).proj (Fin n) (expSym b n (SymSpecies.map (R := R) σ v)) =
      SymOperad.map (R := R) σ
        ((SymOperadIdeal.span R (basisRel b)).proj (Fin n) (expSym b n v)) := by
  set I := SymOperadIdeal.span R (basisRel b)
  have h : I.proj (Fin n) ∘ₗ expSym b n ∘ₗ SymSpecies.map (R := R) σ =
      SymOperad.map (R := R) σ ∘ₗ I.proj (Fin n) ∘ₗ expSym b n := by
    refine (b n).ext fun β => ?_
    simp only [LinearMap.comp_apply, expSym_basis]
    rw [← proj_single_map, ← SymOperadIdeal.projHom_app, ← SymOperadIdeal.projHom_app,
      ← SymOperadHom.app_map]
    congr 1
    exact (Lin.mapL_single _ _ _).symm
  exact LinearMap.congr_fun h v

/-! ## The comparison with the operad presented by a basis -/

/-- The generator values of the comparison morphism: a vector, written in the basis. -/
noncomputable def genVal (n : ℕ) (v : SpGen (UndSp R V) n) : Und R (BPres b) (Fin n) :=
  Und.of R (BPres b) ((SymOperadIdeal.span R (basisRel b)).proj (Fin n) (expSym b n v))

lemma respects_genVal : Pres.Respects (spRel (UndSp R V)) (genVal b) :=
  (respects_spRel_iff (X := UndSp R V) _).2 fun n σ v => proj_expSym_map b n σ v

/-- The comparison morphism, before the linearity relations. -/
noncomputable def toBPLin : SymOperadHom R (Lin R (FreeSp (UndSp R V))) (BPres b) :=
  (Pres.lift (genVal b) (respects_genVal b)).linExtend R

lemma toBPLin_gen {n : ℕ} (v : V (Fin n)) :
    (toBPLin b).app (Fin n) (linGen R V v) =
      (SymOperadIdeal.span R (basisRel b)).proj (Fin n) (expSym b n v) := by
  show Finsupp.lift _ R _ _ (Finsupp.single _ 1) = _
  simp
  rfl

lemma toBPLin_kills (n : ℕ) : ∀ x ∈ linRel R V n, (toBPLin b).app (Fin n) x = 0 := by
  rintro x (⟨v, w, rfl⟩ | ⟨c, v, rfl⟩)
  · rw [map_sub, map_sub, toBPLin_gen, toBPLin_gen, toBPLin_gen, map_add, map_add]
    abel
  · rw [map_sub, map_smul, toBPLin_gen, toBPLin_gen, map_smul, map_smul, sub_self]

/-- **The comparison morphism** from the free operad on a linear species to the operad presented
by a basis: a generator goes to its expansion in the basis. -/
noncomputable def toBP : SymOperadHom R (FreeL R V) (BPres b) :=
  (SymOperadIdeal.span R (linRel R V)).liftHom (toBPLin b) fun _ _ _ _ hx =>
    SymOperadIdeal.app_eq_zero_of_mem_span _ (toBPLin_kills b) hx

/-- The inverse comparison, before the basis relators. -/
noncomputable def fromBPLin : SymOperadHom R (Lin R (FreeSet B)) (FreeL R V) :=
  (FreeSet.homEquiv.symm fun n β => Und.of R (FreeL R V) ((ι R V).app (Fin n) (b n β))).linExtend R

lemma fromBPLin_gen {n : ℕ} (β : B n) :
    (fromBPLin b).app (Fin n) (Finsupp.single (Pres.gen β) 1) = (ι R V).app (Fin n) (b n β) := by
  show Finsupp.lift _ R _ _ (Finsupp.single _ 1) = _
  simp
  rfl

lemma fromBPLin_expSym {n : ℕ} (v : V (Fin n)) :
    (fromBPLin b).app (Fin n) (expSym b n v) = (ι R V).app (Fin n) v := by
  have h : (fromBPLin b).app (Fin n) ∘ₗ expSym b n = (ι R V).app (Fin n) :=
    (b n).ext fun β => by
      rw [LinearMap.comp_apply, expSym_basis]
      exact fromBPLin_gen b β
  exact LinearMap.congr_fun h v

lemma fromBPLin_kills (n : ℕ) : ∀ x ∈ basisRel b n, (fromBPLin b).app (Fin n) x = 0 := by
  rintro x ⟨σ, β, rfl⟩
  rw [map_sub, fromBPLin_expSym, sub_eq_zero, (ι R V).app_map, ← fromBPLin_expSym, expSym_basis]
  refine Eq.trans ?_ ((fromBPLin b).app_map σ _)
  congr 1
  exact (Lin.mapL_single _ _ _).symm

/-- **The inverse comparison**: a basis generator goes to the generator of its basis vector. -/
noncomputable def fromBP : SymOperadHom R (BPres b) (FreeL R V) :=
  (SymOperadIdeal.span R (basisRel b)).liftHom (fromBPLin b) fun _ _ _ _ hx =>
    SymOperadIdeal.app_eq_zero_of_mem_span _ (fromBPLin_kills b) hx

lemma ι_app_fin {n : ℕ} (v : V (Fin n)) :
    (ι R V).app (Fin n) v = (SymOperadIdeal.span R (linRel R V)).proj (Fin n) (linGen R V v) := by
  rw [ι_app, FreeSp.ι_app_fin]
  rfl

theorem fromBP_comp_toBP : (fromBP b).comp (toBP b) = SymOperadHom.id :=
  presLin_hom_ext fun n v => by
    show (fromBP b).app _ ((toBPLin b).app _ (linGen R V v)) = _
    rw [toBPLin_gen]
    show (fromBPLin b).app _ (expSym b n v) = _
    rw [fromBPLin_expSym, ι_app_fin]
    rfl

theorem toBP_comp_fromBP : (toBP b).comp (fromBP b) = SymOperadHom.id :=
  presLin_hom_ext fun n β => by
    show (toBP b).app _ ((fromBPLin b).app _ (Finsupp.single (Pres.gen β) 1)) = _
    rw [fromBPLin_gen, ι_app_fin]
    show (toBPLin b).app _ (linGen R V (b n β)) = _
    rw [toBPLin_gen, expSym_basis]
    rfl

/-! ## The free shuffle operad on the basis -/

section Shuffle

variable [IsEmpty (B 0)]

omit [CommRing R] [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [SymSpecies R V] in
/-- Without basis vectors in arity zero, every basis vector has positive arity. -/
lemma pos_of_basis {k : ℕ} (β : B k) : 0 < k :=
  Nat.pos_of_ne_zero fun h => by
    subst h
    exact isEmptyElim β

/-- **A vector in the shuffle generators**: a vector of `V (Fin k)` written in the basis `b k`, each
basis vector replaced by its generator in the free shuffle operad on the basis. -/
noncomputable def expSh (k : ℕ) : V (Fin k) →ₗ[R] FreeSh R B (Fin k) :=
  (b k).constr R fun β => Finsupp.single (FreeSh.genM (pos_of_basis β) β) 1

omit [SymSpecies R V] in
@[simp] lemma expSh_basis {k : ℕ} (β : B k) :
    expSh b k (b k β) = Finsupp.single (FreeSh.genM (pos_of_basis β) β) 1 :=
  (b k).constr_basis R _ β

/-- **The coordinates of the relabelled generators**: a basis vector with a permutation `σ` of its
inputs goes to the basis vector relabelled by `σ⁻¹`, written in the basis. -/
noncomputable def coordSh : ShuffleOperadHom R (FreeSh R (SGen B)) (FreeSh R B) :=
  FreeSh.lift R (FreeSh R B) fun k g => expSh b k (SymSpecies.map (R := R) g.2.symm (b k g.1))

lemma coordSh_toSh_map (n : ℕ) (τ : Equiv.Perm (Fin n)) (v : V (Fin n)) :
    (coordSh b).app (Fin n) ((FreeSet.toSh R B).app (Fin n)
      (SymOperad.map (R := R) τ (expSym b n v))) = expSh b n (SymSpecies.map (R := R) τ v) := by
  have h : (coordSh b).app (Fin n) ∘ₗ (FreeSet.toSh R B).app (Fin n) ∘ₗ
      SymOperad.map (R := R) τ ∘ₗ expSym b n = expSh b n ∘ₗ SymSpecies.map (R := R) τ :=
    (b n).ext fun β => by
      simp only [LinearMap.comp_apply, expSym_basis]
      erw [map_single_gen]
      rw [FreeSet.toSh_gen R (pos_of_basis β), coordSh, FreeSh.lift_gen, Equiv.symm_symm]
  exact LinearMap.congr_fun h v

lemma coordSh_toSh (n : ℕ) (v : V (Fin n)) :
    (coordSh b).app (Fin n) ((FreeSet.toSh R B).app (Fin n) (expSym b n v)) = expSh b n v := by
  have h := coordSh_toSh_map b n (Equiv.refl _) v
  rwa [SymOperad.map_refl, SymSpecies.map_refl] at h

lemma coordSh_kills (A : Type) [Fintype A] [LinearOrder A] :
    ∀ y ∈ FreeSet.shuffleRel R (basisRel b) A, (coordSh b).app A y = 0 := by
  rintro _ ⟨_, ⟨n, e, _, ⟨σ, β, rfl⟩, rfl⟩, rfl⟩
  let o : Fin n ≃o A := FreeSh.isoOfCard (by rw [Fintype.card_congr e])
  let τ : Equiv.Perm (Fin n) := e.trans o.symm.toEquiv
  have he : SymOperad.map (R := R) e (Finsupp.single (SetOperad.map σ (Pres.gen β)) 1 -
      expSym b n (SymSpecies.map (R := R) σ (b n β))) =
      ShuffleOperad.map (R := R) (P := Shuf (Lin R (FreeSet B))) o
        (SymOperad.map (R := R) τ (SymOperad.map (R := R) σ (expSym b n (b n β)) -
          expSym b n (SymSpecies.map (R := R) σ (b n β)))) := by
    show _ = SymOperad.map (R := R) o.toEquiv _
    rw [SymOperad.map_map', expSym_basis, map_single_gen]
    exact SymOperad.map_congr' (fun a => by simp [τ]) _
  have h1 : (coordSh b).app (Fin n) ((FreeSet.toSh R B).app (Fin n) (SymOperad.map (R := R) τ
      (SymOperad.map (R := R) σ (expSym b n (b n β))))) =
      expSh b n (SymSpecies.map (R := R) τ (SymSpecies.map (R := R) σ (b n β))) := by
    rw [SymOperad.map_map', coordSh_toSh_map, SymSpecies.map_trans]
  have hz : (coordSh b).app (Fin n) ((FreeSet.toSh R B).app (Fin n) (SymOperad.map (R := R) τ
      (SymOperad.map (R := R) σ (expSym b n (b n β)) -
        expSym b n (SymSpecies.map (R := R) σ (b n β))))) = 0 := by
    have := map_sub ((coordSh b).app (Fin n) ∘ₗ (FreeSet.toSh R B).app (Fin n) ∘ₗ
      SymOperad.map (R := R) τ) (SymOperad.map (R := R) σ (expSym b n (b n β)))
      (expSym b n (SymSpecies.map (R := R) σ (b n β)))
    simp only [LinearMap.comp_apply] at this
    refine this.trans (sub_eq_zero.2 (h1.trans (coordSh_toSh_map b n τ _).symm))
  rw [he, (FreeSet.toSh R B).app_map, (coordSh b).app_map, hz, map_zero]

/-- **The operad presented by a basis is the free shuffle operad on the basis**, sorting and
taking coordinates. -/
noncomputable def bpToSh : ShuffleOperadHom R (Shuf (BPres b)) (FreeSh R B) :=
  ((ShuffleOperadIdeal.span R (FreeSet.shuffleRel R (basisRel b))).liftHom (coordSh b)
    fun _ _ _ _ hx => (coordSh b).app_eq_zero_of_mem_span (coordSh_kills b) hx).comp
    (FreeSet.presToSh R (basisRel b))

lemma bpToSh_expSym (n : ℕ) (v : V (Fin n)) :
    (bpToSh b).app (Fin n) ((SymOperadIdeal.span R (basisRel b)).proj (Fin n) (expSym b n v)) =
      expSh b n v :=
  coordSh_toSh b n v

/-- The basis generators of the free shuffle operad, in the operad presented by the basis. -/
noncomputable def shToBP : ShuffleOperadHom R (FreeSh R B) (Shuf (BPres b)) :=
  FreeSh.lift R (Shuf (BPres b)) fun k β =>
    (SymOperadIdeal.span R (basisRel b)).proj (Fin k) (Finsupp.single (Pres.gen β) 1)

lemma shToBP_expSh (n : ℕ) (v : V (Fin n)) :
    (shToBP b).app (Fin n) (expSh b n v) =
      (SymOperadIdeal.span R (basisRel b)).proj (Fin n) (expSym b n v) := by
  have h : (shToBP b).app (Fin n) ∘ₗ expSh b n =
      (SymOperadIdeal.span R (basisRel b)).proj (Fin n) ∘ₗ expSym b n :=
    (b n).ext fun β => by
      show (shToBP b).app (Fin n) (expSh b n (b n β)) =
        (SymOperadIdeal.span R (basisRel b)).proj (Fin n) (expSym b n (b n β))
      rw [expSym_basis, expSh_basis, shToBP, FreeSh.lift_gen]
  exact LinearMap.congr_fun h v

theorem bpToSh_comp_shToBP : (bpToSh b).comp (shToBP b) = ShuffleOperadHom.id :=
  ShuffleOperadHom.ext fun A _ _ x => FreeSh.hom_ext (fun k hk β => by
    show (bpToSh b).app (Fin k) ((shToBP b).app (Fin k) (Finsupp.single (FreeSh.genM hk β) 1)) = _
    rw [shToBP, FreeSh.lift_gen, ← expSym_basis b β, bpToSh_expSym, expSh_basis]
    rfl) A x

theorem shToBP_comp_bpToSh : (shToBP b).comp (bpToSh b) = ShuffleOperadHom.id :=
  SymOperadIdeal.shuffle_hom_ext _ fun n β σ => by
    show (shToBP b).app (Fin n) ((bpToSh b).app (Fin n) _) = _
    rw [proj_single_map, bpToSh_expSym, shToBP_expSh]
    rfl

/-! ## The free operad on a linear species as a free shuffle operad -/

/-- **Sorting and taking coordinates**: the morphism of shuffle operads from the free operad on a
linear species to the free shuffle operad on a basis of its generators. -/
noncomputable def toFreeSh : ShuffleOperadHom R (Shuf (FreeL R V)) (FreeSh R B) :=
  (bpToSh b).comp (toBP b).toShuffle

/-- **The basis generators**: the morphism of shuffle operads from the free shuffle operad on a
basis of the generators to the free operad on the linear species, sending a basis vector to its
generator. -/
noncomputable def ofFreeSh : ShuffleOperadHom R (FreeSh R B) (Shuf (FreeL R V)) :=
  (fromBP b).toShuffle.comp (shToBP b)

/-- **A generator goes to its expansion in the basis.** -/
theorem toFreeSh_ι {k : ℕ} (v : V (Fin k)) :
    (toFreeSh b).app (Fin k) ((ι R V).app (Fin k) v) = expSh b k v := by
  show (bpToSh b).app (Fin k) ((toBP b).app (Fin k) ((ι R V).app (Fin k) v)) = _
  rw [ι_app_fin]
  show (bpToSh b).app (Fin k) ((toBPLin b).app (Fin k) (linGen R V v)) = _
  rw [toBPLin_gen, bpToSh_expSym]

/-- **The generator of a basis vector goes to the shuffle generator.** -/
theorem toFreeSh_ι_basis {k : ℕ} (hk : 0 < k) (β : B k) :
    (toFreeSh b).app (Fin k) ((ι R V).app (Fin k) (b k β)) =
      Finsupp.single (FreeSh.genM hk β) 1 := by
  rw [toFreeSh_ι, expSh_basis]

omit [IsEmpty (B 0)] in
/-- **The shuffle generator goes to the generator of its basis vector.** -/
theorem ofFreeSh_genM {k : ℕ} (hk : 0 < k) (β : B k) :
    (ofFreeSh b).app (Fin k) (Finsupp.single (FreeSh.genM hk β) 1) =
      (ι R V).app (Fin k) (b k β) := by
  show (fromBP b).app (Fin k) ((shToBP b).app (Fin k) _) = _
  rw [shToBP, FreeSh.lift_gen]
  exact fromBPLin_gen b β

theorem toFreeSh_comp_ofFreeSh : (toFreeSh b).comp (ofFreeSh b) = ShuffleOperadHom.id :=
  ShuffleOperadHom.ext fun A _ _ x => by
    show (bpToSh b).app A ((toBP b).app A ((fromBP b).app A ((shToBP b).app A x))) = x
    rw [show (toBP b).app A ((fromBP b).app A ((shToBP b).app A x)) = (shToBP b).app A x from
      congrArg (fun φ : SymOperadHom R (BPres b) (BPres b) => φ.app A ((shToBP b).app A x))
        (toBP_comp_fromBP b)]
    exact congrArg (fun φ : ShuffleOperadHom R (FreeSh R B) (FreeSh R B) => φ.app A x)
      (bpToSh_comp_shToBP b)

theorem ofFreeSh_comp_toFreeSh : (ofFreeSh b).comp (toFreeSh b) = ShuffleOperadHom.id :=
  ShuffleOperadHom.ext fun A _ _ x => by
    show (fromBP b).app A ((shToBP b).app A ((bpToSh b).app A ((toBP b).app A x))) = x
    rw [show (shToBP b).app A ((bpToSh b).app A ((toBP b).app A x)) = (toBP b).app A x from
      congrArg (fun φ : ShuffleOperadHom R (Shuf (BPres b)) (Shuf (BPres b)) =>
        φ.app A ((toBP b).app A x)) (shToBP_comp_bpToSh b)]
    exact congrArg (fun φ : SymOperadHom R (FreeL R V) (FreeL R V) => φ.app A x)
      (fromBP_comp_toBP b)

/-- **The free operad on a linear species is the free shuffle operad on a basis of its
generators**, on every finite linear order. -/
noncomputable def shuffleEquiv (A : Type) [Fintype A] [LinearOrder A] :
    FreeL R V A ≃ₗ[R] FreeSh R B A :=
  LinearEquiv.ofLinear ((toFreeSh b).app A) ((ofFreeSh b).app A)
    (LinearMap.ext fun x => congrArg (fun φ : ShuffleOperadHom R (FreeSh R B) (FreeSh R B) =>
      φ.app A x) (toFreeSh_comp_ofFreeSh b))
    (LinearMap.ext fun x => congrArg (fun φ : ShuffleOperadHom R (Shuf (FreeL R V))
      (Shuf (FreeL R V)) => φ.app A x) (ofFreeSh_comp_toFreeSh b))

/-- **The shuffle-monomial basis of the free operad on a linear species**: on a finite linear
order, the shuffle monomials with vertices the basis vectors of the generators. -/
noncomputable def shuffleBasis (A : Type) [Fintype A] [LinearOrder A] :
    Module.Basis (SMono B (Finset.range (Fintype.card A))) R (FreeL R V A) :=
  Finsupp.basisSingleOne.map (shuffleEquiv b A).symm

theorem shuffleBasis_apply (A : Type) [Fintype A] [LinearOrder A]
    (m : SMono B (Finset.range (Fintype.card A))) :
    shuffleBasis b A m = (ofFreeSh b).app A (Finsupp.single m 1) := by
  rw [shuffleBasis, Module.Basis.map_apply, Finsupp.coe_basisSingleOne]
  rfl

include b in
/-- **The dimension of the free operad on a linear species** is the number of shuffle
monomials on the basis, when there are finitely many. -/
theorem finrank_eq_card [Nontrivial R] (A : Type) [Fintype A] [LinearOrder A]
    [Finite (SMono B (Finset.range (Fintype.card A)))] :
    Module.finrank R (FreeL R V A) = Nat.card (SMono B (Finset.range (Fintype.card A))) :=
  Module.finrank_eq_nat_card_basis (shuffleBasis b A)

end Shuffle

/-! ## Generators of arity two -/

section Binary

open scoped Nat

variable {G : Type w}

/-- The binary generators of arity two are the labels. -/
def binGenEquiv : G ≃ BinGen G 2 where
  toFun := BinGen.op
  invFun x := match x with | BinGen.op g => g
  left_inv _ := rfl
  right_inv x := by cases x; rfl

/-- **The basis of a linear species concentrated in arity two**: a basis of `V (Fin 2)`, indexed
by `G`, and the empty basis of the vanishing arities. -/
noncomputable def binBasisOf (b₂ : Module.Basis G R (V (Fin 2)))
    (h : ∀ k, k ≠ 2 → Subsingleton (V (Fin k))) : ∀ k, Module.Basis (BinGen G k) R (V (Fin k)) :=
  fun k => if hk : k = 2 then by subst hk; exact b₂.reindex binGenEquiv else
    haveI := h k hk
    haveI : IsEmpty (BinGen G k) := ⟨fun x => by cases x; exact hk rfl⟩
    Module.Basis.empty _

omit [SymSpecies R V] in
@[simp] lemma binBasisOf_op (b₂ : Module.Basis G R (V (Fin 2)))
    (h : ∀ k, k ≠ 2 → Subsingleton (V (Fin k))) (g : G) :
    binBasisOf b₂ h 2 (BinGen.op g) = b₂ g := by
  rw [binBasisOf, dif_pos rfl]
  exact (b₂.reindex_apply binGenEquiv (BinGen.op g)).trans rfl

variable (c : ∀ k, Module.Basis (BinGen G k) R (V (Fin k))) [Fintype G] [DecidableEq G]

/-- **The binary-tree basis of the free operad on a linear species concentrated in arity two**:
on a finite linear order with `n` elements, the binary shuffle trees with leaves `0, …, n - 1`
and vertices decorated by the basis vectors of the binary generators. -/
noncomputable def binBasis (A : Type) [Fintype A] [LinearOrder A] :
    Module.Basis {t // t ∈ LTree.monomials (E := G) (Fintype.card A)} R (FreeL R V A) :=
  (shuffleBasis c A).reindex (LTree.binMonoEquiv _).symm

theorem binBasis_apply (A : Type) [Fintype A] [LinearOrder A]
    (t : {t // t ∈ LTree.monomials (E := G) (Fintype.card A)}) :
    binBasis c A t = (ofFreeSh c).app A (Finsupp.single (LTree.binMonoEquiv _ t) 1) := by
  rw [binBasis, Module.Basis.reindex_apply, Equiv.symm_symm, shuffleBasis_apply]

include c in
/-- **The dimension of the free operad on binary generators**: in arity `n + 1`, the free operad on
a linear species concentrated in arity two, with `V (Fin 2)` free on `G`, has dimension
`(2n - 1)!! |G|ⁿ`, the number of binary shuffle trees. -/
theorem finrank_eq_doubleFactorial [Nontrivial R] (A : Type) [Fintype A] [LinearOrder A] (n : ℕ)
    (hA : Fintype.card A = n + 1) :
    Module.finrank R (FreeL R V A) = (2 * n - 1)‼ * Fintype.card G ^ n := by
  rw [Module.finrank_eq_card_basis (binBasis c A), Fintype.card_coe, hA, LTree.card_monomials]

end Binary

end FreeL

end Operad
