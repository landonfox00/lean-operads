/-
# The homotopy transfer theorem for dg Lie algebras: the transferred L∞-structure

Over a ring in which `2` is invertible, for a super module `(V, ε)` with `ε² = 1`, an
L∞[1]-structure `(d, b)` concentrated in arities one and two, and a retraction `(e, h)` with
`h d + d h = e - 1`:

* **the transferred operations form an L∞[1]-structure** (`LInfT.isLInf_transfer`,
  `LInfT.isLInf_lt`): `ℓ'₁ = e d e` (`LInfT.lt_one`) and `ℓ'ₙ = e ∘ ½ ∑ ± b (i∞, i∞)`, the sum
  over the splittings of the inputs into two nonempty parts;
* **the trees form an ∞-morphism `i∞`** from the transferred structure to `(d, b)`, with
  `i∞₁ = e` (`LInfT.ft_one`) and `∑_S ± i∞(ℓ'(v_S), v_{Sᶜ}) = d (i∞ v) + ½ ∑_S ± b (i∞ v_S,
  i∞ v_{Sᶜ})` on homogeneous inputs (`LInfT.morph_transfer`, `LInfT.ft_morph`).

The operations are multilinear maps on `V`: on inputs of parities `q` they are the trees of
`Operad.LInfTree` with parities `q`, and in general the sum over `q` after the parity projections
`½ (1 ± ε)` (`LInfT.proj`, `LInfT.lt`, `LInfT.ft`). Two multilinear maps agreeing on homogeneous
inputs are equal (`LInfT.ext_homog`). The Jacobi identities of the transferred structure are the
key equation on all the inputs (`LInfT.jac_lt`). As in `Operad.HTT`, the operations live on the
image of `e`, and the side conditions on `h` are not needed.

∞-morphisms of L∞-algebras in general, and their composition, are in `Operad.LInfMorphism`,
where `i∞` is shown to be one (`LSer.isInfMorph_transfer`).
-/
import Operad.LInfTransfer

universe u v

namespace Operad

namespace LInfT

open GerBV KS End

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {V : Type v} [AddCommGroup V]
  [Module R V]

/-! ## Parity projections -/

section proj

variable (ε : V →ₗ[R] V)

/-- **The projection onto the inputs of parity `q`**, `½ (1 + σ_q ε)`. -/
noncomputable def proj (q : Bool) : V →ₗ[R] V := (⅟2 : R) • (LinearMap.id + σ R q • ε)

lemma proj_apply (q : Bool) (x : V) : proj ε q x = (⅟2 : R) • (x + σ R q • ε x) := rfl

variable {ε} (hε : ∀ x, ε (ε x) = x)
include hε

lemma isPar_proj (q : Bool) (x : V) : IsPar ε q (proj ε q x) := by
  unfold IsPar
  rw [proj_apply, map_smul, map_add, map_smul, hε,
    show σ R q • (⅟2 : R) • (x + σ R q • ε x)
      = (⅟2 : R) • (σ R q • x + (σ R q * σ R q) • ε x) by module,
    LInf.σ_mul_self, one_smul, add_comm]

omit hε in
lemma proj_of_isPar {q : Bool} {x : V} (hx : IsPar ε q x) : proj ε q x = x := by
  rw [proj_apply, hx, smul_smul, LInf.σ_mul_self, one_smul, ← two_smul R x, smul_smul,
    invOf_mul_self, one_smul]

omit hε in
lemma proj_not_of_isPar {q : Bool} {x : V} (hx : IsPar ε q x) : proj ε (!q) x = 0 := by
  rw [proj_apply, hx, smul_smul, LInf.σ_not, neg_mul, LInf.σ_mul_self, neg_one_smul,
    add_neg_cancel, smul_zero]

omit hε in
lemma sum_proj (x : V) : ∑ q : Bool, proj ε q x = x := by
  rw [Fintype.sum_bool, proj_apply, proj_apply, ← smul_add]
  simp only [σ_true, σ_false, neg_one_smul, one_smul]
  rw [show x + -ε x + (x + ε x) = (2 : R) • x by rw [two_smul]; abel, smul_smul,
    invOf_mul_self, one_smul]

omit hε in
/-- **A multilinear map is the sum of its values on the homogeneous parts of its inputs.** -/
lemma eq_sum_proj {W : Type*} [AddCommGroup W] [Module R W] {k : ℕ}
    (f : MultilinearMap R (fun _ : Fin k => V) W) (v : Fin k → V) :
    f v = ∑ q : Fin k → Bool, f fun i => proj ε (q i) (v i) := by
  conv_lhs => rw [show v = fun i => ∑ q : Bool, proj ε q (v i) from
    funext fun i => (sum_proj (v i)).symm]
  exact f.map_sum fun i q => proj ε q (v i)

/-- **Multilinear maps agreeing on homogeneous inputs are equal.** -/
lemma ext_homog {W : Type*} [AddCommGroup W] [Module R W] {k : ℕ}
    {f g : MultilinearMap R (fun _ : Fin k => V) W}
    (hfg : ∀ (q : Fin k → Bool) (v : Fin k → V), (∀ i, IsPar ε (q i) (v i)) → f v = g v) :
    f = g := by
  ext v
  rw [eq_sum_proj f v, eq_sum_proj g v]
  exact Finset.sum_congr rfl fun q _ => hfg q _ fun i => isPar_proj hε (q i) (v i)

omit hε in
/-- **On homogeneous inputs of parities `p`, only the projection of parities `p` survives.** -/
lemma sum_proj_homog {W : Type*} [AddCommGroup W] [Module R W] {k : ℕ}
    (F : (Fin k → Bool) → MultilinearMap R (fun _ : Fin k => V) W) {p : Fin k → Bool}
    {v : Fin k → V} (hv : ∀ i, IsPar ε (p i) (v i)) :
    ∑ q : Fin k → Bool, F q (fun i => proj ε (q i) (v i)) = F p v := by
  rw [Finset.sum_eq_single p]
  · congr 1
    funext i
    exact proj_of_isPar (hv i)
  · intro q _ hq
    obtain ⟨i, hi⟩ : ∃ i, q i ≠ p i := by
      by_contra h
      push Not at h
      exact hq (funext h)
    have : q i = !p i := by
      cases hq' : q i <;> cases hp : p i <;> simp_all
    exact (F q).map_coord_zero i (by rw [this]; exact proj_not_of_isPar (hv i))
  · intro h
    exact absurd (Finset.mem_univ p) h

end proj

/-! ## The transferred operation on a set of inputs -/

section lp

variable {α : Type*} [LinearOrder α] (d e h : V →ₗ[R] V) (b : End R V 2) (p : α → Bool)
  (v : α → V)

lemma lp_update_lin {a : α} {S : Finset α} (haS : a ∈ S) (x y : V) (c : R) :
    lp d e h b p (Function.update v a (x + y)) S
        = lp d e h b p (Function.update v a x) S + lp d e h b p (Function.update v a y) S ∧
      lp d e h b p (Function.update v a (c • x)) S
        = c • lp d e h b p (Function.update v a x) S := by
  unfold lp
  by_cases hS : S.card ≤ 1
  · have hSa : S = {a} := Finset.eq_singleton_iff_unique_mem.2
      ⟨haS, fun x hx => Finset.card_le_one.1 hS x hx a haS⟩
    subst hSa
    refine ⟨?_, ?_⟩ <;> simp [map_add, map_smul]
  · simp only [if_neg hS]
    obtain ⟨h1, h2⟩ := lam_update_lin b e h p v haS x y c
    rw [h1, h2, map_add, map_smul]
    exact ⟨rfl, rfl⟩

lemma lp_map {β : Type*} [LinearOrder β] (ι : α ↪o β) (q : β → Bool) (w : β → V)
    (S : Finset α) :
    lp d e h b (q ∘ ι) (w ∘ ι) S = lp d e h b q w (S.map ι.toEmbedding) := by
  unfold lp
  rw [Finset.card_map, Finset.sum_map, lam_map]
  rfl

lemma lp_swap {a a' : α} (haa : a < a') (hadj : ∀ z, ¬ (a < z ∧ z < a')) (S : Finset α) :
    lp d e h b (p ∘ Equiv.swap a a') (v ∘ Equiv.swap a a') S
      = cs (R := R) p a a' S • lp d e h b p v (S.map (Equiv.swap a a').toEmbedding) := by
  unfold lp
  rw [Finset.card_map]
  split_ifs with hS
  · rw [cs_of_card_le_one (R := R) p haa.ne hS, one_smul, Finset.sum_map]
    rfl
  · rw [lam_swap b e h p v haa hadj, map_smul]

variable {ε : V →ₗ[R] V}

omit [Invertible (2 : R)] in
lemma isPar_e {e d h : V →ₗ[R] V} (hr : HTT.Retract ε d e h) {q : Bool} {x : V}
    (hx : IsPar ε q x) : IsPar ε q (e x) := by
  unfold IsPar at *
  rw [← hr.e_even, hx, map_smul]

omit [Invertible (2 : R)] in
lemma isPar_d {d : V →ₗ[R] V} {b : End R V 2} (hL : ShLie ε d b) {q : Bool} {x : V}
    (hx : IsPar ε q x) : IsPar ε (!q) (d x) := by
  unfold IsPar at *
  rw [← neg_neg (ε (d x)), ← hL.d_odd, hx, map_smul, LInf.σ_not, neg_smul]

variable {d e h b p v}

/-- **The transferred operations are odd.** -/
lemma isPar_lp (hL : ShLie ε d b) (hr : HTT.Retract ε d e h) (hv : ∀ a, IsPar ε (p a) (v a))
    (S : Finset α) : IsPar ε (!par p S) (lp d e h b p v S) := by
  unfold lp
  split_ifs with hS
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hS with h0 | h1
    · rw [Finset.card_eq_zero.1 h0, Finset.sum_empty]
      exact isPar_zero _
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h1
      rw [Finset.sum_singleton]
      have h1 : par p {a} = p a := by
        rw [show ({a} : Finset α) = insert a ∅ from rfl, par_insert p (Finset.notMem_empty a),
          par_empty, Bool.xor_false]
      rw [h1]
      exact isPar_e hr (isPar_d hL (isPar_e hr (hv a)))
  · exact isPar_e hr (isPar_tree hL.b_odd hr p v hv _ S rfl).2

end lp

/-! ## The transferred operations and the trees as multilinear maps -/

section maps

variable (ε d e h : V →ₗ[R] V) (b : End R V 2)

/-- **The trees on the inputs `Fin k` with parities `q`**, as a multilinear map. -/
noncomputable def treeML {k : ℕ} (q : Fin k → Bool) : End R V k where
  toFun v := tree b e h q v Finset.univ
  map_update_add' v i x y := by
    convert (tree_update_lin b e h q v i _ Finset.univ rfl (Finset.mem_univ i) x y 1).1
  map_update_smul' v i c x := by
    convert (tree_update_lin b e h q v i _ Finset.univ rfl (Finset.mem_univ i) x x c).2

/-- **The transferred operation on the inputs `Fin k` with parities `q`**, as a multilinear
map. -/
noncomputable def lpML {k : ℕ} (q : Fin k → Bool) : End R V k where
  toFun v := lp d e h b q v Finset.univ
  map_update_add' v i x y := by
    convert (lp_update_lin d e h b q v (Finset.mem_univ i) x y 1).1
  map_update_smul' v i c x := by
    convert (lp_update_lin d e h b q v (Finset.mem_univ i) x x c).2

/-- **The transferred L∞-structure**: on inputs of parities `q`, the transferred operation of
parities `q`. -/
noncomputable def lt (k : ℕ) : End R V k :=
  ∑ q : Fin k → Bool, (lpML d e h b q).compLinearMap fun i => proj ε (q i)

/-- **The ∞-morphism `i∞`**: on inputs of parities `q`, the trees of parities `q`. -/
noncomputable def ft (k : ℕ) : End R V k :=
  ∑ q : Fin k → Bool, (treeML e h b q).compLinearMap fun i => proj ε (q i)

variable {ε d e h b}

lemma lt_homog {k : ℕ} {p : Fin k → Bool} {v : Fin k → V} (hv : ∀ i, IsPar ε (p i) (v i)) :
    lt ε d e h b k v = lp d e h b p v Finset.univ := by
  unfold lt
  rw [MultilinearMap.sum_apply]
  exact sum_proj_homog (fun q => lpML d e h b q) hv

lemma ft_homog {k : ℕ} {p : Fin k → Bool} {v : Fin k → V} (hv : ∀ i, IsPar ε (p i) (v i)) :
    ft ε e h b k v = tree b e h p v Finset.univ := by
  unfold ft
  rw [MultilinearMap.sum_apply]
  exact sum_proj_homog (fun q => treeML e h b q) hv

end maps

/-! ## Inner outputs as first inputs, on `Fin n` -/

section cons

/-- The inputs `0, …, m` sent to a new least input `⊥` and to `f 0, …, f (m - 1)`. -/
noncomputable def consEmb {n m : ℕ} (f : Fin m ↪o Fin n) : Fin (m + 1) ↪o WithBot (Fin n) :=
  OrderEmbedding.ofStrictMono
    (fun j => Fin.cases (⊥ : WithBot (Fin n)) (fun j => ((f j : Fin n) : WithBot (Fin n))) j)
    (by
      intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd hij (lt_irrefl _)
        | succ j => exact WithBot.bot_lt_coe _
      | succ i =>
        induction j using Fin.cases with
        | zero => exact absurd hij (not_lt_of_ge (Fin.zero_le _))
        | succ j =>
          exact WithBot.coe_lt_coe.2 (f.strictMono (Fin.succ_lt_succ_iff.1 hij)))

lemma botP_consEmb {n m : ℕ} (f : Fin m ↪o Fin n) (q : Bool) (p : Fin n → Bool) :
    botP q p ∘ consEmb f = Fin.cons q (p ∘ f) := by
  funext j
  induction j using Fin.cases <;> rfl

omit [Invertible (2 : R)] [AddCommGroup V] [Module R V] in
lemma botV_consEmb {n m : ℕ} (f : Fin m ↪o Fin n) (x : V) (v : Fin n → V) :
    botV x v ∘ consEmb f = Fin.cons x (v ∘ f) := by
  funext j
  induction j using Fin.cases <;> rfl

lemma map_univ_consEmb {n : ℕ} (S : Finset (Fin n)) :
    (Finset.univ : Finset (Fin (Sᶜ.card + 1))).map (consEmb (Sᶜ.orderEmbOfFin rfl)).toEmbedding
      = bset S Finset.univ := by
  unfold bset
  rw [← Finset.compl_eq_univ_sdiff]
  ext x
  rw [Finset.mem_map, Finset.mem_insert, Finset.mem_map]
  induction x using WithBot.recBotCoe with
  | bot =>
    simp only [true_or, iff_true]
    exact ⟨0, Finset.mem_univ _, rfl⟩
  | coe a =>
    simp only [WithBot.coe_ne_bot, false_or]
    constructor
    · rintro ⟨j, -, hj⟩
      induction j using Fin.cases with
      | zero => exact absurd hj.symm WithBot.coe_ne_bot
      | succ j =>
        refine ⟨Sᶜ.orderEmbOfFin rfl j, Finset.orderEmbOfFin_mem _ _ _, ?_⟩
        exact hj
    · rintro ⟨c, hc, hca⟩
      have : c ∈ Set.range (Sᶜ.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        exact hc
      obtain ⟨j, rfl⟩ := this
      exact ⟨j.succ, Finset.mem_univ _, hca⟩

end cons

/-! ## The transferred structure is an L∞-structure -/

section theorem_

variable {ε d e h : V →ₗ[R] V} {b : End R V 2}

/-- The transferred operation with an inner transferred operation on `T` as a new first input. -/
lemma lp_bset_eq {n : ℕ} (p : Fin n → Bool) (v : Fin n → V) {T S : Finset (Fin n)}
    (hTS : T ⊆ S) :
    lp d e h b (botP (!par p T) p) (botV (lp d e h b p v T) v) (bset T S)
      = e (lamB d e h b p v T S) + (if T = S then e (d (e (lp d e h b p v T))) else 0) := by
  have hdef : lp d e h b (botP (!par p T) p) (botV (lp d e h b p v T) v) (bset T S)
      = if (bset T S).card ≤ 1 then ∑ x ∈ bset T S, e (d (e (botV (lp d e h b p v T) v x)))
        else e (lam b e h (botP (!par p T) p) (botV (lp d e h b p v T) v) (bset T S)) := rfl
  unfold lamB
  rw [hdef, card_bset]
  by_cases hT : T = S
  · subst hT
    have h1 : bset T T = {⊥} := by
      unfold bset
      rw [Finset.sdiff_self, Finset.map_empty]
      rfl
    rw [if_pos (by rw [Finset.sdiff_self, Finset.card_empty]), if_pos rfl, h1,
      Finset.sum_singleton, lam_of_card_le_one _ _ _ _ _ (by rw [Finset.card_singleton]),
      map_zero, zero_add]
    rfl
  · have hne : (S \ T).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro e'
      exact hT (Finset.Subset.antisymm hTS (Finset.sdiff_eq_empty_iff_subset.1 e'))
    rw [if_neg (by have := hne.card_pos; omega), if_neg hT, add_zero]

variable (hε : ∀ x, ε (ε x) = x) (hL : ShLie ε d b) (hr : HTT.Retract ε d e h)
include hε hL hr

omit hε in
/-- The Jacobi expressions of the transferred structure, as transferred operations with an inner
transferred operation. -/
lemma jac_lt {n : ℕ} (p : Fin n → Bool) (v : Fin n → V) (hv : ∀ a, IsPar ε (p a) (v a)) :
    LInf.jac (lt ε d e h b) p v = ∑ S ∈ nes (Finset.univ : Finset (Fin n)),
      ks R p S (Finset.univ \ S) • lp d e h b (botP (!par p S) p)
        (botV (lp d e h b p v S) v) (bset S Finset.univ) := by
  unfold LInf.jac nes
  rw [Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hS : lt ε d e h b S.card (LInf.restr v S) = lp d e h b p v S := by
    rw [show LInf.restr v S = v ∘ (S.orderEmbOfFin rfl) from rfl,
      lt_homog (p := p ∘ S.orderEmbOfFin rfl) (v := v ∘ S.orderEmbOfFin rfl) fun a => hv _]
    have := lp_map d e h b (S.orderEmbOfFin rfl) p v Finset.univ
    rw [Finset.map_orderEmbOfFin_univ] at this
    exact this
  have hx := isPar_lp hL hr hv S
  have hrs : LInf.restr v Sᶜ = v ∘ (Sᶜ.orderEmbOfFin rfl) := rfl
  rw [hS, LInf.usgn, ← Finset.compl_eq_univ_sdiff]
  congr 1
  have hcons : ∀ a, IsPar ε
      ((Fin.cons (!par p S) (p ∘ Sᶜ.orderEmbOfFin rfl) : Fin (Sᶜ.card + 1) → Bool) a)
      ((Fin.cons (lp d e h b p v S) (LInf.restr v Sᶜ) : Fin (Sᶜ.card + 1) → V) a) := by
    intro a
    induction a using Fin.cases with
    | zero => exact hx
    | succ a => exact hv _
  rw [lt_homog hcons, hrs, ← botP_consEmb, ← botV_consEmb, lp_map, map_univ_consEmb]

/-- **The homotopy transfer theorem for dg Lie algebras**: the transferred operations form an
L∞[1]-structure. -/
theorem isLInf_lt : LInf.IsLInf ε (lt ε d e h b) where
  odd k := by
    have key : (lt ε d e h b k).compLinearMap (fun _ => ε)
        = (-1 : R) • ε.compMultilinearMap (lt ε d e h b k) := by
      refine ext_homog hε fun q v hv => ?_
      rw [MultilinearMap.compLinearMap_apply, MultilinearMap.smul_apply,
        LinearMap.compMultilinearMap_apply]
      have e1 : (fun i => ε (v i)) = fun i => σ R (q i) • v i := funext hv
      rw [e1, MultilinearMap.map_smul_univ, lt_homog hv, ← σ_par]
      have := isPar_lp hL hr hv Finset.univ
      unfold IsPar at this
      rw [this, LInf.σ_not, smul_smul]
      congr 1
      ring
    intro v
    have := congrArg (fun F : End R V k => F v) key
    simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.smul_apply,
      LinearMap.compMultilinearMap_apply] at this
    rw [pow_one]
    exact this
  symm k p v hv i hik := by
    have haa : (⟨i, by omega⟩ : Fin k) < ⟨i + 1, hik⟩ := Fin.mk_lt_mk.2 (Nat.lt_succ_self i)
    have hadj : ∀ z : Fin k, ¬ ((⟨i, by omega⟩ : Fin k) < z ∧ z < ⟨i + 1, hik⟩) := by
      rintro z ⟨h1, h2⟩
      rw [Fin.lt_def] at h1 h2
      simp only at h1 h2
      omega
    rw [lt_homog (p := p ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, hik⟩)
      (v := v ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, hik⟩) fun a => hv _, lt_homog hv,
      lp_swap d e h b p v haa hadj, Finset.map_univ_equiv]
    unfold cs
    rw [if_pos ⟨Finset.mem_univ _, Finset.mem_univ _⟩]
  jac n p v hv := by
    rw [jac_lt hL hr p v hv]
    have hK := (morph_key hL hr hv _ (Finset.univ : Finset (Fin n)) rfl).1
    have hI : insL d e h b p v Finset.univ = -d (lam b e h p v Finset.univ) := by
      rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
      exact hK
    have hterm : ∀ S ∈ nes (Finset.univ : Finset (Fin n)), ks R p S (Finset.univ \ S) •
        lp d e h b (botP (!par p S) p) (botV (lp d e h b p v S) v) (bset S Finset.univ)
        = ks R p S (Finset.univ \ S) • e (lamB d e h b p v S Finset.univ) +
          (if S = Finset.univ then ks R p S (Finset.univ \ S) •
            e (d (e (lp d e h b p v S))) else 0) := fun S _ => by
      rw [lp_bset_eq p v (Finset.subset_univ S), smul_add, smul_ite, smul_zero]
    have h1 : ∑ S ∈ nes (Finset.univ : Finset (Fin n)),
        ks R p S (Finset.univ \ S) • e (lamB d e h b p v S Finset.univ)
        = e (insL d e h b p v Finset.univ) := by
      unfold insL
      rw [map_sum]
      simp only [map_smul]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', h1, hI]
    split_ifs with hmem
    · rw [Finset.sdiff_self, ks_empty_right, one_smul]
      unfold lp
      split_ifs with hn
      · rw [lam_of_card_le_one b e h p v hn]
        simp only [map_zero, neg_zero, zero_add, map_sum]
        exact Finset.sum_eq_zero fun a _ => by simp only [hr.de, hr.ee, hL.dd, map_zero]
      · simp only [map_neg, hr.de, hr.ee]
        abel
    · have hn : (Finset.univ : Finset (Fin n)).card ≤ 1 := by
        by_contra hc
        exact hmem (mem_nes.2 ⟨subset_rfl, Finset.card_pos.1 (by omega)⟩)
      rw [lam_of_card_le_one b e h p v hn]
      simp

end theorem_

/-! ## The trees form an ∞-morphism -/

section morphism

variable {ε d e h : V →ₗ[R] V} {b : End R V 2}

omit [Invertible (2 : R)] [AddCommGroup V] [Module R V] in
lemma restr_eq {n : ℕ} (v : Fin n → V) (S : Finset (Fin n)) :
    LInf.restr v S = v ∘ (S.orderEmbOfFin rfl) := rfl

/-- The trees on a subset of the inputs, as values of `i∞`. -/
lemma ft_restr {n : ℕ} {p : Fin n → Bool} {v : Fin n → V} (hv : ∀ a, IsPar ε (p a) (v a))
    (S : Finset (Fin n)) : ft ε e h b S.card (LInf.restr v S) = tree b e h p v S := by
  rw [restr_eq, ft_homog (p := p ∘ S.orderEmbOfFin rfl) (v := v ∘ S.orderEmbOfFin rfl)
    fun a => hv _]
  have := tree_map b e h (S.orderEmbOfFin rfl) p v _ Finset.univ rfl
  rw [Finset.map_orderEmbOfFin_univ] at this
  exact this

/-- The transferred operations on a subset of the inputs. -/
lemma lt_restr {n : ℕ} {p : Fin n → Bool} {v : Fin n → V} (hv : ∀ a, IsPar ε (p a) (v a))
    (S : Finset (Fin n)) : lt ε d e h b S.card (LInf.restr v S) = lp d e h b p v S := by
  rw [restr_eq, lt_homog (p := p ∘ S.orderEmbOfFin rfl) (v := v ∘ S.orderEmbOfFin rfl)
    fun a => hv _]
  have := lp_map d e h b (S.orderEmbOfFin rfl) p v Finset.univ
  rw [Finset.map_orderEmbOfFin_univ] at this
  exact this

/-- The trees with an inner transferred operation as a new first input. -/
lemma ft_cons (hL : ShLie ε d b) (hr : HTT.Retract ε d e h) {n : ℕ} {p : Fin n → Bool}
    {v : Fin n → V} (hv : ∀ a, IsPar ε (p a) (v a)) (S : Finset (Fin n)) :
    ft ε e h b (Sᶜ.card + 1) (Fin.cons (lp d e h b p v S) (LInf.restr v Sᶜ))
      = treeB d e h b p v S Finset.univ := by
  have hx := isPar_lp hL hr hv S
  have hcons : ∀ a, IsPar ε
      ((Fin.cons (!par p S) (p ∘ Sᶜ.orderEmbOfFin rfl) : Fin (Sᶜ.card + 1) → Bool) a)
      ((Fin.cons (lp d e h b p v S) (LInf.restr v Sᶜ) : Fin (Sᶜ.card + 1) → V) a) := by
    intro a
    induction a using Fin.cases with
    | zero => exact hx
    | succ a => exact hv _
  rw [ft_homog hcons, restr_eq, ← botP_consEmb, ← botV_consEmb,
    tree_map b e h (consEmb (Sᶜ.orderEmbOfFin rfl)) _ _ _ Finset.univ rfl, map_univ_consEmb]
  rfl

/-- **The trees form an ∞-morphism `i∞`** from the transferred L∞-structure to the dg Lie
algebra: on homogeneous inputs, `∑_S ± i∞(ℓ'(v_S), v_{Sᶜ}) = d (i∞ v) + ½ ∑_S ± b (i∞ v_S,
i∞ v_{Sᶜ})`. -/
theorem ft_morph (hL : ShLie ε d b) (hr : HTT.Retract ε d e h) {n : ℕ} (p : Fin n → Bool)
    (v : Fin n → V) (hv : ∀ a, IsPar ε (p a) (v a)) :
    ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.Nonempty), LInf.usgn (R := R) p S •
        ft ε e h b (Sᶜ.card + 1)
          (Fin.cons (lt ε d e h b S.card (LInf.restr v S)) (LInf.restr v Sᶜ))
      = d (ft ε e h b n v) + (⅟2 : R) • ∑ S ∈ splits (Finset.univ : Finset (Fin n)),
        LInf.usgn (R := R) p S • b ![ft ε e h b S.card (LInf.restr v S),
          ft ε e h b Sᶜ.card (LInf.restr v Sᶜ)] := by
  have hL' : ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.Nonempty),
      LInf.usgn (R := R) p S •
      ft ε e h b (Sᶜ.card + 1)
        (Fin.cons (lt ε d e h b S.card (LInf.restr v S)) (LInf.restr v Sᶜ))
      = ins d e h b p v Finset.univ := by
    unfold ins nes
    rw [Finset.powerset_univ]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [lt_restr hv, ft_cons hL hr hv]
    rfl
  have hR : ∑ S ∈ splits (Finset.univ : Finset (Fin n)), LInf.usgn (R := R) p S •
      b ![ft ε e h b S.card (LInf.restr v S), ft ε e h b Sᶜ.card (LInf.restr v Sᶜ)]
      = ∑ S ∈ splits (Finset.univ : Finset (Fin n)), ks R p S (Finset.univ \ S) •
        b ![tree b e h p v S, tree b e h p v (Finset.univ \ S)] := by
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [ft_restr hv, ft_restr hv, Finset.compl_eq_univ_sdiff]
    rfl
  rw [hL', hR, ft_homog hv]
  rcases (Finset.univ : Finset (Fin n)).eq_empty_or_nonempty with hn | hn
  · have h0 : nes (Finset.univ : Finset (Fin n)) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro T hT
      obtain ⟨hTS, a, ha⟩ := mem_nes.1 hT
      have := hTS ha
      rw [hn] at this
      exact Finset.notMem_empty a this
    unfold ins
    rw [h0, Finset.sum_empty, hn, tree_empty, map_zero, zero_add, splits_of_card_le_one
      (by rw [Finset.card_empty]; omega), Finset.sum_empty, smul_zero]
  · exact (morph_key hL hr hv _ Finset.univ rfl).2 hn

end morphism

/-! ## The theorem for L∞-structures concentrated in arities one and two -/

section bridge

variable {ε d e h : V →ₗ[R] V} {b : End R V 2}

/-- **An L∞[1]-structure concentrated in arities one and two is a shifted dg Lie algebra**
(`LInf.isLInf_two_iff`); the differential squares to zero on every input, by the parity
decomposition. -/
theorem ShLie.of_isLInf (hε : ∀ x, ε (ε x) = x) (H : LInf.IsLInf ε (LInf.two (HTT.op1 d) b)) :
    ShLie ε d b := by
  obtain ⟨hd, hb, hsymm, hdd, hleib, hjac⟩ := (LInf.isLInf_two_iff ε (HTT.op1 d) b).1 H
  refine ⟨fun x => ?_, hb, fun x => ?_, hsymm, fun p q x y hx hy => hleib p q x y hx hy, hjac⟩
  · have := hd ![x]
    simp only [HTT.op1_apply, Matrix.cons_val_zero, pow_one, neg_one_smul] at this
    exact this
  · rw [← sum_proj (ε := ε) x, map_sum, map_sum]
    exact Finset.sum_eq_zero fun q _ => hdd q _ (isPar_proj hε q x)

/-- **The homotopy transfer theorem for dg Lie algebras**: for an L∞[1]-structure `(d, b)`
concentrated in arities one and two and a retraction `(e, h)` with `h d + d h = e - 1`, the
transferred operations `ℓ'₁ = e d e`, `ℓ'ₙ = e ∘ ½ ∑ ± b (i∞, i∞)` form an L∞[1]-structure. -/
theorem isLInf_transfer (hε : ∀ x, ε (ε x) = x) (H : LInf.IsLInf ε (LInf.two (HTT.op1 d) b))
    (hr : HTT.Retract ε d e h) : LInf.IsLInf ε (lt ε d e h b) :=
  isLInf_lt hε (ShLie.of_isLInf hε H) hr

/-- **The ∞-morphism `i∞` of the transfer**: `i∞₁ = e`, `i∞ₙ = h ∘ ½ ∑ ± b (i∞, i∞)`, with
`∑_S ± i∞(ℓ'(v_S), v_{Sᶜ}) = d (i∞ v) + ½ ∑_S ± b (i∞ v_S, i∞ v_{Sᶜ})` on homogeneous
inputs. -/
theorem morph_transfer (hε : ∀ x, ε (ε x) = x) (H : LInf.IsLInf ε (LInf.two (HTT.op1 d) b))
    (hr : HTT.Retract ε d e h) {n : ℕ} (p : Fin n → Bool) (v : Fin n → V)
    (hv : ∀ a, IsPar ε (p a) (v a)) :
    ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.Nonempty), LInf.usgn (R := R) p S •
        ft ε e h b (Sᶜ.card + 1)
          (Fin.cons (lt ε d e h b S.card (LInf.restr v S)) (LInf.restr v Sᶜ))
      = d (ft ε e h b n v) + (⅟2 : R) • ∑ S ∈ splits (Finset.univ : Finset (Fin n)),
        LInf.usgn (R := R) p S • b ![ft ε e h b S.card (LInf.restr v S),
          ft ε e h b Sᶜ.card (LInf.restr v Sᶜ)] :=
  ft_morph (ShLie.of_isLInf hε H) hr p v hv

/-- The transferred differential is `e d e`. -/
theorem lt_one (hε : ∀ x, ε (ε x) = x) (v : Fin 1 → V) : lt ε d e h b 1 v = e (d (e (v 0))) := by
  have key : lt ε d e h b 1 = (e ∘ₗ d ∘ₗ e).compMultilinearMap
      (MultilinearMap.ofSubsingleton R V V 0 LinearMap.id) := by
    refine ext_homog hε fun q w hw => ?_
    rw [lt_homog hw]
    unfold lp
    rw [if_pos (by simp), Fin.sum_univ_one]
    rfl
  rw [key]
  rfl

/-- The first component of `i∞` is `e`. -/
theorem ft_one (hε : ∀ x, ε (ε x) = x) (v : Fin 1 → V) : ft ε e h b 1 v = e (v 0) := by
  have key : ft ε e h b 1 = e.compMultilinearMap
      (MultilinearMap.ofSubsingleton R V V 0 LinearMap.id) := by
    refine ext_homog hε fun q w hw => ?_
    rw [ft_homog hw, tree_of_card_le_one b e h q w (by simp), Fin.sum_univ_one]
    rfl
  rw [key]
  rfl

end bridge

end LInfT

end Operad
