/-
# ∞-morphisms of L∞-algebras

Over a ring in which `2` is invertible, for super modules with `ε² = 1`:

* **Composites as series** (`LSer.comp`): on inputs of parities `q`, the composite along the
  partitions with the signs for `q`, made multilinear by the parity projections. Composites of
  even series are even (`LSer.comp_even`), and **composition is associative** when the inner series
  is even (`LSer.comp_assoc`).
* **The extension by an odd parameter.** `V̂ = V ⊕ θV` has the parity `(a, b) ↦ (ε a, -ε b)`
  (`LSer.hatε`); a series extends to `F̂((a₁, b₁), …) = (F(a), ∑ₛ F(ε a₁, …, ε aₛ₋₁, bₛ, …))`
  (`LSer.hat`), and **the extension of a composite is the composite of the extensions**
  (`LSer.hat_comp`), by the sign of flipping the parity of one input (`LSer.sgn_flip`).
* **∞-morphisms** (`LSer.IsInfMorph`): for L∞[1]-structures `ℓ`, `ℓ'`, encoded by
  `β_ℓ = (id, ℓ) : V ⇝ V̂` (`LSer.beta`), an even series `F` with `F̂ ∘ β_ℓ = β_ℓ' ∘ F`.
  **∞-morphisms compose** (`LSer.IsInfMorph.comp`), by associativity and the extension of
  composites, and the identity is one (`LSer.isInfMorph_id`).
* **The equation in the convention of `LInf.IsLInf`.** The part of `F̂ ∘ β_ℓ` in `θ` is
  `∑_T ± F(ℓ(v_T), v_{Tᶜ})`, the inner output first, for `F` graded symmetric
  (`LSer.hat_beta_snd`), by moving one input across the others (`LSer.gsymm_insertNth`); for an
  L∞[1]-structure `(d, b)` in arities one and two, `β_{(d, b)} ∘ F` is `d ∘ F` and half the signed
  sum of `b (F, F)` over the splittings (`LSer.cmp_two`).
* **The ∞-morphism of the transfer** (`LSer.isInfMorph_transfer`): the trees `i∞` of
  `Operad.LInfHTT` form an ∞-morphism from the transferred structure to the dg Lie algebra.

The definition forces the operations without inputs to vanish: a series `F` with
`F̂ ∘ β_ℓ = β_ℓ' ∘ F` has `F₀ = 0` and `ℓ'₀ = 0`.
-/
import Operad.LInfSeries
import Operad.LInfHTT

universe u

namespace Operad

namespace LSer

open GerBV KS IPart LInfT

variable {R : Type u} [CommRing R] {V W X U : Type*} [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [AddCommGroup X] [Module R X] [AddCommGroup U] [Module R U]

/-! ## Even series and parities -/

section parity

variable (εV : V →ₗ[R] V) (εW : W →ₗ[R] W)

/-- **An even series** commutes with the parity operators. -/
def IsEven (F : Ser R V W) : Prop := ∀ k (v : Fin k → V), F k (fun i => εV (v i)) = εW (F k v)

variable {εV εW} {α : Type*} [LinearOrder α]

/-- **An even series has the parity of its inputs.** -/
lemma isPar_ev {F : Ser R V W} (hF : IsEven εV εW F) {p : α → Bool} {v : α → V} {S : Finset α}
    (hv : ∀ a ∈ S, IsPar εV (p a) (v a)) : IsPar εW (par p S) (ev F v S) := by
  have h1 : ev F (fun a => εV (v a)) S = εW (ev F v S) := hF _ _
  have h2 : ev F (fun a => εV (v a)) S = ev F (fun a => σ R (p a) • v a) S :=
    ev_congr F fun a ha => hv a ha
  unfold IsPar
  rw [← h1, h2, ev_smul, σ_par]

/-- Parities with equal signs. -/
lemma isPar_of_σ_eq {b b' : Bool} {x : V} (h : σ R b = σ R b') (hx : IsPar εV b x) :
    IsPar εV b' x := by
  unfold IsPar at *
  rw [hx, h]

end parity

/-! ## Updating one input -/

section update

variable {α : Type*} [LinearOrder α]

lemma ev_update (G : Ser R W X) (w : α → W) {M : Finset α} {m : α} (hm : m ∈ M) (x y : W)
    (c : R) :
    ev G (Function.update w m (x + y)) M
        = ev G (Function.update w m x) M + ev G (Function.update w m y) M ∧
      ev G (Function.update w m (c • x)) M = c • ev G (Function.update w m x) M := by
  classical
  set j := (M.orderIsoOfFin rfl).symm ⟨m, hm⟩
  have hj : M.orderEmbOfFin rfl j = m := by
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  have e : ∀ z, Function.update w m z ∘ M.orderEmbOfFin rfl
      = Function.update (w ∘ M.orderEmbOfFin rfl) j z := fun z => by
    rw [← hj]
    exact Function.update_comp_eq_of_injective w (M.orderEmbOfFin rfl).injective j z
  unfold ev
  rw [e, e, e, e]
  exact ⟨(G M.card).map_update_add _ j x y, (G M.card).map_update_smul _ j c x⟩

variable [Fintype α]

/-- **A composite is additive and homogeneous in each input.** -/
lemma cmp_update (G : Ser R W X) (F : Ser R V W) (p : α → Bool) (v : α → V) {S : Finset α}
    {i : α} (hi : i ∈ S) (x y : V) (c : R) :
    cmp G (ev F (Function.update v i (x + y))) p S
        = cmp G (ev F (Function.update v i x)) p S + cmp G (ev F (Function.update v i y)) p S ∧
      cmp G (ev F (Function.update v i (c • x))) p S
        = c • cmp G (ev F (Function.update v i x)) p S := by
  classical
  have hval : ∀ r ∈ roots S, ∀ z : V, (fun m => ev F (Function.update v i z) (blk r S m))
      = Function.update (fun m => ev F v (blk r S m)) (r i)
          (ev F (Function.update v i z) (blk r S (r i))) := fun r _ z => by
    funext m
    by_cases hm : m = r i
    · subst hm
      rw [Function.update_self]
    · rw [Function.update_of_ne hm]
      refine ev_congr F fun a ha => Function.update_of_ne (fun e => hm ?_) _ _
      rw [← (mem_blk.1 ha).2, e]
  have hterm : ∀ r ∈ roots S,
      ev G (fun m => ev F (Function.update v i (x + y)) (blk r S m)) (fix r S)
        = ev G (fun m => ev F (Function.update v i x) (blk r S m)) (fix r S)
          + ev G (fun m => ev F (Function.update v i y) (blk r S m)) (fix r S) ∧
      ev G (fun m => ev F (Function.update v i (c • x)) (blk r S m)) (fix r S)
        = c • ev G (fun m => ev F (Function.update v i x) (blk r S m)) (fix r S) := by
    intro r hr
    have hr' := mem_roots.1 hr
    have hib : i ∈ blk r S (r i) := mem_blk.2 ⟨hi, rfl⟩
    have hF := ev_update F v hib x y c
    have hfix := hr'.root_mem_fix hi
    rw [hval r hr, hval r hr, hval r hr, hval r hr, hF.1, hF.2]
    exact ev_update G _ hfix _ _ c
  unfold cmp
  constructor
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [(hterm r hr).1, smul_add]
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [(hterm r hr).2, smul_comm]

end update

/-! ## Composites as series -/

section package

variable [Invertible (2 : R)] (εV : V →ₗ[R] V) (εW : W →ₗ[R] W)

/-- The composite on inputs of parities `q`, as a multilinear map. -/
noncomputable def cmpML (G : Ser R W X) (F : Ser R V W) {k : ℕ} (q : Fin k → Bool) :
    MultilinearMap R (fun _ : Fin k => V) X where
  toFun v := cmp G (ev F v) q Finset.univ
  map_update_add' v i x y := by
    convert (cmp_update G F q v (Finset.mem_univ i) x y 1).1
  map_update_smul' v i c x := by
    convert (cmp_update G F q v (Finset.mem_univ i) x x c).2

/-- **The composite of two series**: on inputs of parities `q`, the composite along the
partitions of the inputs with the Koszul signs for `q`. -/
noncomputable def comp (G : Ser R W X) (F : Ser R V W) : Ser R V X := fun k =>
  ∑ q : Fin k → Bool, (cmpML G F q).compLinearMap fun i => proj εV (q i)

variable {εV εW}

lemma comp_homog (G : Ser R W X) (F : Ser R V W) {k : ℕ} {p : Fin k → Bool} {v : Fin k → V}
    (hv : ∀ i, IsPar εV (p i) (v i)) : comp εV G F k v = cmp G (ev F v) p Finset.univ := by
  unfold comp
  rw [MultilinearMap.sum_apply]
  exact sum_proj_homog (fun q => cmpML G F q) hv

/-- **A composite evaluated on homogeneous inputs** is the composite along the partitions of
those inputs. -/
lemma ev_comp_homog (G : Ser R W X) (F : Ser R V W) {α : Type*} [LinearOrder α] [Fintype α]
    {q : α → Bool} {w : α → V} {M : Finset α} (hw : ∀ a ∈ M, IsPar εV (q a) (w a)) :
    ev (comp εV G F) w M = cmp G (ev F w) q M := by
  show comp εV G F M.card (w ∘ M.orderEmbOfFin rfl) = _
  rw [comp_homog (p := q ∘ M.orderEmbOfFin rfl) (v := w ∘ M.orderEmbOfFin rfl) G F
    fun i => hw _ (Finset.orderEmbOfFin_mem _ _ _)]
  have h1 : ev F (w ∘ M.orderEmbOfFin rfl)
      = fun B => ev F w (B.map (M.orderEmbOfFin rfl).toEmbedding) :=
    funext fun B => ev_map F _ w B
  rw [h1, cmp_map, Finset.map_orderEmbOfFin_univ]

/-- **Associativity of composites**, on homogeneous inputs, the inner series being even. -/
theorem comp_assoc_homog (H : Ser R X U) (G : Ser R W X) (F : Ser R V W)
    (hF : IsEven εV εW F) {n : ℕ} {p : Fin n → Bool} {v : Fin n → V}
    (hv : ∀ i, IsPar εV (p i) (v i)) :
    comp εV H (comp εV G F) n v = comp εV (comp εW H G) F n v := by
  rw [comp_homog H _ hv, comp_homog _ F hv]
  have h1 : ev (comp εV G F) v = fun B => cmp G (ev F v) p B :=
    funext fun B => ev_comp_homog G F fun a _ => hv a
  rw [h1, cmp_assoc]
  unfold cmp
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  symm
  exact ev_comp_homog H G fun m _ => isPar_ev hF fun a _ => hv a

/-- **Associativity of composites**, the inner series being even. -/
theorem comp_assoc (hεV : ∀ x, εV (εV x) = x) (H : Ser R X U) (G : Ser R W X) (F : Ser R V W)
    (hF : IsEven εV εW F) : comp εV H (comp εV G F) = comp εV (comp εW H G) F := by
  funext n
  exact ext_homog hεV fun q v hv => comp_assoc_homog H G F hF hv

end package

/-! ## The extension by an odd parameter -/

section hat

variable (εV : V →ₗ[R] V) (εW : W →ₗ[R] W)

/-- **The parity of `V ⊕ θV`**, for `θ` odd: `(a, b) ↦ (ε a, -ε b)`. -/
def hatε : V × V →ₗ[R] V × V := LinearMap.prodMap εV (-εV)

/-- The linear maps reading the inputs of the `s`-th term of an extended series: `θ` passes the
inputs before the `s`-th, which costs `ε` on each. -/
noncomputable def hatL (k : ℕ) (s i : Fin k) : V × V →ₗ[R] V :=
  if i < s then εV ∘ₗ LinearMap.fst R V V else if i = s then LinearMap.snd R V V
  else LinearMap.fst R V V

/-- **The extension of a series** to `V ⊕ θV`:
`F̂((a₁, b₁), …) = (F(a), ∑ₛ F(ε a₁, …, ε aₛ₋₁, bₛ, aₛ₊₁, …))`. -/
noncomputable def hat (F : Ser R V W) : Ser R (V × V) (W × W) := fun k =>
  ((F k).compLinearMap fun _ => LinearMap.fst R V V).prod
    (∑ s : Fin k, (F k).compLinearMap (hatL εV k s))

variable {α : Type*} [LinearOrder α]

/-- The inputs of the term of `F̂` with the second component at `s`. -/
def tw (w : α → V × V) (s : α) : α → V := fun m =>
  if m < s then εV (w m).1 else if m = s then (w m).2 else (w m).1

lemma tw_apply (w : α → V × V) (s m : α) :
    tw εV w s m = if m < s then εV (w m).1 else if m = s then (w m).2 else (w m).1 := rfl

lemma ev_hat (F : Ser R V W) (w : α → V × V) (M : Finset α) :
    ev (hat εV F) w M = (ev F (fun m => (w m).1) M, ∑ s ∈ M, ev F (tw εV w s) M) := by
  ext
  · rfl
  · have h := Finset.sum_map Finset.univ (M.orderEmbOfFin rfl).toEmbedding
      (fun s => ev F (tw εV w s) M)
    rw [Finset.map_orderEmbOfFin_univ] at h
    rw [h]
    unfold ev hat
    simp only [MultilinearMap.prod_apply, MultilinearMap.sum_apply,
      MultilinearMap.compLinearMap_apply]
    refine Finset.sum_congr rfl fun s _ => congrArg (F M.card) (funext fun i => ?_)
    simp only [Function.comp_apply]
    unfold hatL tw
    simp only [show ∀ j : Fin M.card, (M.orderEmbOfFin rfl).toEmbedding j
      = M.orderEmbOfFin rfl j from fun _ => rfl, (M.orderEmbOfFin rfl).lt_iff_lt,
      (M.orderEmbOfFin rfl).injective.eq_iff]
    split_ifs <;> rfl

lemma isPar_hat {q : Bool} {z : V × V} :
    IsPar (hatε εV) q z ↔ IsPar εV q z.1 ∧ IsPar εV (!q) z.2 := by
  obtain ⟨a, b⟩ := z
  unfold IsPar hatε
  simp only [LinearMap.prodMap_apply, LinearMap.neg_apply, Prod.smul_mk, Prod.mk.injEq,
    LInf.σ_not, neg_smul]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [← h2, neg_neg]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h2, neg_neg]⟩

end hat

/-! ## Functoriality of the extension -/

section hatfun

variable {α : Type*} [LinearOrder α]

omit [Module R V] [AddCommGroup V] in
/-- Flipping the parity of one input changes the sign of a partition by the inputs whose order
with it is reversed. -/
lemma sgn_flip (q : α → Bool) (r : α → α) {S : Finset α} {s : α} (hs : s ∈ S) :
    sgn R (Function.update q s (!q s)) r S = sgn R q r S *
      ∏ y ∈ S, if (y < s ∧ r s < r y) ∨ (s < y ∧ r y < r s) then σ R (q y) else 1 := by
  classical
  have key : ∀ x y, (if y < x ∧ r x < r y then
      σ R (Function.update q s (!q s) x && Function.update q s (!q s) y) else 1)
      = (if y < x ∧ r x < r y then σ R (q x && q y) else 1) *
        ((if x = s then (if y < x ∧ r x < r y then σ R (q y) else 1) else 1) *
          (if y = s then (if y < x ∧ r x < r y then σ R (q x) else 1) else 1)) := by
    intro x y
    by_cases hc : y < x ∧ r x < r y
    · have hxy : x ≠ y := fun e => (e ▸ hc.1).false
      by_cases hx : x = s
      · subst hx
        have hy : y ≠ x := Ne.symm hxy
        rw [Function.update_self, Function.update_of_ne hy, if_pos hc, if_pos hc, if_pos rfl,
          if_pos hc, if_neg hy, mul_one]
        cases q x <;> cases q y <;> simp [σ]
      · by_cases hy : y = s
        · subst hy
          rw [Function.update_self, Function.update_of_ne hx, if_pos hc, if_pos hc, if_neg hx,
            if_pos rfl, if_pos hc, one_mul]
          cases q x <;> cases q y <;> simp [σ]
        · rw [Function.update_of_ne hx, Function.update_of_ne hy, if_neg hx, if_neg hy, if_pos hc,
            mul_one, mul_one]
    · simp only [if_neg hc, ite_self, mul_one]
  unfold sgn
  simp only [key, Finset.prod_mul_distrib]
  congr 1
  have h1 : ∏ x ∈ S, ∏ y ∈ S, (if x = s then (if y < x ∧ r x < r y then σ R (q y) else 1)
      else 1) = ∏ y ∈ S, (if y < s ∧ r s < r y then σ R (q y) else 1) := by
    have e : ∀ x, ∏ y ∈ S, (if x = s then (if y < x ∧ r x < r y then σ R (q y) else 1) else 1)
        = if x = s then ∏ y ∈ S, (if y < s ∧ r s < r y then σ R (q y) else 1) else 1 := by
      intro x
      by_cases hx : x = s
      · subst hx
        simp only [if_true]
      · simp only [if_neg hx, Finset.prod_const_one]
    rw [Finset.prod_congr rfl fun x _ => e x, Finset.prod_ite_eq' S s, if_pos hs]
  rw [h1]
  have h2 : ∏ x ∈ S, ∏ y ∈ S, (if y = s then (if y < x ∧ r x < r y then σ R (q x) else 1) else 1)
      = ∏ x ∈ S, (if s < x ∧ r x < r s then σ R (q x) else 1) := by
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [Finset.prod_ite_eq' S s, if_pos hs]
  rw [h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun y _ => ?_
  by_cases h1 : y < s ∧ r s < r y
  · have h3 : ¬ (s < y ∧ r y < r s) := fun h => (lt_asymm h1.1 h.1)
    rw [if_pos h1, if_neg h3, if_pos (Or.inl h1), mul_one]
  · by_cases h3 : s < y ∧ r y < r s
    · rw [if_neg h1, if_pos h3, if_pos (Or.inr h3), one_mul]
    · rw [if_neg h1, if_neg h3, if_neg (by tauto), mul_one]

omit [Module R V] [AddCommGroup V] in
lemma sum_fix_blk {M : Type*} [AddCommMonoid M] {S : Finset α} {r : α → α} (hr : IsRoot S r)
    (f : α → α → M) : ∑ m ∈ fix r S, ∑ s ∈ blk r S m, f m s = ∑ s ∈ S, f (r s) s := by
  conv_rhs => rw [← biUnion_blk hr]
  rw [Finset.sum_biUnion fun m _ m' _ h => disjoint_blk r S h]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun s hs => ?_
  rw [(mem_blk.1 hs).2]

omit [Module R V] [AddCommGroup V] in
lemma prod_fix_blk {M : Type*} [CommMonoid M] {S : Finset α} {r : α → α} (hr : IsRoot S r)
    (f : α → α → M) : ∏ m ∈ fix r S, ∏ s ∈ blk r S m, f m s = ∏ s ∈ S, f (r s) s := by
  conv_rhs => rw [← biUnion_blk hr]
  rw [Finset.prod_biUnion fun m _ m' _ h => disjoint_blk r S h]
  refine Finset.prod_congr rfl fun m _ => Finset.prod_congr rfl fun s hs => ?_
  rw [(mem_blk.1 hs).2]

lemma ev_update_sum (G : Ser R W X) (w : α → W) {M : Finset α} {m : α} (hm : m ∈ M) {ι : Type*}
    (s : Finset ι) (f : ι → W) :
    ev G (Function.update w m (∑ i ∈ s, f i)) M = ∑ i ∈ s, ev G (Function.update w m (f i)) M := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    have := (ev_update G w hm 0 0 0).2
    rwa [zero_smul, zero_smul] at this
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, (ev_update G w hm _ _ 1).1, ih]

lemma ev_univ (F : Ser R V W) {k : ℕ} (v : Fin k → V) : ev F v Finset.univ = F k v := by
  rw [ev_eq F v Finset.univ (Finset.card_fin k)]
  congr 1
  have := Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset (Fin k))) (Finset.card_fin k)
    (f := id) (fun _ => Finset.mem_univ _) strictMono_id
  rw [← this]
  rfl

end hatfun

/-! ## The extension of a composite -/

section hatcomp

variable [Invertible (2 : R)] {εV : V →ₗ[R] V} {εW : W →ₗ[R] W}

omit [Invertible (2 : R)] in
lemma isPar_eps {b : Bool} {x : V} (hx : IsPar εV b x) : IsPar εV b (εV x) := by
  unfold IsPar at *
  rw [hx, map_smul, hx]

omit [Invertible (2 : R)] in
lemma isPar_tw {α : Type*} [LinearOrder α] {q : α → Bool} {w : α → V × V}
    (hw : ∀ i, IsPar (hatε εV) (q i) (w i)) (s : α) (m : α) :
    IsPar εV (Function.update q s (!q s) m) (tw εV w s m) := by
  classical
  unfold tw
  by_cases hms : m = s
  · subst hms
    rw [Function.update_self, if_neg (lt_irrefl m), if_pos rfl]
    exact ((isPar_hat εV).1 (hw m)).2
  · rw [Function.update_of_ne hms]
    split_ifs
    · exact isPar_eps ((isPar_hat εV).1 (hw m)).1
    · exact ((isPar_hat εV).1 (hw m)).1

/-- **The extension of a composite is the composite of the extensions**, on homogeneous
inputs. -/
theorem hat_comp_homog (G : Ser R W X) (F : Ser R V W) (hF : IsEven εV εW F) {k : ℕ}
    {q : Fin k → Bool} {w : Fin k → V × V} (hw : ∀ i, IsPar (hatε εV) (q i) (w i)) :
    hat εV (comp εV G F) k w = cmp (hat εW G) (ev (hat εV F) w) q Finset.univ := by
  classical
  have hw1 : ∀ i, IsPar εV (q i) (w i).1 := fun i => ((isPar_hat εV).1 (hw i)).1
  set base : Finset (Fin k) → W := ev F fun m => (w m).1 with hbase
  rw [← ev_univ, ev_hat, ev_comp_homog G F fun a _ => hw1 a]
  have hs : ∀ s, ev (comp εV G F) (tw εV w s) Finset.univ
      = cmp G (ev F (tw εV w s)) (Function.update q s (!q s)) Finset.univ := fun s =>
    ev_comp_homog G F fun m _ => isPar_tw hw s m
  simp only [hs]
  unfold cmp
  ext
  · simp only [Prod.fst_sum, Prod.smul_fst, ev_hat]
  · simp only [Prod.snd_sum, Prod.smul_snd]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' := mem_roots.1 hr
    -- the plain values of the blocks, with the signs of the inputs `θ` passes
    have hbase_par : ∀ m, IsPar εW (par q (blk r Finset.univ m)) (base (blk r Finset.univ m)) :=
      fun m => isPar_ev hF fun a _ => hw1 a
    -- the right-hand side, input by input
    have hR : ∀ m ∈ fix r Finset.univ,
        ev G (tw εW (fun m' => ev (hat εV F) w (blk r Finset.univ m')) m) (fix r Finset.univ)
        = ∑ s ∈ blk r Finset.univ m,
          (∏ m' ∈ fix r Finset.univ, if m' < m then σ R (par q (blk r Finset.univ m')) else 1) •
            ev G (Function.update (fun m' => base (blk r Finset.univ m')) m
              (ev F (tw εV w s) (blk r Finset.univ m))) (fix r Finset.univ) := by
      intro m hm
      have e1 : ∀ m' ∈ fix r Finset.univ,
          tw εW (fun m' => ev (hat εV F) w (blk r Finset.univ m')) m m'
          = (if m' < m then σ R (par q (blk r Finset.univ m')) else 1) •
            Function.update (fun m' => base (blk r Finset.univ m')) m
              (∑ s ∈ blk r Finset.univ m, ev F (tw εV w s) (blk r Finset.univ m)) m' := by
        intro m' _
        rw [tw_apply εW]
        simp only [ev_hat]
        by_cases h1 : m' < m
        · rw [if_pos h1, if_pos h1, Function.update_of_ne h1.ne]
          exact hbase_par m'
        · rw [if_neg h1, if_neg h1, one_smul]
          by_cases h2 : m' = m
          · subst h2
            rw [if_pos rfl, Function.update_self]
          · rw [if_neg h2, Function.update_of_ne h2]
      rw [ev_congr G e1, ev_smul, ev_update_sum G _ hm, Finset.smul_sum]
    rw [ev_hat, Finset.sum_congr rfl hR]
    simp only [Finset.smul_sum]
    rw [sum_fix_blk hr']
    refine Finset.sum_congr rfl fun s _ => ?_
    -- the left-hand side
    have hL : ∀ m ∈ fix r Finset.univ, ev F (tw εV w s) (blk r Finset.univ m)
        = (if m = r s then 1 else ∏ a ∈ blk r Finset.univ m, if a < s then σ R (q a) else 1) •
          Function.update (fun m' => base (blk r Finset.univ m')) (r s)
            (ev F (tw εV w s) (blk r Finset.univ (r s))) m := by
      intro m _
      by_cases hm : m = r s
      · subst hm
        rw [if_pos rfl, one_smul, Function.update_self]
      · rw [if_neg hm, Function.update_of_ne hm, hbase, ← ev_smul]
        refine ev_congr F fun a ha => ?_
        have has : a ≠ s := fun e => hm (by rw [← (mem_blk.1 ha).2, e])
        unfold tw
        rw [if_neg has]
        by_cases h1 : a < s
        · rw [if_pos h1, if_pos h1]
          exact hw1 a
        · rw [if_neg h1, if_neg h1, one_smul]
    rw [ev_congr G hL, ev_smul, smul_smul, smul_smul]
    congr 1
    -- the signs
    rw [sgn_flip q r (Finset.mem_univ s)]
    have e2 : ∏ m ∈ fix r Finset.univ,
        (if m = r s then 1 else ∏ a ∈ blk r Finset.univ m, if a < s then σ R (q a) else 1)
        = ∏ a ∈ Finset.univ, if r a = r s then 1 else if a < s then σ R (q a) else 1 := by
      rw [← prod_fix_blk hr' fun m a => if m = r s then 1 else if a < s then σ R (q a) else 1]
      refine Finset.prod_congr rfl fun m _ => ?_
      by_cases hm : m = r s
      · rw [if_pos hm]
        simp [hm]
      · rw [if_neg hm]
        simp [hm]
    have e3 : ∏ m' ∈ fix r Finset.univ,
        (if m' < r s then σ R (par q (blk r Finset.univ m')) else 1)
        = ∏ a ∈ Finset.univ, if r a < r s then σ R (q a) else 1 := by
      rw [← prod_fix_blk hr' fun m' a => if m' < r s then σ R (q a) else 1]
      refine Finset.prod_congr rfl fun m' _ => ?_
      by_cases hm : m' < r s
      · rw [if_pos hm, σ_par]
        simp [hm]
      · rw [if_neg hm]
        simp [hm]
    rw [e2, e3, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun a _ => ?_
    have hσ := LInf.σ_mul_self (R := R) (q a)
    rcases lt_trichotomy (r a) (r s) with h | h | h
    · have hne : a ≠ s := fun e => h.ne (by rw [e])
      have h' : ¬ r a = r s := h.ne
      rcases lt_or_gt_of_ne hne with h2 | h2
      · simp [h, h', h2, not_lt.2 h2.le, not_lt.2 h.le]
      · simp [h, h', h2, not_lt.2 h2.le]
    · simp [h]
    · have h' : ¬ r a = r s := h.ne'
      have h'' : ¬ r a < r s := not_lt.2 h.le
      by_cases h2 : a < s
      · simp [h, h', h'', h2, hσ]
      · simp [h, h', h'', h2]

end hatcomp

/-! ## ∞-morphisms -/

section morph

variable [Invertible (2 : R)] {εV : V →ₗ[R] V} {εW : W →ₗ[R] W} {εX : X →ₗ[R] X}

omit [Invertible (2 : R)] in
/-- **Composites of even series on homogeneous values have the parity of the inputs.** -/
lemma isPar_cmp {α : Type*} [LinearOrder α] [Fintype α] {G : Ser R W X} (hG : IsEven εW εX G)
    {Φ : Finset α → W} {p : α → Bool} {S : Finset α}
    (hΦ : ∀ B ⊆ S, IsPar εW (par p B) (Φ B)) : IsPar εX (par p S) (cmp G Φ p S) := by
  unfold cmp
  refine LInfT.isPar_sum _ fun r hr => LInfT.isPar_smul _ ?_
  have hr' := mem_roots.1 hr
  have h1 := isPar_ev (S := fix r S) (p := fun m => par p (blk r S m)) hG
    fun m _ => hΦ _ (Finset.filter_subset _ _)
  refine isPar_of_σ_eq ?_ h1
  rw [σ_par, σ_par]
  simp only [σ_par]
  exact prod_fix_blk hr' fun _ a => σ R (p a)

variable (εV) in
/-- **The identity series**: the identity in arity one, zero elsewhere. -/
noncomputable def idSer : Ser R V V := fun k =>
  match k with
  | 1 => MultilinearMap.ofSubsingleton R V V 0 LinearMap.id
  | _ => 0

/-- **The series of an L∞[1]-structure**, `β_ℓ = (id, ℓ) : V ⇝ V ⊕ θV`. -/
noncomputable def beta (ℓ : Ser R V V) : Ser R V (V × V) := fun k => (idSer k).prod (ℓ k)

/-- **An odd series** anticommutes with the parity operator. -/
def IsOdd (εV : V →ₗ[R] V) (ℓ : Ser R V V) : Prop :=
  ∀ k (v : Fin k → V), ℓ k (fun i => εV (v i)) = -εV (ℓ k v)

omit [Invertible (2 : R)] in
lemma idSer_even : IsEven εV εV (idSer (R := R) (V := V)) := by
  intro k v
  match k with
  | 1 => rfl
  | 0 => simp [idSer]
  | k + 2 => simp [idSer]

omit [Invertible (2 : R)] in
lemma beta_even {ℓ : Ser R V V} (hℓ : IsOdd εV ℓ) : IsEven εV (hatε εV) (beta ℓ) := by
  intro k v
  unfold beta hatε
  simp only [MultilinearMap.prod_apply, LinearMap.prodMap_apply, LinearMap.neg_apply,
    idSer_even k v, hℓ k v]

/-- **An ∞-morphism of L∞[1]-algebras** `(V, ℓ) ⇝ (W, ℓ')`: an even series `F` with
`F̂ ∘ β_ℓ = β_ℓ' ∘ F`, the composites taken along the partitions of the inputs with their Koszul
signs. -/
structure IsInfMorph (εV : V →ₗ[R] V) (εW : W →ₗ[R] W) (ℓ : Ser R V V) (ℓ' : Ser R W W)
    (F : Ser R V W) : Prop where
  even : IsEven εV εW F
  eq : comp εV (hat εV F) (beta ℓ) = comp εV (beta ℓ') F

/-- **Composites of even series are even.** -/
lemma comp_even (hεV : ∀ x, εV (εV x) = x) {G : Ser R W X} {F : Ser R V W}
    (hG : IsEven εW εX G) (hF : IsEven εV εW F) : IsEven εV εX (comp εV G F) := by
  intro k v
  have key : (comp εV G F k).compLinearMap (fun _ => εV)
      = εX.compMultilinearMap (comp εV G F k) := by
    refine ext_homog hεV fun q w hw => ?_
    rw [MultilinearMap.compLinearMap_apply, LinearMap.compMultilinearMap_apply]
    have e1 : (fun i => εV (w i)) = fun i => σ R (q i) • w i := funext hw
    rw [e1, MultilinearMap.map_smul_univ, comp_homog G F hw]
    have h2 := isPar_cmp hG (Φ := ev F w) (p := q) (S := Finset.univ)
      fun B _ => isPar_ev hF fun a _ => hw a
    unfold IsPar at h2
    rw [h2, ← σ_par]
  exact congrArg (fun f : MultilinearMap R (fun _ : Fin k => V) X => f v) key

omit [Invertible (2 : R)] in
lemma hatε_invol (hεV : ∀ x, εV (εV x) = x) (z : V × V) : hatε εV (hatε εV z) = z := by
  obtain ⟨a, b⟩ := z
  simp [hatε, hεV]

/-- **The extension of a composite**, as series. -/
theorem hat_comp (hεV : ∀ x, εV (εV x) = x) (G : Ser R W X) (F : Ser R V W)
    (hF : IsEven εV εW F) :
    hat εV (comp εV G F) = comp (hatε εV) (hat εW G) (hat εV F) := by
  funext k
  refine ext_homog (hatε_invol hεV) fun q w hw => ?_
  rw [hat_comp_homog G F hF hw, comp_homog _ _ hw]

/-- **∞-morphisms compose.** -/
theorem IsInfMorph.comp (hεV : ∀ x, εV (εV x) = x)
    {ℓ : Ser R V V} {ℓ' : Ser R W W} {ℓ'' : Ser R X X} (hℓ : IsOdd εV ℓ)
    {F : Ser R V W} {G : Ser R W X} (hF : IsInfMorph εV εW ℓ ℓ' F)
    (hG : IsInfMorph εW εX ℓ' ℓ'' G) : IsInfMorph εV εX ℓ ℓ'' (LSer.comp εV G F) := by
  refine ⟨comp_even hεV hG.even hF.even, ?_⟩
  rw [hat_comp hεV G F hF.even,
    ← comp_assoc hεV (hat εW G) (hat εV F) (beta ℓ) (beta_even hℓ), hF.eq,
    comp_assoc hεV (hat εW G) (beta ℓ') F hF.even, hG.eq,
    ← comp_assoc hεV (beta ℓ'') G F hF.even]

end morph

/-! ## Moving the first input -/

section move

omit [Module R V] [AddCommGroup V] in
/-- Inserting at the next position is inserting and exchanging two adjacent inputs. -/
lemma insertNth_succ {β : Type*} {m : ℕ} (x : β) (u : Fin m → β) (j : Fin m) :
    Fin.insertNth j.succ x u = Fin.insertNth j.castSucc x u ∘ Equiv.swap j.castSucc j.succ := by
  rw [Fin.insertNth_eq_iff]
  refine ⟨by simp, ?_⟩
  funext i
  simp only [Fin.removeNth_apply, Function.comp_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · have h1 : j.succ.succAbove i = i.castSucc :=
      Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simp; omega)
    have h2 : (j.castSucc).succAbove i = i.castSucc :=
      Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_castSucc_iff.2 h)
    rw [h1, Equiv.swap_apply_of_ne_of_ne (fun e => h.ne (Fin.castSucc_injective _ e))
      (fun e => by rw [Fin.ext_iff] at e; simp at e; omega), ← h2,
      Fin.insertNth_apply_succAbove]
  · have h1 : i.succ.succAbove i = i.castSucc :=
      Fin.succAbove_of_castSucc_lt _ _ Fin.castSucc_lt_succ
    have h2 : (i.castSucc).succAbove i = i.succ := Fin.succAbove_of_le_castSucc _ _ le_rfl
    rw [h1, Equiv.swap_apply_left, ← h2, Fin.insertNth_apply_succAbove]
  · have h1 : j.succ.succAbove i = i.succ :=
      Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)
    have h2 : (j.castSucc).succAbove i = i.succ :=
      Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)
    rw [h1, Equiv.swap_apply_of_ne_of_ne (fun e => by rw [Fin.ext_iff] at e; simp at e; omega)
      (fun e => h.ne' (Fin.succ_injective _ e)), ← h2, Fin.insertNth_apply_succAbove]

variable {εV : V →ₗ[R] V}

/-- **A graded symmetric series**: exchanging two adjacent homogeneous inputs costs their Koszul
sign. -/
def IsGSymm (εV : V →ₗ[R] V) (F : Ser R V W) : Prop :=
  ∀ k (p : Fin k → Bool) (v : Fin k → V), (∀ a, IsPar εV (p a) (v a)) →
    ∀ (i : ℕ) (h : i + 1 < k), F k (v ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, h⟩) =
      σ R (p ⟨i, by omega⟩ && p ⟨i + 1, h⟩) • F k v

/-- **Moving the first input to the position `j`** costs the Koszul sign of the inputs it
passes. -/
lemma gsymm_insertNth {F : Ser R V W} (hF : IsGSymm εV F) {m : ℕ} {x : V} {qx : Bool}
    (hx : IsPar εV qx x) {u : Fin m → V} {pu : Fin m → Bool} (hu : ∀ i, IsPar εV (pu i) (u i)) :
    ∀ (j : ℕ) (hj : j ≤ m), F (m + 1) (Fin.insertNth ⟨j, by omega⟩ x u)
      = (∏ i ∈ Finset.univ.filter (fun i : Fin m => i.val < j), σ R (qx && pu i)) •
        F (m + 1) (Fin.cons x u) := by
  intro j
  induction j with
  | zero =>
    intro _
    have h0 : (⟨0, by omega⟩ : Fin (m + 1)) = 0 := rfl
    rw [h0, Fin.insertNth_zero']
    simp
  | succ j ih =>
    intro hj
    have hjm : j < m := by omega
    have e1 : (⟨j + 1, by omega⟩ : Fin (m + 1)) = (⟨j, hjm⟩ : Fin m).succ := rfl
    have e2 : (⟨j, by omega⟩ : Fin (m + 1)) = (⟨j, hjm⟩ : Fin m).castSucc := rfl
    rw [e1, insertNth_succ, ← e2]
    have hw : ∀ a, IsPar εV
        ((Fin.insertNth (⟨j, by omega⟩ : Fin (m + 1)) qx pu : Fin (m + 1) → Bool) a)
        ((Fin.insertNth (⟨j, by omega⟩ : Fin (m + 1)) x u : Fin (m + 1) → V) a) := by
      intro a
      induction a using (⟨j, by omega⟩ : Fin (m + 1)).succAboveCases with
      | x => simp only [Fin.insertNth_apply_same]; exact hx
      | p a => simp only [Fin.insertNth_apply_succAbove]; exact hu a
    have h3 := hF (m + 1) _ _ hw j (by omega)
    rw [show (⟨j + 1, by omega⟩ : Fin (m + 1)) = (⟨j, hjm⟩ : Fin m).succ from rfl] at h3
    rw [h3, ih (by omega), smul_smul]
    congr 1
    have hq1 : (Fin.insertNth (⟨j, by omega⟩ : Fin (m + 1)) qx pu : Fin (m + 1) → Bool)
        ⟨j, by omega⟩ = qx :=
      Fin.insertNth_apply_same _ _ _
    have hq2 : (Fin.insertNth (⟨j, by omega⟩ : Fin (m + 1)) qx pu : Fin (m + 1) → Bool)
        (⟨j, hjm⟩ : Fin m).succ = pu ⟨j, hjm⟩ := by
      have : (⟨j, hjm⟩ : Fin m).succ = (⟨j, by omega⟩ : Fin (m + 1)).succAbove ⟨j, hjm⟩ :=
        (Fin.succAbove_of_le_castSucc _ _ le_rfl).symm
      rw [this, Fin.insertNth_apply_succAbove]
    rw [hq1, hq2]
    have hs : Finset.univ.filter (fun i : Fin m => i.val < j + 1)
        = insert ⟨j, hjm⟩ (Finset.univ.filter (fun i : Fin m => i.val < j)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    rw [hs, Finset.prod_insert (by simp), mul_comm]

end move

/-! ## Partitions with one block of several inputs -/

section oneRoot

variable {α : Type*} [LinearOrder α]

/-- The partition with the block `T` of least input `m`, the other inputs alone. -/
noncomputable def oneRoot (m : α) (T : Finset α) : α → α := by
  classical
  exact fun x => if x ∈ T then m else x

/-- The blocks of least input `m`. -/
noncomputable def blocksAt (S : Finset α) (m : α) : Finset (Finset α) := by
  classical
  exact (S.filter (m ≤ ·)).powerset.filter (m ∈ ·)

omit [Module R V] [AddCommGroup V] in
lemma mem_blocksAt {S T : Finset α} {m : α} :
    T ∈ blocksAt S m ↔ T ⊆ S ∧ (∀ x ∈ T, m ≤ x) ∧ m ∈ T := by
  classical
  unfold blocksAt
  rw [Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff, Finset.subset_iff]
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun x hx => (h1 hx).1, fun x hx => (h1 hx).2, h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun x hx => ⟨h1 hx, h2 x hx⟩, h3⟩

omit [Module R V] [AddCommGroup V] in
lemma oneRoot_of_mem {m x : α} {T : Finset α} (hx : x ∈ T) : oneRoot m T x = m := by
  classical
  unfold oneRoot
  rw [if_pos hx]

omit [Module R V] [AddCommGroup V] in
lemma oneRoot_of_notMem {m x : α} {T : Finset α} (hx : x ∉ T) : oneRoot m T x = x := by
  classical
  unfold oneRoot
  rw [if_neg hx]

omit [Module R V] [AddCommGroup V] in
lemma isRoot_oneRoot {S T : Finset α} {m : α} (hT : T ∈ blocksAt S m) :
    IsRoot S (oneRoot m T) := by
  obtain ⟨h1, h2, h3⟩ := mem_blocksAt.1 hT
  refine ⟨fun x hx => ?_, fun x hx => oneRoot_of_notMem fun h => hx (h1 h), fun x => ?_,
    fun x => ?_⟩
  · by_cases h : x ∈ T
    · rw [oneRoot_of_mem h]
      exact h1 h3
    · rw [oneRoot_of_notMem h]
      exact hx
  · by_cases h : x ∈ T
    · rw [oneRoot_of_mem h, oneRoot_of_mem h3]
    · rw [oneRoot_of_notMem h, oneRoot_of_notMem h]
  · by_cases h : x ∈ T
    · rw [oneRoot_of_mem h]
      exact h2 x h
    · rw [oneRoot_of_notMem h]

omit [Module R V] [AddCommGroup V] in
lemma blk_oneRoot {S T : Finset α} {m : α} (hT : T ∈ blocksAt S m) :
    blk (oneRoot m T) S m = T := by
  obtain ⟨h1, h2, h3⟩ := mem_blocksAt.1 hT
  ext x
  rw [mem_blk]
  constructor
  · rintro ⟨hx, hxm⟩
    by_contra h
    rw [oneRoot_of_notMem h] at hxm
    exact h (hxm ▸ h3)
  · intro hx
    exact ⟨h1 hx, oneRoot_of_mem hx⟩

omit [Module R V] [AddCommGroup V] in
lemma fix_oneRoot {S T : Finset α} {m : α} (hT : T ∈ blocksAt S m) :
    fix (oneRoot m T) S = insert m (S \ T) := by
  obtain ⟨h1, h2, h3⟩ := mem_blocksAt.1 hT
  ext x
  rw [mem_fix, Finset.mem_insert, Finset.mem_sdiff]
  constructor
  · rintro ⟨hx, hxx⟩
    by_cases h : x ∈ T
    · rw [oneRoot_of_mem h] at hxx
      exact Or.inl hxx.symm
    · exact Or.inr ⟨hx, h⟩
  · rintro (rfl | ⟨hx, h⟩)
    · exact ⟨h1 h3, oneRoot_of_mem h3⟩
    · exact ⟨hx, oneRoot_of_notMem h⟩

omit [Module R V] [AddCommGroup V] in
lemma blk_oneRoot_ne {S T : Finset α} {m a : α} (hT : T ∈ blocksAt S m) (ha : a ∈ S \ T) :
    blk (oneRoot m T) S a = {a} := by
  obtain ⟨h1, h2, h3⟩ := mem_blocksAt.1 hT
  obtain ⟨haS, haT⟩ := Finset.mem_sdiff.1 ha
  ext x
  rw [mem_blk, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hxa⟩
    by_cases h : x ∈ T
    · rw [oneRoot_of_mem h] at hxa
      exact absurd (hxa ▸ h3) haT
    · rwa [oneRoot_of_notMem h] at hxa
  · rintro rfl
    exact ⟨haS, oneRoot_of_notMem haT⟩

variable [Fintype α]

/-- **Sums over the partitions with a marked block, the other blocks single inputs**, as sums
over the marked blocks. -/
lemma sum_roots_marked {M : Type*} [AddCommMonoid M] (S : Finset α) (f : (α → α) → α → M)
    (hf : ∀ r ∈ roots S, ∀ m ∈ fix r S, (∃ m' ∈ fix r S, m' ≠ m ∧ (blk r S m').card ≠ 1) →
      f r m = 0) :
    ∑ r ∈ roots S, ∑ m ∈ fix r S, f r m
      = ∑ m ∈ S, ∑ T ∈ blocksAt S m, f (oneRoot m T) m := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  symm
  refine Finset.sum_bij_ne_zero (fun x _ _ => ⟨oneRoot x.1 x.2, x.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨m, T⟩ hx _
    rw [Finset.mem_sigma] at hx ⊢
    obtain ⟨hm, hT⟩ := hx
    refine ⟨mem_roots.2 (isRoot_oneRoot hT), ?_⟩
    rw [fix_oneRoot hT]
    exact Finset.mem_insert_self _ _
  · rintro ⟨m, T⟩ hx _ ⟨m', T'⟩ hx' _ h
    rw [Finset.mem_sigma] at hx hx'
    simp only [Sigma.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hmm : m = m' := eq_of_heq h2
    subst hmm
    have hTT : T = T' := by
      rw [← blk_oneRoot (show T ∈ blocksAt S m from hx.2),
        ← blk_oneRoot (show T' ∈ blocksAt S m from hx'.2), h1]
    subst hTT
    rfl
  · rintro ⟨r, m⟩ hx hne
    rw [Finset.mem_sigma] at hx
    obtain ⟨hr, hm⟩ := hx
    have hr' := mem_roots.1 hr
    set T := blk r S m
    have hT : T ∈ blocksAt S m := by
      refine mem_blocksAt.2 ⟨Finset.filter_subset _ _, fun x hx => hr'.le_of_mem_blk hx,
        mem_blk_self hm⟩
    have hreq : oneRoot m T = r := by
      funext x
      by_contra hx
      by_cases hxT : x ∈ T
      · exact hx ((oneRoot_of_mem hxT).trans (mem_blk.1 hxT).2.symm)
      · rw [oneRoot_of_notMem hxT] at hx
        by_cases hxS : x ∈ S
        · apply hne
          refine hf r hr m hm ⟨r x, hr'.root_mem_fix hxS, fun e => hxT (mem_blk.2 ⟨hxS, e⟩), ?_⟩
          intro hc
          obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hc
          have h1 : x ∈ blk r S (r x) := mem_blk.2 ⟨hxS, rfl⟩
          have h2 : r x ∈ blk r S (r x) := mem_blk_self (hr'.root_mem_fix hxS)
          rw [ha, Finset.mem_singleton] at h1 h2
          exact hx (h1.trans h2.symm)
        · exact hx (hr'.off x hxS).symm
    refine ⟨⟨m, T⟩, Finset.mem_sigma.2 ⟨(mem_fix.1 hm).1, hT⟩, ?_, ?_⟩
    · dsimp only
      rw [hreq]
      exact hne
    · dsimp only
      rw [hreq]
  · rintro ⟨m, T⟩ _ _
    rfl

end oneRoot

/-! ## Helpers for the part of `F̂ ∘ β_ℓ` in `θ` -/

section thetaHelpers

variable {α : Type*} [LinearOrder α] {εV : V →ₗ[R] V}

lemma idSer_apply_ne {k : ℕ} (hk : k ≠ 1) : (idSer : Ser R V V) k = 0 := by
  match k, hk with
  | 0, _ => rfl
  | k + 2, _ => rfl

lemma ev_idSer_of_card_ne (v : α → V) {B : Finset α} (hB : B.card ≠ 1) :
    ev (idSer : Ser R V V) v B = 0 := by
  unfold ev
  rw [idSer_apply_ne hB, MultilinearMap.zero_apply]

lemma ev_idSer_singleton (v : α → V) (a : α) : ev (idSer : Ser R V V) v {a} = v a := by
  rw [ev_eq _ v {a} (Finset.card_singleton a)]
  show (v ∘ ⇑(({a} : Finset α).orderEmbOfFin (Finset.card_singleton a))) 0 = v a
  simp only [Function.comp_apply]
  congr 1
  exact Finset.mem_singleton.1 (Finset.orderEmbOfFin_mem _ _ _)

lemma ev_coord_zero (F : Ser R V W) {w : α → V} {M : Finset α} {m : α} (hm : m ∈ M)
    (h0 : w m = 0) : ev F w M = 0 := by
  unfold ev
  refine (F M.card).map_coord_zero ((M.orderIsoOfFin rfl).symm ⟨m, hm⟩) ?_
  simp only [Function.comp_apply]
  rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  exact h0

/-- **An odd series shifts the parity of its inputs.** -/
lemma isPar_ev_odd {ℓ : Ser R V V} (hℓ : IsOdd εV ℓ) {p : α → Bool} {v : α → V} {S : Finset α}
    (hv : ∀ a ∈ S, IsPar εV (p a) (v a)) : IsPar εV (!par p S) (ev ℓ v S) := by
  have h1 : ev ℓ (fun a => εV (v a)) S = -εV (ev ℓ v S) := hℓ _ _
  have h2 : ev ℓ (fun a => εV (v a)) S = ev ℓ (fun a => σ R (p a) • v a) S :=
    ev_congr ℓ fun a ha => hv a ha
  unfold IsPar
  rw [LInf.σ_not, neg_smul, ← neg_neg (εV _), ← h1, h2, ev_smul, σ_par]

/-- **Evaluation with a new input at `m`**, as the insertion of that input. -/
lemma ev_insert (F : Ser R V W) (v : α → V) {U : Finset α} {m : α} (hm : m ∉ U) (y : V) :
    ∃ j : Fin (U.card + 1),
      ev F (Function.update v m y) (insert m U)
        = F (U.card + 1) (Fin.insertNth j y (v ∘ U.orderEmbOfFin rfl)) ∧
      ∀ i : Fin U.card, U.orderEmbOfFin rfl i < m ↔ i.castSucc < j := by
  classical
  have h : (insert m U).card = U.card + 1 := Finset.card_insert_of_notMem hm
  set oe := (insert m U).orderEmbOfFin h
  set j := ((insert m U).orderIsoOfFin h).symm ⟨m, Finset.mem_insert_self m U⟩
  have hj : oe j = m := by
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  have hne : ∀ i, oe (j.succAbove i) ≠ m := fun i e => by
    rw [← hj] at e
    exact Fin.succAbove_ne j i (oe.injective e)
  have hU : ∀ i, oe (j.succAbove i) ∈ U := fun i => by
    have := Finset.orderEmbOfFin_mem (insert m U) h (j.succAbove i)
    rcases Finset.mem_insert.1 this with e | e
    · exact absurd e (hne i)
    · exact e
  have hsub : U.orderEmbOfFin rfl = fun i => oe (j.succAbove i) :=
    (Finset.orderEmbOfFin_unique rfl hU (oe.strictMono.comp (Fin.strictMono_succAbove j))).symm
  refine ⟨j, ?_, fun i => ?_⟩
  · rw [ev_eq F _ _ h]
    congr 1
    rw [Fin.eq_insertNth_iff]
    refine ⟨?_, ?_⟩
    · show Function.update v m y (oe j) = y
      rw [hj, Function.update_self]
    · funext i
      simp only [Fin.removeNth_apply, Function.comp_apply, hsub]
      exact Function.update_of_ne (hne i) _ _
  · rw [hsub]
    simp only
    rw [← hj, oe.lt_iff_lt, Fin.succAbove_lt_iff_castSucc_lt]

omit [Module R V] [AddCommGroup V] in
/-- The sign of the partition with one block `T` of least input `m`. -/
lemma sgn_oneRoot (p : α → Bool) {S T : Finset α} {m : α} (hT : T ∈ blocksAt S m) :
    sgn R p (oneRoot m T) S
      = ∏ x ∈ T, ∏ y ∈ S \ T, if m < y ∧ y < x then σ R (p x && p y) else 1 := by
  classical
  obtain ⟨h1, h2, h3⟩ := mem_blocksAt.1 hT
  unfold sgn
  have hS : S = T ∪ (S \ T) := (Finset.union_sdiff_of_subset h1).symm
  have hd : Disjoint T (S \ T) := Finset.disjoint_sdiff
  conv_lhs => rw [hS]
  rw [Finset.prod_union hd]
  have e1 : ∏ x ∈ S \ T, ∏ y ∈ T ∪ (S \ T),
      (if y < x ∧ oneRoot m T x < oneRoot m T y then σ R (p x && p y) else 1) = 1 := by
    refine Finset.prod_eq_one fun x hx => Finset.prod_eq_one fun y hy => ?_
    obtain ⟨-, hxT⟩ := Finset.mem_sdiff.1 hx
    rw [oneRoot_of_notMem hxT, if_neg]
    rintro ⟨hyx, hxy⟩
    rcases Finset.mem_union.1 hy with hyT | hy'
    · rw [oneRoot_of_mem hyT] at hxy
      exact absurd (hyx.trans hxy) (not_lt.2 (h2 y hyT))
    · rw [oneRoot_of_notMem (Finset.mem_sdiff.1 hy').2] at hxy
      exact lt_asymm hyx hxy
  rw [e1, mul_one]
  refine Finset.prod_congr rfl fun x hx => ?_
  rw [Finset.prod_union hd]
  have e2 : ∏ y ∈ T, (if y < x ∧ oneRoot m T x < oneRoot m T y then σ R (p x && p y) else 1)
      = 1 := by
    refine Finset.prod_eq_one fun y hy => ?_
    rw [oneRoot_of_mem hx, oneRoot_of_mem hy, if_neg (fun h => lt_irrefl _ h.2)]
  rw [e2, one_mul]
  refine Finset.prod_congr rfl fun y hy => ?_
  rw [oneRoot_of_mem hx, oneRoot_of_notMem (Finset.mem_sdiff.1 hy).2]
  simp only [and_comm]

end thetaHelpers

/-! ## The part of `F̂ ∘ β_ℓ` in `θ`: inserting the structure -/

section theta

variable [Invertible (2 : R)] {εV : V →ₗ[R] V} {εW : W →ₗ[R] W}

omit [Invertible (2 : R)] in
lemma ev_beta {α : Type*} [LinearOrder α] (ℓ : Ser R V V) (v : α → V) (B : Finset α) :
    ev (beta ℓ) v B = (ev (idSer : Ser R V V) v B, ev ℓ v B) := rfl

/-- **The part of `F̂ ∘ β_ℓ` in `θ`** is the insertion of `ℓ` into `F`, the inner output first:
`∑_T ± F(ℓ(v_T), v_{Tᶜ})`, for `F` even and graded symmetric and `ℓ` odd. -/
theorem hat_beta_snd {F : Ser R V W} {ℓ : Ser R V V} (hFs : IsGSymm εV F) (hℓ : IsOdd εV ℓ)
    {n : ℕ} {p : Fin n → Bool} {v : Fin n → V} (hv : ∀ i, IsPar εV (p i) (v i)) :
    (comp εV (hat εV F) (beta ℓ) n v).2
      = ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => T.Nonempty),
        LInf.usgn (R := R) p T •
          F (Tᶜ.card + 1) (Fin.cons (ℓ T.card (LInf.restr v T)) (LInf.restr v Tᶜ)) := by
  classical
  rw [comp_homog _ _ hv]
  unfold cmp
  simp only [Prod.snd_sum, Prod.smul_snd, ev_hat, Finset.smul_sum]
  rw [sum_roots_marked Finset.univ (fun r m => sgn R p r Finset.univ •
    ev F (tw εV (fun m' => ev (beta ℓ) v (blk r Finset.univ m')) m) (fix r Finset.univ))]
  swap
  · rintro r - m - ⟨m', hm', hne, hc⟩
    rw [ev_coord_zero F hm', smul_zero]
    rw [tw_apply, ev_beta, ev_idSer_of_card_ne v hc, if_neg hne]
    split_ifs <;> simp
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => x.2)
    (fun T hT => ⟨T.min' (Finset.mem_filter.1 hT).2, T⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨m, T⟩ hx
    rw [Finset.mem_sigma] at hx
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨m, (mem_blocksAt.1 hx.2).2.2⟩⟩
  · intro T hT
    have hTn := (Finset.mem_filter.1 hT).2
    rw [Finset.mem_sigma]
    exact ⟨Finset.mem_univ _, mem_blocksAt.2 ⟨Finset.subset_univ _,
      fun x hx => Finset.min'_le T x hx, Finset.min'_mem T hTn⟩⟩
  · rintro ⟨m, T⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨-, h2, h3⟩ := mem_blocksAt.1 hx.2
    have : T.min' ⟨m, h3⟩ = m := le_antisymm (Finset.min'_le T m h3)
      (Finset.le_min' T ⟨m, h3⟩ m h2)
    simp only [this]
  · intro T _
    rfl
  · rintro ⟨m, T⟩ hx
    rw [Finset.mem_sigma] at hx
    have hT := hx.2
    obtain ⟨-, h2, h3⟩ := mem_blocksAt.1 hT
    dsimp only
    set U := Finset.univ \ T with hUdef
    have hmU : m ∉ U := fun h => (Finset.mem_sdiff.1 h).2 h3
    have hval : ∀ m' ∈ insert m U,
        tw εV (fun m' => ev (beta ℓ) v (blk (oneRoot m T) Finset.univ m')) m m'
        = (if m' < m then σ R (p m') else 1) • Function.update v m (ev ℓ v T) m' := by
      intro m' hm'
      rw [tw_apply]
      by_cases he : m' = m
      · subst he
        rw [if_neg (lt_irrefl _), if_pos rfl, if_neg (lt_irrefl _), one_smul, Function.update_self,
          ev_beta, blk_oneRoot hT]
      · have hm'U : m' ∈ U := (Finset.mem_insert.1 hm').resolve_left he
        rw [if_neg he, Function.update_of_ne he, ev_beta, blk_oneRoot_ne hT hm'U,
          ev_idSer_singleton]
        by_cases hlt : m' < m
        · rw [if_pos hlt, if_pos hlt]
          exact hv m'
        · rw [if_neg hlt, if_neg hlt, one_smul]
    rw [fix_oneRoot hT, ev_congr F hval, ev_smul]
    obtain ⟨j, hj1, hj2⟩ := ev_insert F v hmU (ev ℓ v T)
    rw [hj1]
    have hy := isPar_ev_odd hℓ (S := T) fun a _ => hv a
    have hu : ∀ i, IsPar εV (p (U.orderEmbOfFin rfl i)) ((v ∘ U.orderEmbOfFin rfl) i) :=
      fun i => hv _
    have hg := gsymm_insertNth hFs hy hu j.val (Nat.lt_succ_iff.1 j.isLt)
    rw [show (⟨j.val, by omega⟩ : Fin (U.card + 1)) = j from rfl] at hg
    rw [hg, smul_smul, smul_smul, Finset.compl_eq_univ_sdiff]
    congr 1
    -- the signs
    have e1 : ∏ i ∈ Finset.univ.filter (fun i : Fin U.card => i.val < j.val),
        σ R ((!par p T) && p (U.orderEmbOfFin rfl i))
        = ∏ y ∈ U, if y < m then σ R ((!par p T) && p y) else 1 := by
      rw [Finset.prod_filter]
      conv_rhs => rw [← Finset.map_orderEmbOfFin_univ U rfl, Finset.prod_map]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [RelEmbedding.coe_toEmbedding]
      have : i.val < j.val ↔ U.orderEmbOfFin rfl i < m := by
        rw [hj2 i, Fin.lt_def]
        rfl
      simp only [this]
    have e2 : ∏ a ∈ insert m U, (if a < m then σ R (p a) else 1)
        = ∏ y ∈ U, if y < m then σ R (p y) else 1 := by
      rw [Finset.prod_insert hmU, if_neg (lt_irrefl _), one_mul]
    have e3 := sgn_oneRoot (R := R) p hT
    have e4 : LInf.usgn (R := R) p T
        = ∏ x ∈ T, ∏ y ∈ U, if y < x then σ R (p x && p y) else 1 := by
      unfold LInf.usgn
      rw [Finset.compl_eq_univ_sdiff]
      refine Finset.prod_congr rfl fun x _ => ?_
      rw [Finset.prod_filter]
    rw [e1, e2, e3, e4, Finset.prod_comm (s := T) (t := U),
      Finset.prod_comm (s := T) (t := U) (f := fun x y => if y < x then σ R (p x && p y) else 1),
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun y hy => ?_
    have hyT : y ∉ T := (Finset.mem_sdiff.1 hy).2
    have hym : y ≠ m := fun e => hyT (e ▸ h3)
    by_cases hlt : y < m
    · have hall : ∀ x ∈ T, y < x := fun x hx => lt_of_lt_of_le hlt (h2 x hx)
      rw [if_pos hlt, if_pos hlt, Finset.prod_eq_one (fun x _ => if_neg (fun h => absurd
        (h.1.trans hlt) (lt_irrefl _))), one_mul,
        Finset.prod_congr rfl fun x hx => if_pos (hall x hx), ← σ_par_and, σ_and_not]
    · have hgt : m < y := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hym)
      rw [if_neg hlt, if_neg hlt, mul_one, mul_one]
      refine Finset.prod_congr rfl fun x _ => ?_
      simp only [hgt, true_and]

end theta

/-! ## The first components, and composites into a dg Lie algebra -/

section first

variable [Invertible (2 : R)] {εV : V →ₗ[R] V} {εW : W →ₗ[R] W}

/-- **The first component of `F̂ ∘ β_ℓ` is `F`.** -/
theorem hat_beta_fst (F : Ser R V W) (ℓ : Ser R V V) {n : ℕ} {p : Fin n → Bool} {v : Fin n → V}
    (hv : ∀ i, IsPar εV (p i) (v i)) : (comp εV (hat εV F) (beta ℓ) n v).1 = F n v := by
  classical
  rw [comp_homog _ _ hv]
  unfold cmp
  simp only [Prod.fst_sum, Prod.smul_fst, ev_hat, ev_beta]
  have hid : IsRoot (Finset.univ : Finset (Fin n)) id :=
    ⟨fun x _ => Finset.mem_univ _, fun x hx => absurd (Finset.mem_univ x) hx, fun _ => rfl,
      fun _ => le_rfl⟩
  rw [Finset.sum_eq_single id]
  · have hsgn : sgn R p id Finset.univ = 1 := by
      unfold sgn
      exact Finset.prod_eq_one fun x _ => Finset.prod_eq_one fun y _ =>
        if_neg fun h => lt_asymm h.1 h.2
    have hfix : fix id (Finset.univ : Finset (Fin n)) = Finset.univ := by
      ext x
      simp [mem_fix]
    rw [hsgn, one_smul, hfix, ← ev_univ F v]
    refine ev_congr F fun m _ => ?_
    have hb : blk id (Finset.univ : Finset (Fin n)) m = {m} := by
      ext x
      simp [mem_blk]
    rw [hb, ev_idSer_singleton]
  · intro r hr hne
    have hr' := mem_roots.1 hr
    obtain ⟨x, hx⟩ : ∃ x, r x ≠ x := by
      by_contra h
      push Not at h
      exact hne (funext h)
    have hfix := hr'.root_mem_fix (Finset.mem_univ x)
    rw [ev_coord_zero F hfix, smul_zero]
    refine ev_idSer_of_card_ne v fun hc => ?_
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hc
    have h1 : x ∈ blk r Finset.univ (r x) := mem_blk.2 ⟨Finset.mem_univ _, rfl⟩
    have h2 : r x ∈ blk r Finset.univ (r x) := mem_blk_self hfix
    rw [ha, Finset.mem_singleton] at h1 h2
    exact hx (h2.trans h1.symm)
  · intro h
    exact absurd (mem_roots.2 hid) h

/-- **The first component of `β_ℓ' ∘ F` is `F`**, on at least one input. -/
theorem beta_comp_fst (F : Ser R V W) (ℓ' : Ser R W W) {n : ℕ} (hn : 0 < n)
    {p : Fin n → Bool} {v : Fin n → V} (hv : ∀ i, IsPar εV (p i) (v i)) :
    (comp εV (beta ℓ') F n v).1 = F n v := by
  classical
  rw [comp_homog _ _ hv]
  unfold cmp
  simp only [Prod.fst_sum, Prod.smul_fst, ev_beta]
  set z : Fin n := ⟨0, hn⟩
  have hz : ∀ x, z ≤ x := fun x => by
    rw [Fin.le_def]
    exact Nat.zero_le _
  have hc : IsRoot (Finset.univ : Finset (Fin n)) (fun _ => z) :=
    ⟨fun _ _ => Finset.mem_univ _, fun x hx => absurd (Finset.mem_univ x) hx, fun _ => rfl,
      fun x => hz x⟩
  rw [Finset.sum_eq_single (fun _ => z)]
  · have hsgn : sgn R p (fun _ => z) Finset.univ = 1 := by
      unfold sgn
      exact Finset.prod_eq_one fun x _ => Finset.prod_eq_one fun y _ =>
        if_neg fun h => lt_irrefl _ h.2
    have hfix : fix (fun _ => z) (Finset.univ : Finset (Fin n)) = {z} := by
      ext x
      simp only [mem_fix, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact eq_comm
    have hb : blk (fun _ => z) (Finset.univ : Finset (Fin n)) z = Finset.univ := by
      ext x
      simp [mem_blk]
    rw [hsgn, one_smul, hfix, ev_idSer_singleton, hb, ev_univ]
  · intro r hr hne
    have hr' := mem_roots.1 hr
    rw [ev_idSer_of_card_ne _ fun hc => hne ?_, smul_zero]
    obtain ⟨m, hm⟩ := Finset.card_eq_one.1 hc
    have hrz : r z = z := le_antisymm (hr'.le z) (hz _)
    have hzf : z ∈ fix r Finset.univ := mem_fix.2 ⟨Finset.mem_univ _, hrz⟩
    rw [hm, Finset.mem_singleton] at hzf
    funext x
    have := hr'.root_mem_fix (Finset.mem_univ x)
    rw [hm, Finset.mem_singleton] at this
    rw [this, hzf]
  · intro h
    exact absurd (mem_roots.2 hc) h

end first

/-! ## Composites into an L∞-structure in arities one and two -/

section twoTarget

variable [Invertible (2 : R)] {εV : V →ₗ[R] V} {εW : W →ₗ[R] W}

/-- The partition into the block `S` of least input `z` and its complement. -/
noncomputable def twoRoot {n : ℕ} (z : Fin n) (S : Finset (Fin n))
    (h : (Finset.univ \ S).Nonempty) :
    Fin n → Fin n := by
  classical
  exact fun x => if x ∈ S then z else (Finset.univ \ S).min' h

/-- The splittings whose first part holds the least input. -/
noncomputable def splitsAt {n : ℕ} (z : Fin n) : Finset (Finset (Fin n)) := by
  classical
  exact (splits (Finset.univ : Finset (Fin n))).filter (z ∈ ·)

lemma compl_nonempty_of_mem_splits {n : ℕ} {S : Finset (Fin n)}
    (hS : S ∈ splits (Finset.univ : Finset (Fin n))) : (Finset.univ \ S).Nonempty := by
  have := sdiff_mem_splits hS
  exact (mem_splits.1 this).2.1

/-- **The partitions into two blocks**, by the block of the least input. -/
lemma sum_roots_two {M : Type*} [AddCommMonoid M] {n : ℕ} (hn : 0 < n)
    (f : (Fin n → Fin n) → M) :
    ∑ r ∈ (roots (Finset.univ : Finset (Fin n))).filter (fun r => (fix r Finset.univ).card = 2),
        f r
      = ∑ S ∈ (splits (Finset.univ : Finset (Fin n))).attach.filter
          (fun S => (⟨0, hn⟩ : Fin n) ∈ S.1),
        f (twoRoot ⟨0, hn⟩ S.1 (compl_nonempty_of_mem_splits S.2)) := by
  classical
  set z : Fin n := ⟨0, hn⟩
  have hz : ∀ x, z ≤ x := fun x => by rw [Fin.le_def]; exact Nat.zero_le _
  symm
  refine Finset.sum_bij' (fun S _ => twoRoot z S.1 (compl_nonempty_of_mem_splits S.2))
    (fun r hr => ⟨blk r Finset.univ z, ?_⟩) ?_ ?_ ?_ ?_ ?_
  · -- the block of the least input is a splitting
    rw [Finset.mem_filter] at hr
    have hr' := mem_roots.1 hr.1
    have hrz : r z = z := le_antisymm (hr'.le z) (hz _)
    have hzf : z ∈ fix r Finset.univ := mem_fix.2 ⟨Finset.mem_univ _, hrz⟩
    obtain ⟨m2, hm2, hne⟩ : ∃ m2 ∈ fix r Finset.univ, m2 ≠ z := by
      by_contra h
      push Not at h
      have : fix r Finset.univ ⊆ {z} := fun x hx => Finset.mem_singleton.2 (h x hx)
      have := Finset.card_le_card this
      rw [hr.2, Finset.card_singleton] at this
      omega
    refine mem_splits.2 ⟨Finset.filter_subset _ _, ⟨z, mem_blk_self hzf⟩, fun e => ?_⟩
    have : m2 ∈ blk r Finset.univ z := by rw [e]; exact Finset.mem_univ _
    exact hne ((mem_blk.1 this).2.symm.trans (mem_fix.1 hm2).2).symm
  · rintro ⟨S, hS⟩ hx
    rw [Finset.mem_filter] at hx ⊢
    have hc := compl_nonempty_of_mem_splits hS
    set m2 := (Finset.univ \ S).min' hc
    have hm2 : m2 ∉ S := (Finset.mem_sdiff.1 (Finset.min'_mem _ hc)).2
    have hroot : IsRoot (Finset.univ : Finset (Fin n)) (twoRoot z S hc) := by
      refine ⟨fun _ _ => Finset.mem_univ _, fun x hx => absurd (Finset.mem_univ x) hx,
        fun x => ?_, fun x => ?_⟩
      · unfold twoRoot
        by_cases h : x ∈ S
        · rw [if_pos h, if_pos hx.2]
        · rw [if_neg h, if_neg hm2]
      · unfold twoRoot
        by_cases h : x ∈ S
        · rw [if_pos h]
          exact hz x
        · rw [if_neg h]
          exact Finset.min'_le _ x (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, h⟩)
    refine ⟨mem_roots.2 hroot, ?_⟩
    have : fix (twoRoot z S hc) Finset.univ = {z, m2} := by
      ext x
      rw [mem_fix, Finset.mem_insert, Finset.mem_singleton]
      unfold twoRoot
      constructor
      · rintro ⟨-, h⟩
        by_cases hx : x ∈ S
        · rw [if_pos hx] at h
          exact Or.inl h.symm
        · rw [if_neg hx] at h
          exact Or.inr h.symm
      · rintro (rfl | rfl)
        · exact ⟨Finset.mem_univ _, by rw [if_pos hx.2]⟩
        · exact ⟨Finset.mem_univ _, by rw [if_neg hm2]⟩
    rw [this, Finset.card_pair (fun e => hm2 (by rw [← e]; exact hx.2))]
  · intro r hr
    rw [Finset.mem_filter] at hr ⊢
    have hr' := mem_roots.1 hr.1
    have hrz : r z = z := le_antisymm (hr'.le z) (hz _)
    exact ⟨Finset.mem_attach _ _, mem_blk_self (mem_fix.2 ⟨Finset.mem_univ _, hrz⟩)⟩
  · rintro ⟨S, hS⟩ hx
    rw [Finset.mem_filter] at hx
    apply Subtype.ext
    ext x
    rw [mem_blk]
    unfold twoRoot
    dsimp only
    constructor
    · rintro ⟨-, h⟩
      by_contra hxS
      rw [if_neg hxS] at h
      have := Finset.min'_mem _ (compl_nonempty_of_mem_splits hS)
      rw [h] at this
      exact (Finset.mem_sdiff.1 this).2 hx.2
    · intro hxS
      exact ⟨Finset.mem_univ _, by rw [if_pos hxS]⟩
  · intro r hr
    rw [Finset.mem_filter] at hr
    have hr' := mem_roots.1 hr.1
    have hrz : r z = z := le_antisymm (hr'.le z) (hz _)
    funext x
    unfold twoRoot
    dsimp only
    by_cases hx : x ∈ blk r Finset.univ z
    · rw [if_pos hx, (mem_blk.1 hx).2]
    · rw [if_neg hx]
      have hc : (Finset.univ \ blk r Finset.univ z).Nonempty := ⟨x, by simpa using hx⟩
      -- the other least input
      have hxf := hr'.root_mem_fix (Finset.mem_univ x)
      have hrx : r x ≠ z := fun e => hx (mem_blk.2 ⟨Finset.mem_univ _, e⟩)
      have hfix : fix r Finset.univ = {z, r x} := by
        refine (Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_).symm
        · rcases Finset.mem_insert.1 hy with rfl | hy
          · exact mem_fix.2 ⟨Finset.mem_univ _, hrz⟩
          · rw [Finset.mem_singleton.1 hy]
            exact hxf
        · rw [hr.2, Finset.card_pair (Ne.symm hrx)]
      refine le_antisymm (Finset.min'_le _ _ ?_) (Finset.le_min' _ _ _ fun y hy => ?_)
      · refine Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun h => hrx ?_⟩
        have := (mem_blk.1 h).2
        rwa [hr'.idem] at this
      · have hy' : y ∉ blk r Finset.univ z := (Finset.mem_sdiff.1 hy).2
        have hyf := hr'.root_mem_fix (Finset.mem_univ y)
        rw [hfix, Finset.mem_insert, Finset.mem_singleton] at hyf
        rcases hyf with h | h
        · exact absurd (mem_blk.2 ⟨Finset.mem_univ _, h⟩) hy'
        · rw [← h]
          exact hr'.le y
  · intro S _
    rfl

end twoTarget

section twoTarget2

variable [Invertible (2 : R)] {εV : V →ₗ[R] V} {εW : W →ₗ[R] W}

omit [Invertible (2 : R)] in
lemma ev_two_pair {n : ℕ} (d : W →ₗ[R] W) (b : End R W 2) (w : Fin n → W) {i j : Fin n}
    (hij : i < j) : ev (LInf.two (HTT.op1 d) b) w {i, j} = b ![w i, w j] := by
  have hc : ({i, j} : Finset (Fin n)).card = 2 := Finset.card_pair hij.ne
  rw [ev_eq _ w _ hc]
  have hoe : ({i, j} : Finset (Fin n)).orderEmbOfFin hc = ![i, j] :=
    (Finset.orderEmbOfFin_unique hc (fun x => by fin_cases x <;> simp)
      (LInf.strictMono_vec2 hij)).symm
  rw [hoe]
  show b (w ∘ ![i, j]) = _
  congr 1
  funext x
  fin_cases x <;> rfl

omit [Invertible (2 : R)] in
lemma ev_two_single {α : Type*} [LinearOrder α] (d : W →ₗ[R] W) (b : End R W 2) (w : α → W)
    (a : α) : ev (LInf.two (HTT.op1 d) b) w {a} = d (w a) := by
  rw [ev_eq _ w _ (Finset.card_singleton a)]
  show HTT.op1 d (w ∘ _) = _
  rw [HTT.op1_apply]
  simp only [Function.comp_apply]
  congr 1
  exact congrArg w (Finset.mem_singleton.1 (Finset.orderEmbOfFin_mem _ _ _))

omit [Invertible (2 : R)] in
lemma ev_two_of_card {α : Type*} [LinearOrder α] (d : W →ₗ[R] W) (b : End R W 2) (w : α → W)
    {M : Finset α} (h1 : M.card ≠ 1) (h2 : M.card ≠ 2) :
    ev (LInf.two (HTT.op1 d) b) w M = 0 := by
  unfold ev
  rcases Nat.lt_or_ge M.card 3 with h | h
  · have h0 : M.card = 0 := by omega
    rw [show (LInf.two (HTT.op1 d) b) M.card = 0 by rw [h0]; rfl]
    rfl
  · rw [LInf.two_of_ge _ _ h]
    rfl

omit [Invertible (2 : R)] in
/-- The sign of a partition into two blocks is the unshuffle sign of the first. -/
lemma sgn_twoRoot {n : ℕ} (p : Fin n → Bool) {z : Fin n} (hz : ∀ x, z ≤ x) {S : Finset (Fin n)}
    (hzS : z ∈ S) (hc : (Finset.univ \ S).Nonempty) :
    sgn R p (twoRoot z S hc) Finset.univ = LInf.usgn (R := R) p S := by
  classical
  set m2 := (Finset.univ \ S).min' hc
  have hm2 : m2 ∉ S := (Finset.mem_sdiff.1 (Finset.min'_mem _ hc)).2
  have hzm : z < m2 := lt_of_le_of_ne (hz m2) fun e => hm2 (e ▸ hzS)
  have ht : ∀ x, twoRoot z S hc x = if x ∈ S then z else m2 := fun _ => rfl
  have key : ∀ x y, (if y < x ∧ twoRoot z S hc x < twoRoot z S hc y then σ R (p x && p y) else 1)
      = if x ∈ S ∧ (y ∉ S ∧ y < x) then σ R (p x && p y) else 1 := by
    intro x y
    rw [ht, ht]
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · simp [hx, hy]
    · simp only [hx, hy, if_true, if_false, hzm, and_true, not_false_eq_true, true_and]
    · simp only [hx, hy, if_true, if_false, false_and]
      rw [if_neg fun h => absurd (hzm.trans h.2) (lt_irrefl _)]
    · simp [hx, hy]
  unfold sgn LInf.usgn
  simp only [key]
  calc (∏ x, ∏ y, if x ∈ S ∧ y ∉ S ∧ y < x then σ R (p x && p y) else 1)
      = ∏ x, if x ∈ S then ∏ y, (if y ∈ Sᶜ.filter (· < x) then σ R (p x && p y) else 1)
          else 1 := by
        refine Finset.prod_congr rfl fun x _ => ?_
        by_cases hx : x ∈ S
        · rw [if_pos hx]
          refine Finset.prod_congr rfl fun y _ => ?_
          simp only [hx, true_and, Finset.mem_filter, Finset.mem_compl]
        · rw [if_neg hx]
          exact Finset.prod_eq_one fun y _ => by simp [hx]
    _ = ∏ x ∈ S, ∏ y, (if y ∈ Sᶜ.filter (· < x) then σ R (p x && p y) else 1) := by
        rw [Finset.prod_ite_mem, Finset.univ_inter]
    _ = _ := Finset.prod_congr rfl fun x _ => by rw [Finset.prod_ite_mem, Finset.univ_inter]

lemma twoRoot_facts {n : ℕ} {z : Fin n} (hz : ∀ x, z ≤ x) {S : Finset (Fin n)} (hzS : z ∈ S)
    (hc : (Finset.univ \ S).Nonempty) :
    z < (Finset.univ \ S).min' hc ∧
      fix (twoRoot z S hc) Finset.univ = {z, (Finset.univ \ S).min' hc} ∧
      blk (twoRoot z S hc) Finset.univ z = S ∧
      blk (twoRoot z S hc) Finset.univ ((Finset.univ \ S).min' hc) = Sᶜ := by
  classical
  set m2 := (Finset.univ \ S).min' hc
  have hm2 : m2 ∉ S := (Finset.mem_sdiff.1 (Finset.min'_mem _ hc)).2
  have hzm : z < m2 := lt_of_le_of_ne (hz m2) fun e => hm2 (e ▸ hzS)
  have ht : ∀ x, twoRoot z S hc x = if x ∈ S then z else m2 := fun x => rfl
  refine ⟨hzm, ?_, ?_, ?_⟩
  · ext x
    rw [mem_fix, Finset.mem_insert, Finset.mem_singleton, ht]
    constructor
    · rintro ⟨-, h⟩
      by_cases hx : x ∈ S
      · rw [if_pos hx] at h
        exact Or.inl h.symm
      · rw [if_neg hx] at h
        exact Or.inr h.symm
    · rintro (rfl | rfl)
      · exact ⟨Finset.mem_univ _, by rw [if_pos hzS]⟩
      · exact ⟨Finset.mem_univ _, by rw [if_neg hm2]⟩
  · ext x
    rw [mem_blk, ht]
    constructor
    · rintro ⟨-, h⟩
      by_contra hx
      rw [if_neg hx] at h
      exact hzm.ne h.symm
    · intro hx
      exact ⟨Finset.mem_univ _, by rw [if_pos hx]⟩
  · ext x
    rw [mem_blk, ht, Finset.mem_compl]
    constructor
    · rintro ⟨-, h⟩ hx
      rw [if_pos hx] at h
      exact hzm.ne h
    · intro hx
      exact ⟨Finset.mem_univ _, by rw [if_neg hx]⟩

omit [Invertible (2 : R)] in
/-- Pairing a splitting with its complement halves the sum of the brackets. -/
lemma sum_splits_brackets {b : End R W 2}
    (hbs : ∀ p q x y, IsPar εW p x → IsPar εW q y → b ![y, x] = σ R (p && q) • b ![x, y])
    {F : Ser R V W} (hF : IsEven εV εW F) {n : ℕ} (z : Fin n) {p : Fin n → Bool}
    {v : Fin n → V} (hv : ∀ i, IsPar εV (p i) (v i)) :
    ∑ S ∈ splits (Finset.univ : Finset (Fin n)), LInf.usgn (R := R) p S • b ![ev F v S, ev F v Sᶜ]
      = (2 : R) • ∑ S ∈ (splits (Finset.univ : Finset (Fin n))).filter (z ∈ ·),
        LInf.usgn (R := R) p S • b ![ev F v S, ev F v Sᶜ] := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not _ (z ∈ ·), two_smul]
  congr 1
  symm
  refine Finset.sum_nbij' (fun S => Sᶜ) (fun S => Sᶜ) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    dsimp only
    rw [Finset.mem_filter] at hS ⊢
    refine ⟨?_, by simpa using hS.2⟩
    rw [Finset.compl_eq_univ_sdiff]
    exact sdiff_mem_splits hS.1
  · intro S hS
    dsimp only
    rw [Finset.mem_filter] at hS ⊢
    refine ⟨?_, by simpa using hS.2⟩
    rw [Finset.compl_eq_univ_sdiff]
    exact sdiff_mem_splits hS.1
  · intro S _
    exact compl_compl S
  · intro S _
    exact compl_compl S
  · intro S _
    dsimp only
    rw [compl_compl]
    have hS := isPar_ev hF (p := p) (v := v) (S := S) fun a _ => hv a
    have hSc := isPar_ev hF (p := p) (v := v) (S := Sᶜ) fun a _ => hv a
    rw [hbs _ _ _ _ hS hSc, smul_smul]
    congr 1
    have h1 : LInf.usgn (R := R) p S = ks R p S Sᶜ := rfl
    have h2 : LInf.usgn (R := R) p Sᶜ = ks R p Sᶜ S := by
      show ks R p Sᶜ Sᶜᶜ = _
      rw [compl_compl]
    rw [h1, h2, ← ks_mul_ks p disjoint_compl_right]
    have := ks_mul_self (R := R) p Sᶜ S
    linear_combination (-(ks R p S Sᶜ)) * this

/-- **A composite into an L∞-structure in arities one and two**: `d ∘ F` and half the signed sum
of the brackets over the splittings. -/
theorem cmp_two {d : W →ₗ[R] W} {b : End R W 2}
    (hbs : ∀ p q x y, IsPar εW p x → IsPar εW q y → b ![y, x] = σ R (p && q) • b ![x, y])
    {F : Ser R V W} (hF : IsEven εV εW F) {n : ℕ} (hn : 0 < n) {p : Fin n → Bool}
    {v : Fin n → V} (hv : ∀ i, IsPar εV (p i) (v i)) :
    cmp (LInf.two (HTT.op1 d) b) (ev F v) p Finset.univ
      = d (F n v) + (⅟2 : R) • ∑ S ∈ splits (Finset.univ : Finset (Fin n)),
        LInf.usgn (R := R) p S • b ![ev F v S, ev F v Sᶜ] := by
  classical
  set z : Fin n := ⟨0, hn⟩
  have hz : ∀ x, z ≤ x := fun x => by rw [Fin.le_def]; exact Nat.zero_le _
  set f : (Fin n → Fin n) → W := fun r => sgn R p r Finset.univ •
    ev (LInf.two (HTT.op1 d) b) (fun m => ev F v (blk r Finset.univ m)) (fix r Finset.univ)
  unfold cmp
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun r => (fix r Finset.univ).card = 1),
    ← Finset.sum_filter_add_sum_filter_not ((roots Finset.univ).filter
      fun r => ¬ (fix r Finset.univ).card = 1) (fun r => (fix r Finset.univ).card = 2)]
  have hrest : ∑ r ∈ ((roots Finset.univ).filter fun r => ¬ (fix r Finset.univ).card = 1).filter
      (fun r => ¬ (fix r Finset.univ).card = 2), f r = 0 := by
    refine Finset.sum_eq_zero fun r hr => ?_
    simp only [Finset.mem_filter] at hr
    show sgn R p r Finset.univ • _ = 0
    rw [ev_two_of_card d b _ hr.1.2 hr.2, smul_zero]
  have hone : ∑ r ∈ (roots Finset.univ).filter (fun r => (fix r Finset.univ).card = 1), f r
      = d (F n v) := by
    have hc : IsRoot (Finset.univ : Finset (Fin n)) (fun _ => z) :=
      ⟨fun _ _ => Finset.mem_univ _, fun x hx => absurd (Finset.mem_univ x) hx, fun _ => rfl,
        fun x => hz x⟩
    have hfix : fix (fun _ => z) (Finset.univ : Finset (Fin n)) = {z} := by
      ext x
      simp only [mem_fix, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact eq_comm
    rw [Finset.sum_eq_single (fun _ => z)]
    · show sgn R p (fun _ => z) Finset.univ • _ = _
      have hsgn : sgn R p (fun _ => z) Finset.univ = 1 := by
        unfold sgn
        exact Finset.prod_eq_one fun x _ => Finset.prod_eq_one fun y _ =>
          if_neg fun h => lt_irrefl _ h.2
      have hb : blk (fun _ => z) (Finset.univ : Finset (Fin n)) z = Finset.univ := by
        ext x
        simp [mem_blk]
      rw [hsgn, one_smul, hfix, ev_two_single, hb, ev_univ]
    · intro r hr hne
      simp only [Finset.mem_filter] at hr
      exfalso
      obtain ⟨m, hm⟩ := Finset.card_eq_one.1 hr.2
      have hr' := mem_roots.1 hr.1
      have hrz : r z = z := le_antisymm (hr'.le z) (hz _)
      have hzf : z ∈ fix r Finset.univ := mem_fix.2 ⟨Finset.mem_univ _, hrz⟩
      rw [hm, Finset.mem_singleton] at hzf
      apply hne
      funext x
      have := hr'.root_mem_fix (Finset.mem_univ x)
      rw [hm, Finset.mem_singleton] at this
      rw [this, hzf]
    · intro h
      exfalso
      apply h
      rw [Finset.mem_filter, hfix, Finset.card_singleton]
      exact ⟨mem_roots.2 hc, rfl⟩
  have htwo : ∑ r ∈ ((roots Finset.univ).filter fun r => ¬ (fix r Finset.univ).card = 1).filter
      (fun r => (fix r Finset.univ).card = 2), f r
      = ∑ S ∈ (splits (Finset.univ : Finset (Fin n))).filter (z ∈ ·),
        LInf.usgn (R := R) p S • b ![ev F v S, ev F v Sᶜ] := by
    rw [Finset.filter_filter]
    have e1 : ((roots (Finset.univ : Finset (Fin n))).filter fun r =>
        ¬ (fix r Finset.univ).card = 1 ∧ (fix r Finset.univ).card = 2)
        = (roots Finset.univ).filter fun r => (fix r Finset.univ).card = 2 := by
      ext r
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨h1, -, h2⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by omega, h2⟩
    rw [e1, sum_roots_two hn f, Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_attach (splits Finset.univ) (fun S => if z ∈ S then
        LInf.usgn (R := R) p S • b ![ev F v S, ev F v Sᶜ] else 0)]
    refine Finset.sum_congr rfl fun S _ => ?_
    by_cases hzS : z ∈ S.1
    · rw [if_pos hzS, if_pos hzS]
      have hc := compl_nonempty_of_mem_splits S.2
      obtain ⟨hzm, hfix, hbz, hbm⟩ := twoRoot_facts hz hzS hc
      show sgn R p (twoRoot z S.1 hc) Finset.univ • _ = _
      rw [sgn_twoRoot p hz hzS hc, hfix, ev_two_pair d b _ hzm, hbz, hbm]
    · rw [if_neg hzS, if_neg hzS]
  rw [hone, htwo, hrest, add_zero, sum_splits_brackets hbs hF z hv, smul_smul,
    invOf_mul_self, one_smul]

end twoTarget2

/-! ## `i∞` is an ∞-morphism -/

section transfer

variable [Invertible (2 : R)] {εV : V →ₗ[R] V} {εW : W →ₗ[R] W}

lemma beta_comp_snd (ℓ' : Ser R W W) (F : Ser R V W) {n : ℕ} {p : Fin n → Bool}
    {v : Fin n → V} (hv : ∀ i, IsPar εV (p i) (v i)) :
    (comp εV (beta ℓ') F n v).2 = cmp ℓ' (ev F v) p Finset.univ := by
  rw [comp_homog _ _ hv]
  unfold cmp
  simp only [Prod.snd_sum, Prod.smul_snd, ev_beta]

lemma beta_comp_fst_zero (ℓ' : Ser R W W) (F : Ser R V W) {p : Fin 0 → Bool} {v : Fin 0 → V}
    (hv : ∀ i, IsPar εV (p i) (v i)) : (comp εV (beta ℓ') F 0 v).1 = 0 := by
  rw [comp_homog _ _ hv]
  unfold cmp
  simp only [Prod.fst_sum, Prod.smul_fst, ev_beta]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [ev_idSer_of_card_ne _ (by simp [Finset.univ_eq_empty, fix]), smul_zero]

variable {d e h : V →ₗ[R] V} {b : End R V 2}

/-- **The trees are even.** -/
lemma ft_even (hε : ∀ x, εV (εV x) = x) (hL : LInfT.ShLie εV d b) (hr : HTT.Retract εV d e h) :
    IsEven εV εV (LInfT.ft εV e h b) := by
  intro k v
  have key : (LInfT.ft εV e h b k).compLinearMap (fun _ => εV)
      = εV.compMultilinearMap (LInfT.ft εV e h b k) := by
    refine ext_homog hε fun q w hw => ?_
    rw [MultilinearMap.compLinearMap_apply, LinearMap.compMultilinearMap_apply]
    have e1 : (fun i => εV (w i)) = fun i => σ R (q i) • w i := funext hw
    rw [e1, MultilinearMap.map_smul_univ, LInfT.ft_homog hw]
    have h2 := (LInfT.isPar_tree hL.b_odd hr q w hw _ Finset.univ rfl).1
    unfold IsPar at h2
    rw [h2, ← σ_par]
  exact congrArg (fun f : MultilinearMap R (fun _ : Fin k => V) V => f v) key

/-- **The trees are graded symmetric.** -/
lemma ft_gsymm : IsGSymm εV (LInfT.ft εV e h b) := by
  intro k p v hv i hik
  have haa : (⟨i, by omega⟩ : Fin k) < ⟨i + 1, hik⟩ := Fin.mk_lt_mk.2 (Nat.lt_succ_self i)
  have hadj : ∀ z : Fin k, ¬ ((⟨i, by omega⟩ : Fin k) < z ∧ z < ⟨i + 1, hik⟩) := by
    rintro z ⟨h1, h2⟩
    rw [Fin.lt_def] at h1 h2
    simp only at h1 h2
    omega
  rw [LInfT.ft_homog (p := p ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, hik⟩)
    (v := v ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, hik⟩) fun a => hv _, LInfT.ft_homog hv,
    LInfT.tree_swap b e h p v haa hadj _ Finset.univ rfl, Finset.map_univ_equiv]
  unfold LInfT.cs
  rw [if_pos ⟨Finset.mem_univ _, Finset.mem_univ _⟩]

/-- **The transferred structure is odd.** -/
lemma lt_odd (hε : ∀ x, εV (εV x) = x) (hL : LInfT.ShLie εV d b) (hr : HTT.Retract εV d e h) :
    IsOdd εV (LInfT.lt εV d e h b) := by
  intro k v
  have := (LInfT.isLInf_lt hε hL hr).odd k v
  rw [pow_one, neg_one_smul] at this
  exact this

/-- **The trees form an ∞-morphism `i∞`** from the transferred L∞[1]-structure to the dg Lie
algebra, in the sense of `IsInfMorph`. -/
theorem ft_isInfMorph (hε : ∀ x, εV (εV x) = x) (hL : LInfT.ShLie εV d b)
    (hr : HTT.Retract εV d e h) :
    IsInfMorph εV εV (LInfT.lt εV d e h b) (LInf.two (HTT.op1 d) b) (LInfT.ft εV e h b) := by
  refine ⟨ft_even hε hL hr, ?_⟩
  funext k
  refine ext_homog hε fun q v hv => Prod.ext ?_ ?_
  · rw [hat_beta_fst _ _ hv]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [beta_comp_fst_zero _ _ hv, LInfT.ft_homog hv, Finset.univ_eq_empty, LInfT.tree_empty]
    · rw [beta_comp_fst _ _ hk hv]
  · rw [hat_beta_snd ft_gsymm (lt_odd hε hL hr) hv, beta_comp_snd _ _ hv]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [Finset.sum_eq_zero fun T hT => absurd (Finset.mem_filter.1 hT).2 (by
        rw [Finset.eq_empty_of_isEmpty T]
        exact Finset.not_nonempty_empty)]
      unfold cmp
      refine (Finset.sum_eq_zero fun r _ => ?_).symm
      rw [ev_two_of_card d b _ (by simp [fix]) (by simp [fix]), smul_zero]
    · rw [LInfT.ft_morph hL hr q v hv, cmp_two hL.symm (ft_even hε hL hr) hk hv]
      rfl

/-- **The homotopy transfer theorem for dg Lie algebras, with the ∞-morphism**: for an
L∞[1]-structure `(d, b)` concentrated in arities one and two and a retraction `(e, h)`, the trees
`i∞` form an ∞-morphism from the transferred L∞[1]-structure to `(d, b)`. -/
theorem isInfMorph_transfer (hε : ∀ x, εV (εV x) = x)
    (H : LInf.IsLInf εV (LInf.two (HTT.op1 d) b)) (hr : HTT.Retract εV d e h) :
    IsInfMorph εV εV (LInfT.lt εV d e h b) (LInf.two (HTT.op1 d) b) (LInfT.ft εV e h b) :=
  ft_isInfMorph hε (LInfT.ShLie.of_isLInf hε H) hr

end transfer

/-! ## The identity -/

section identity

variable [Invertible (2 : R)] {εV : V →ₗ[R] V}

omit [Invertible (2 : R)] in
lemma idSer_gsymm : IsGSymm εV (idSer : Ser R V V) := by
  intro k p v _ i hik
  rw [idSer_apply_ne (by omega), MultilinearMap.zero_apply, MultilinearMap.zero_apply, smul_zero]

/-- **The identity is an ∞-morphism** of an L∞[1]-structure without operation of arity zero. -/
theorem isInfMorph_id (hε : ∀ x, εV (εV x) = x) {ℓ : Ser R V V} (hℓ : IsOdd εV ℓ)
    (hℓ0 : ∀ v, ℓ 0 v = 0) : IsInfMorph εV εV ℓ ℓ idSer := by
  classical
  refine ⟨idSer_even, ?_⟩
  funext k
  refine ext_homog hε fun q v hv => Prod.ext ?_ ?_
  · rw [hat_beta_fst _ _ hv]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [beta_comp_fst_zero _ _ hv]
      rfl
    · rw [beta_comp_fst _ _ hk hv]
  · rw [hat_beta_snd idSer_gsymm hℓ hv, beta_comp_snd _ _ hv]
    unfold cmp
    have hid : IsRoot (Finset.univ : Finset (Fin k)) id :=
      ⟨fun x _ => Finset.mem_univ _, fun x hx => absurd (Finset.mem_univ x) hx, fun _ => rfl,
        fun _ => le_rfl⟩
    rw [Finset.sum_eq_single id]
    · have hsgn : sgn R q id Finset.univ = 1 := by
        unfold sgn
        exact Finset.prod_eq_one fun x _ => Finset.prod_eq_one fun y _ =>
          if_neg fun h => lt_asymm h.1 h.2
      have hfix : fix id (Finset.univ : Finset (Fin k)) = Finset.univ := by
        ext x
        simp [mem_fix]
      have hval : ev ℓ (fun m => ev (idSer : Ser R V V) v (blk id Finset.univ m)) Finset.univ
          = ev ℓ v Finset.univ := by
        refine ev_congr ℓ fun m _ => ?_
        have hb : blk id (Finset.univ : Finset (Fin k)) m = {m} := by
          ext x
          simp [mem_blk]
        rw [hb, ev_idSer_singleton]
      rw [hsgn, one_smul, hfix, hval, ev_univ]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [Finset.sum_eq_zero fun T hT => absurd (Finset.mem_filter.1 hT).2 (by
          rw [Finset.eq_empty_of_isEmpty T]
          exact Finset.not_nonempty_empty), hℓ0]
      · rw [Finset.sum_eq_single Finset.univ]
        · have hu : LInf.usgn (R := R) q Finset.univ = 1 := by
            unfold LInf.usgn
            simp
          rw [Finset.compl_univ, hu, one_smul]
          show (ℓ Finset.univ.card (LInf.restr v Finset.univ)) = ℓ k v
          rw [← ev_univ ℓ v]
          rfl
        · intro T hT hne
          have hc : Tᶜ.card ≠ 0 := by
            intro h0
            exact hne (by rw [Finset.card_eq_zero, Finset.compl_eq_empty_iff] at h0; exact h0)
          rw [idSer_apply_ne (by omega), MultilinearMap.zero_apply, smul_zero]
        · intro h
          exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.univ_nonempty_iff.2
            ⟨⟨0, hk⟩⟩⟩) h
    · intro r hr hne
      have hr' := mem_roots.1 hr
      obtain ⟨x, hx⟩ : ∃ x, r x ≠ x := by
        by_contra h
        push Not at h
        exact hne (funext h)
      have hfix := hr'.root_mem_fix (Finset.mem_univ x)
      rw [ev_coord_zero ℓ hfix, smul_zero]
      refine ev_idSer_of_card_ne v fun hc => ?_
      obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hc
      have h1 : x ∈ blk r Finset.univ (r x) := mem_blk.2 ⟨Finset.mem_univ _, rfl⟩
      have h2 : r x ∈ blk r Finset.univ (r x) := mem_blk_self hfix
      rw [ha, Finset.mem_singleton] at h1 h2
      exact hx (h2.trans h1.symm)
    · intro h
      exact absurd (mem_roots.2 hid) h

end identity

end LSer

end Operad
