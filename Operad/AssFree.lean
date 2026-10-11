/-
# Algebras over `Ass` are associative algebras, and the free one is the tensor algebra

`Sym.Ass R A` is free on the linear orders on `A`, the empty order included. An algebra over `Ass`
on a module `V` acts by an order as the product in that order.

* **Ordered lists** (`Operad.Sym.LinOrd.toList`): the elements of a finite set in a linear order,
  the unique sorted list of them (`Operad.Sym.LinOrd.eq_toList`). Relabelling maps the list, and
  composing inserts the inner list at the place of the input (`Operad.Sym.LinOrd.toList_map`,
  `Operad.Sym.LinOrd.toList_comp`); so **ordered products** in a monoid are compatible with
  relabelling and composition (`Operad.Sym.LinOrd.oprod_map`, `Operad.Sym.LinOrd.oprod_comp`).
* `Operad.Sym.AssAlg.toRing`, `Operad.Sym.AssAlg.toAlgebra`: **the associative algebra of an
  `Ass`-algebra**, with product the action of the standard order on two inputs and unit the
  action of the empty order; an order acts as the ordered product (`Operad.Sym.AssAlg.act_eq`).
* `Operad.Sym.AssAlg.ofAlgebra`: **the `Ass`-algebra of an associative algebra**; the two
  constructions are inverse, and the morphisms of `Ass`-algebras between associative algebras
  are the algebra morphisms (`Operad.Sym.AssAlg.homEquiv`).
* **The free `Ass`-algebra on `V` is the tensor algebra of `V`**
  (`Operad.Schur.tensorAlgebraEquiv`).
-/
import Operad.ComAlgebra
import Operad.Regular
import Mathlib.LinearAlgebra.TensorAlgebra.Basic

universe u v w x

namespace Operad

namespace Sym

namespace LinOrd

variable {A B : Type} [Fintype A] [Fintype B]

/-! ## Ordered lists -/

/-- **The elements in the order** `ℓ`, from the least. -/
noncomputable def toList (ℓ : LinOrd A) : List A := List.ofFn fun k => ℓ.toRank.symm k

lemma pairwise_toList (ℓ : LinOrd A) : ℓ.toList.Pairwise ℓ.lt := by
  rw [toList, List.pairwise_ofFn]
  intro i j hij
  rw [ℓ.lt_iff_rank_lt, ← toRank_apply, ← toRank_apply, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  exact hij

lemma mem_toList (ℓ : LinOrd A) (a : A) : a ∈ ℓ.toList := by
  rw [toList, List.mem_ofFn]
  exact ⟨ℓ.toRank a, Equiv.symm_apply_apply _ _⟩

omit [Fintype A] in
lemma nodup_of_pairwise (ℓ : LinOrd A) {l : List A} (hl : l.Pairwise ℓ.lt) : l.Nodup := by
  refine hl.imp fun {a b} h => ?_
  rintro rfl
  exact ℓ.irrefl a h

/-- **The ordered list is the unique sorted list of the elements.** -/
lemma eq_toList (ℓ : LinOrd A) {l : List A} (hl : l.Pairwise ℓ.lt) (hm : ∀ a, a ∈ l) :
    l = ℓ.toList :=
  List.Perm.eq_of_pairwise (fun a _ _ _ h h' => absurd (ℓ.trans _ _ _ h h') (ℓ.irrefl a)) hl
    ℓ.pairwise_toList ((List.perm_ext_iff_of_nodup (ℓ.nodup_of_pairwise hl)
      (ℓ.nodup_of_pairwise ℓ.pairwise_toList)).2 fun a => ⟨fun _ => ℓ.mem_toList a, fun _ => hm a⟩)

/-- **Relabelling an order maps its list.** -/
lemma toList_map (e : A ≃ B) (ℓ : LinOrd A) : (map e ℓ).toList = ℓ.toList.map e := by
  refine (eq_toList _ ?_ fun b => ?_).symm
  · rw [List.pairwise_map]
    refine ℓ.pairwise_toList.imp fun {a a'} h => ?_
    show ℓ.lt (e.symm (e a)) (e.symm (e a'))
    rwa [e.symm_apply_apply, e.symm_apply_apply]
  · exact List.mem_map.2 ⟨e.symm b, ℓ.mem_toList _, e.apply_symm_apply b⟩

lemma toList_one : (LinOrd.one : LinOrd Unit).toList = [()] :=
  (eq_toList _ (List.pairwise_singleton _ _) fun u => by
    cases u
    exact List.mem_singleton_self _).symm

lemma toList_eq_nil [IsEmpty A] (ℓ : LinOrd A) : ℓ.toList = [] :=
  (eq_toList _ List.Pairwise.nil fun a => isEmptyElim a).symm

lemma toList_std (n : ℕ) : (std n).toList = List.finRange n :=
  (eq_toList _ (List.pairwise_lt_finRange n) fun k => List.mem_finRange k).symm

variable [DecidableEq A]

/-- **The list of a composite**: the inner list in the place of the input. -/
def insList (i : A) (L : List A) (L' : List B) : List (Without A i ⊕ B) :=
  L.flatMap fun a => if h : a = i then L'.map Sum.inr else [Sum.inl ⟨a, h⟩]

/-- **Composing orders inserts the inner list** at the place of the input. -/
lemma toList_comp (i : A) (ℓ : LinOrd A) (ℓ' : LinOrd B) :
    (comp i ℓ ℓ').toList = insList i ℓ.toList ℓ'.toList := by
  refine (eq_toList _ ?_ fun u => ?_).symm
  · rw [insList, List.pairwise_flatMap]
    refine ⟨fun a _ => ?_, ℓ.pairwise_toList.imp fun {a a'} h => ?_⟩
    · split_ifs with ha
      · rw [List.pairwise_map]
        exact ℓ'.pairwise_toList.imp fun h => h
      · exact List.pairwise_singleton _ _
    · intro x hx y hy
      by_cases ha : a = i <;> by_cases ha' : a' = i
      · subst ha
        subst ha'
        exact absurd h (ℓ.irrefl _)
      · rw [dif_pos ha] at hx
        rw [dif_neg ha', List.mem_singleton] at hy
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
        subst hy
        subst ha
        exact h
      · rw [dif_neg ha, List.mem_singleton] at hx
        rw [dif_pos ha'] at hy
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 hy
        subst hx
        subst ha'
        exact h
      · rw [dif_neg ha, List.mem_singleton] at hx
        rw [dif_neg ha', List.mem_singleton] at hy
        subst hx
        subst hy
        exact h
  · rcases u with a | b
    · refine List.mem_flatMap.2 ⟨a.1, ℓ.mem_toList _, ?_⟩
      rw [dif_neg a.2]
      exact List.mem_singleton_self _
    · refine List.mem_flatMap.2 ⟨i, ℓ.mem_toList _, ?_⟩
      rw [dif_pos rfl]
      exact List.mem_map_of_mem (ℓ'.mem_toList b)

/-! ## Ordered products -/

variable {M : Type*} [Monoid M]

/-- **The ordered product** of a family along an order. -/
noncomputable def oprod (ℓ : LinOrd A) (s : A → M) : M := (ℓ.toList.map s).prod

omit [DecidableEq A] in
lemma oprod_map {B : Type} [Fintype B] (e : A ≃ B) (ℓ : LinOrd A) (s : B → M) :
    oprod (map e ℓ) s = oprod ℓ fun a => s (e a) := by
  rw [oprod, oprod, toList_map, List.map_map]
  rfl

lemma oprod_comp (i : A) (ℓ : LinOrd A) (ℓ' : LinOrd B) (s : Without A i ⊕ B → M) :
    oprod (comp i ℓ ℓ') s = oprod ℓ (feed i s (oprod ℓ' fun b => s (Sum.inr b))) := by
  rw [oprod, oprod, toList_comp, insList, List.map_flatMap, List.flatMap_def, List.prod_flatten,
    List.map_map]
  congr 1
  refine List.map_congr_left fun a _ => ?_
  rw [Function.comp_apply]
  by_cases ha : a = i
  · subst ha
    rw [dif_pos rfl, feed_self, List.map_map]
    rfl
  · rw [dif_neg ha, feed_of_ne ha, List.map_singleton, List.prod_singleton]

lemma oprod_one (s : Unit → M) : oprod LinOrd.one s = s () := by
  rw [oprod, toList_one, List.map_singleton, List.prod_singleton]

/-! ## Restriction and the least element -/

omit [DecidableEq A] in
/-- **The restriction of an order** to the other elements. -/
def restrict (ℓ : LinOrd A) (i : A) : LinOrd (Without A i) where
  lt a b := ℓ.lt a.1 b.1
  irrefl a := ℓ.irrefl a.1
  trans a b c := ℓ.trans a.1 b.1 c.1
  total a b h := ℓ.total a.1 b.1 fun e => h (Subtype.ext e)

omit [Fintype A] in
/-- **An order with a least element** is the binary order with the least element first and the
restricted order inserted second. -/
lemma eq_map_split (ℓ : LinOrd A) {a₀ : A} (h : ∀ b, b ≠ a₀ → ℓ.lt a₀ b) :
    ℓ = map (ComAlg.splitEquiv a₀) (comp 1 (std 2) (ℓ.restrict a₀)) := by
  refine LinOrd.ext fun b b' => ?_
  have hsymm : ∀ c : A, (ComAlg.splitEquiv a₀).symm c =
      if hc : c = a₀ then Sum.inl ⟨0, by decide⟩ else Sum.inr ⟨c, hc⟩ := fun _ => rfl
  rw [map_lt, hsymm, hsymm, comp_lt]
  by_cases hb : b = a₀ <;> by_cases hb' : b' = a₀
  · rw [dif_pos hb, dif_pos hb', hb, hb']
    exact ⟨fun h' => absurd h' (ℓ.irrefl _), fun h' => absurd h' (lt_irrefl _)⟩
  · rw [dif_pos hb, dif_neg hb', hb]
    exact ⟨fun _ => (by decide : (0 : Fin 2) < 1), fun _ => h b' hb'⟩
  · rw [dif_neg hb, dif_pos hb', hb']
    exact ⟨fun h' => absurd (ℓ.trans _ _ _ h' (h b hb)) (ℓ.irrefl _),
      fun h' => absurd h' (by decide : ¬ ((1 : Fin 2) < 0))⟩
  · rw [dif_neg hb, dif_neg hb']
    rfl

lemma toList_split (ℓ : LinOrd A) {a₀ : A} (h : ∀ b, b ≠ a₀ → ℓ.lt a₀ b) :
    ℓ.toList = a₀ :: (ℓ.restrict a₀).toList.map Subtype.val := by
  conv_lhs => rw [ℓ.eq_map_split h]
  rw [toList_map, toList_comp, toList_std,
    show List.finRange 2 = [0, 1] by decide, insList, List.flatMap_cons, List.flatMap_cons,
    List.flatMap_nil, dif_neg (by decide), dif_pos rfl, List.append_nil, List.map_append,
    List.map_map]
  rfl

/-- The least element of an order on a nonempty set. -/
noncomputable def least (ℓ : LinOrd A) (h : 0 < Fintype.card A) : A := ℓ.toRank.symm ⟨0, h⟩

omit [DecidableEq A] in
lemma least_lt (ℓ : LinOrd A) (h : 0 < Fintype.card A) :
    ∀ b, b ≠ ℓ.least h → ℓ.lt (ℓ.least h) b := fun b hb => by
  rw [ℓ.lt_iff_rank_lt, ← toRank_apply, ← toRank_apply, least, Equiv.apply_symm_apply]
  refine Nat.pos_of_ne_zero fun h0 => hb ?_
  apply ℓ.toRank.injective
  rw [least, Equiv.apply_symm_apply]
  exact Fin.ext h0

end LinOrd

/-! ## The associative algebra of an `Ass`-algebra -/

namespace AssAlg

open LinOrd

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
  (α : SymAlgebra R (Ass R) V)

/-- **The action of an order.** -/
noncomputable def oact {A : Type} [Fintype A] [DecidableEq A] (ℓ : LinOrd A) (s : A → V) : V :=
  α.act (Finsupp.single ℓ 1) s

lemma oact_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    (ℓ : LinOrd A) (s : B → V) : oact α (LinOrd.map e ℓ) s = oact α ℓ fun a => s (e a) := by
  rw [oact, oact, ← SymAlgebra.act_map]
  congr 1
  exact (Lin.mapL_single (R := R) (S := fun A _ _ => LinOrd A) e ℓ 1).symm

lemma oact_comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (ℓ : LinOrd A) (ℓ' : LinOrd B) (s : Without A i ⊕ B → V) :
    oact α (LinOrd.comp i ℓ ℓ') s = oact α ℓ (feed i s (oact α ℓ' fun b => s (Sum.inr b))) := by
  rw [oact, oact, oact, ← SymAlgebra.act_comp]
  congr 1
  show Finsupp.single (LinOrd.comp i ℓ ℓ') (1 : R) =
    Lin.compL R (S := fun A _ _ => LinOrd A) i (Finsupp.single ℓ (1 : R))
      (Finsupp.single ℓ' (1 : R))
  rw [Lin.compL_single, mul_one]
  rfl

lemma oact_one (s : Unit → V) : oact α LinOrd.one s = s () :=
  SymAlgebra.act_one α s

lemma oact_unique {A : Type} [Fintype A] [DecidableEq A] (a₀ : A) (h : ∀ a, a = a₀)
    (ℓ : LinOrd A) (s : A → V) : oact α ℓ s = s a₀ := by
  let e : Unit ≃ A := ⟨fun _ => a₀, fun _ => (), fun _ => rfl, fun a => (h a).symm⟩
  haveI : Subsingleton A := ⟨fun a b => (h a).trans (h b).symm⟩
  rw [LinOrd.eq_of_subsingleton ℓ (LinOrd.map e LinOrd.one), oact_map, oact_one]
  rfl

/-- The product of an `Ass`-algebra: the standard order on two inputs. -/
noncomputable def mul (x y : V) : V := oact α (LinOrd.std 2) ![x, y]

/-- The unit of an `Ass`-algebra: the empty order. -/
noncomputable def one : V := oact α (LinOrd.std 0) Fin.elim0

lemma oact_empty {A : Type} [Fintype A] [DecidableEq A] [IsEmpty A] (ℓ : LinOrd A)
    (s : A → V) : oact α ℓ s = one α := by
  let e : Fin 0 ≃ A := Equiv.equivOfIsEmpty _ _
  haveI : Subsingleton A := ⟨fun a => isEmptyElim a⟩
  rw [LinOrd.eq_of_subsingleton ℓ (LinOrd.map e (LinOrd.std 0)), oact_map, one]
  congr 1
  funext k
  exact k.elim0

/-- **An order acts by the right-nested product** of the family in that order. -/
theorem oact_eq_foldr : ∀ (n : ℕ) {A : Type} [Fintype A] [DecidableEq A],
    Fintype.card A = n → ∀ (ℓ : LinOrd A) (s : A → V),
      oact α ℓ s = (ℓ.toList.map s).foldr (mul α) (one α)
  | 0, A, _, _, hA, ℓ, s => by
    haveI : IsEmpty A := Fintype.card_eq_zero_iff.1 hA
    rw [toList_eq_nil, List.map_nil, List.foldr_nil, oact_empty]
  | n + 1, A, _, _, hA, ℓ, s => by
    have hpos : 0 < Fintype.card A := by omega
    have hmin := ℓ.least_lt hpos
    have hcard : Fintype.card (Without A (ℓ.least hpos)) = n := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hA]
      rfl
    rw [ℓ.toList_split hmin, List.map_cons, List.foldr_cons, List.map_map,
      ← oact_eq_foldr n hcard (ℓ.restrict (ℓ.least hpos))]
    conv_lhs => rw [ℓ.eq_map_split hmin]
    rw [oact_map, oact_comp, mul]
    congr 1
    funext k
    fin_cases k
    · rfl
    · rfl

lemma one_mul' (x : V) : mul α (one α) x = x := by
  have h := oact_comp α (B := Fin 0) (0 : Fin 2) (LinOrd.std 2) (LinOrd.std 0) fun _ => x
  have hu : ∀ c : Without (Fin 2) 0 ⊕ Fin 0, c = Sum.inl ⟨1, by decide⟩ := by decide
  rw [oact_unique α _ hu] at h
  refine Eq.trans ?_ h.symm
  rw [mul]
  congr 1
  funext k
  fin_cases k
  · exact (oact_empty α _ _).symm
  · rfl

lemma mul_one' (x : V) : mul α x (one α) = x := by
  have h := oact_comp α (B := Fin 0) (1 : Fin 2) (LinOrd.std 2) (LinOrd.std 0) fun _ => x
  have hu : ∀ c : Without (Fin 2) 1 ⊕ Fin 0, c = Sum.inl ⟨0, by decide⟩ := by decide
  rw [oact_unique α _ hu] at h
  refine Eq.trans ?_ h.symm
  rw [mul]
  congr 1
  funext k
  fin_cases k
  · rfl
  · exact (oact_empty α _ _).symm

lemma mul_assoc' (x y z : V) : mul α (mul α x y) z = mul α x (mul α y z) := by
  set v₀ : Without (Fin 2) 0 ⊕ Fin 2 → V := Sum.elim (fun _ => z) ![x, y] with hv₀
  set v₁ : Without (Fin 2) 1 ⊕ Fin 2 → V := Sum.elim (fun _ => x) ![y, z] with hv₁
  have h₀ := oact_comp α (0 : Fin 2) (LinOrd.std 2) (LinOrd.std 2) v₀
  have h₁ := oact_comp α (1 : Fin 2) (LinOrd.std 2) (LinOrd.std 2) v₁
  rw [oact_eq_foldr α _ rfl, toList_comp, toList_std, show List.finRange 2 = [0, 1] by decide]
    at h₀ h₁
  have e₀ : mul α (mul α x y) z = oact α (LinOrd.std 2) (feed 0 v₀
      (oact α (LinOrd.std 2) fun b => v₀ (Sum.inr b))) := by
    rw [mul, mul]
    congr 1
    funext k
    fin_cases k
    · rfl
    · rfl
  have e₁ : mul α x (mul α y z) = oact α (LinOrd.std 2) (feed 1 v₁
      (oact α (LinOrd.std 2) fun b => v₁ (Sum.inr b))) := by
    rw [mul, mul]
    congr 1
    funext k
    fin_cases k
    · rfl
    · rfl
  rw [e₀, e₁, ← h₀, ← h₁]
  rfl

lemma mul_add' (x y z : V) : mul α x (y + z) = mul α x y + mul α x z := by
  unfold mul oact SymAlgebra.act
  have h := (α.app (Fin 2) (Finsupp.single (LinOrd.std 2) 1)).map_update_add ![x, y] 1 y z
  simp only [show ∀ t : V, Function.update ![x, y] 1 t = ![x, t] from fun t => by
    funext k
    fin_cases k <;> rfl] at h
  exact h

lemma add_mul' (x y z : V) : mul α (x + y) z = mul α x z + mul α y z := by
  unfold mul oact SymAlgebra.act
  have h := (α.app (Fin 2) (Finsupp.single (LinOrd.std 2) 1)).map_update_add ![x, z] 0 x y
  simp only [show ∀ t : V, Function.update ![x, z] 0 t = ![t, z] from fun t => by
    funext k
    fin_cases k <;> rfl] at h
  exact h

lemma mul_smul' (c : R) (x y : V) : mul α x (c • y) = c • mul α x y := by
  unfold mul oact SymAlgebra.act
  have h := (α.app (Fin 2) (Finsupp.single (LinOrd.std 2) 1)).map_update_smul ![x, y] 1 c y
  simp only [show ∀ t : V, Function.update ![x, y] 1 t = ![x, t] from fun t => by
    funext k
    fin_cases k <;> rfl] at h
  exact h

lemma smul_mul' (c : R) (x y : V) : mul α (c • x) y = c • mul α x y := by
  unfold mul oact SymAlgebra.act
  have h := (α.app (Fin 2) (Finsupp.single (LinOrd.std 2) 1)).map_update_smul ![x, y] 0 c x
  simp only [show ∀ t : V, Function.update ![x, y] 0 t = ![t, y] from fun t => by
    funext k
    fin_cases k <;> rfl] at h
  exact h

/-- **The associative ring of an `Ass`-algebra.** -/
noncomputable abbrev toRing : Ring V :=
  { ‹AddCommGroup V› with
    mul := mul α
    one := one α
    mul_assoc := mul_assoc' α
    one_mul := one_mul' α
    mul_one := mul_one' α
    left_distrib := mul_add' α
    right_distrib := add_mul' α
    zero_mul := fun x => by
      show mul α 0 x = 0
      have h := smul_mul' α (0 : R) 0 x
      rwa [zero_smul, zero_smul] at h
    mul_zero := fun x => by
      show mul α x 0 = 0
      have h := mul_smul' α (0 : R) x 0
      rwa [zero_smul, zero_smul] at h }

/-- **The associative algebra of an `Ass`-algebra.** -/
noncomputable abbrev toAlgebra : @Algebra R V _ (toRing α).toSemiring :=
  letI := toRing α
  Algebra.ofModule (fun c x y => smul_mul' α c x y) fun c x y => mul_smul' α c x y

/-- **An order acts as the ordered product.** -/
theorem act_eq {A : Type} [Fintype A] [DecidableEq A] (ℓ : LinOrd A) (s : A → V) :
    letI := toRing α
    α.act (Finsupp.single ℓ 1) s = ℓ.oprod s := by
  letI := toRing α
  rw [LinOrd.oprod, List.prod_eq_foldr]
  exact oact_eq_foldr α _ rfl ℓ s


/-! ## The `Ass`-algebra of an associative algebra -/

section OfAlgebra

variable (A' : Type w) [Ring A'] [Algebra R A']

/-- **The ordered product**, as a multilinear map. -/
noncomputable def ordML {B : Type} [Fintype B] [DecidableEq B] (ℓ : LinOrd B) : EndOp R A' B :=
  (MultilinearMap.mkPiAlgebraFin R (Fintype.card B) A').domDomCongr ℓ.toRank.symm

lemma ordML_apply {B : Type} [Fintype B] [DecidableEq B] (ℓ : LinOrd B) (s : B → A') :
    ordML (R := R) A' ℓ s = ℓ.oprod s := by
  rw [ordML, MultilinearMap.domDomCongr_apply, MultilinearMap.mkPiAlgebraFin_apply,
    LinOrd.oprod, LinOrd.toList, List.map_ofFn]
  rfl

lemma ordML_comp {B C : Type} [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] (i : B)
    (ℓ : LinOrd B) (ℓ' : LinOrd C) :
    ordML (R := R) A' (LinOrd.comp i ℓ ℓ') =
      EndOp.compL R A' i (ordML (R := R) A' ℓ) (ordML (R := R) A' ℓ') :=
  MultilinearMap.ext fun s => by
    show ordML (R := R) A' (LinOrd.comp i ℓ ℓ') s =
      ordML (R := R) A' ℓ (feed i s (ordML (R := R) A' ℓ' fun b => s (Sum.inr b)))
    rw [ordML_apply, ordML_apply, ordML_apply, LinOrd.oprod_comp]

variable (R) in
/-- **The `Ass`-algebra of an associative algebra**: an order acts as the ordered product. -/
noncomputable def ofAlgebra : SymAlgebra R (Ass R) A' where
  app B _ _ := Finsupp.linearCombination R fun ℓ : LinOrd B => ordML (R := R) A' ℓ
  app_map e x := by
    show Finsupp.linearCombination R _ (Lin.mapL R (S := fun A _ _ => LinOrd A) e x) =
      EndOp.mapL R A' e (Finsupp.linearCombination R _ x)
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single ℓ c =>
      rw [Lin.mapL_single, Finsupp.linearCombination_single, Finsupp.linearCombination_single,
        map_smul]
      congr 1
      refine MultilinearMap.ext fun s => ?_
      rw [EndOp.mapL_apply, ordML_apply, ordML_apply]
      exact LinOrd.oprod_map e ℓ s
  app_one := MultilinearMap.ext fun s => by
    show (Finsupp.linearCombination R fun ℓ : LinOrd Unit => ordML (R := R) A' ℓ)
      (Finsupp.single LinOrd.one (1 : R)) s = s ()
    rw [Finsupp.linearCombination_single, one_smul, ordML_apply, LinOrd.oprod_one]
  app_comp i x y := by
    show Finsupp.linearCombination R _ (Lin.compL R (S := fun A _ _ => LinOrd A) i x y) =
      EndOp.compL R A' i (Finsupp.linearCombination R _ x) (Finsupp.linearCombination R _ y)
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | single ℓ c =>
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, hy, hy']
      | single ℓ' c' =>
        rw [Lin.compL_single, Finsupp.linearCombination_single, Finsupp.linearCombination_single,
          Finsupp.linearCombination_single, map_smul, map_smul, LinearMap.smul_apply, smul_smul,
          mul_comm c']
        exact congrArg ((c * c') • ·) (ordML_comp A' i ℓ ℓ')

lemma ofAlgebra_act {B : Type} [Fintype B] [DecidableEq B] (ℓ : LinOrd B) (s : B → A') :
    (ofAlgebra R A').act (Finsupp.single ℓ 1) s = ℓ.oprod s := by
  show (Finsupp.linearCombination R fun ℓ : LinOrd B => ordML (R := R) A' ℓ)
    (Finsupp.single ℓ (1 : R)) s = _
  rw [Finsupp.linearCombination_single, one_smul, ordML_apply]

lemma ofAlgebra_act_smul {B : Type} [Fintype B] [DecidableEq B] (ℓ : LinOrd B) (c : R)
    (s : B → A') : (ofAlgebra R A').act (Finsupp.single ℓ c) s = c • ℓ.oprod s := by
  show (Finsupp.linearCombination R fun ℓ : LinOrd B => ordML (R := R) A' ℓ)
    (Finsupp.single ℓ c) s = _
  rw [Finsupp.linearCombination_single, MultilinearMap.smul_apply, ordML_apply]

lemma mul_ofAlgebra (x y : A') : mul (ofAlgebra R A') x y = x * y := by
  rw [mul, oact, ofAlgebra_act, LinOrd.oprod, LinOrd.toList_std,
    show List.finRange 2 = [0, 1] by decide]
  simp

lemma one_ofAlgebra : one (ofAlgebra R A') = 1 := by
  rw [one, oact, ofAlgebra_act, LinOrd.oprod, LinOrd.toList_std]
  rfl

/-- **The ring of the `Ass`-algebra of a ring is that ring.** -/
theorem ofAlgebra_toRing : toRing (ofAlgebra R A') = ‹Ring A'› := by
  refine Ring.ext rfl ?_
  funext x y
  exact mul_ofAlgebra (R := R) A' x y

end OfAlgebra

/-- **The `Ass`-algebra of the algebra of an `Ass`-algebra is that `Ass`-algebra.** -/
theorem toAlgebra_ofAlgebra :
    letI := toRing α
    letI := toAlgebra α
    ofAlgebra R V = α := by
  letI := toRing α
  letI := toAlgebra α
  refine SymOperadHom.ext fun B _ _ p => ?_
  induction p using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | single ℓ c =>
    refine MultilinearMap.ext fun s => ?_
    rw [show Finsupp.single ℓ c = c • Finsupp.single ℓ (1 : R) by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one], map_smul, map_smul,
      MultilinearMap.smul_apply, MultilinearMap.smul_apply]
    exact congrArg (c • ·) ((ofAlgebra_act V ℓ s).trans (act_eq α ℓ s).symm)

/-! ## Morphisms -/

section Hom

variable {A' : Type w} {B' : Type x} [Ring A'] [Algebra R A'] [Ring B'] [Algebra R B']

lemma map_oprod (f : A' →ₐ[R] B') {C : Type} [Fintype C] (ℓ : LinOrd C) (s : C → A') :
    f (ℓ.oprod s) = ℓ.oprod fun c => f (s c) := by
  rw [LinOrd.oprod, LinOrd.oprod, map_list_prod, List.map_map]
  rfl

/-- **Morphisms of `Ass`-algebras between associative algebras are the algebra morphisms.** -/
noncomputable def homEquiv :
    SymAlgebraHom (ofAlgebra R A') (ofAlgebra R B') ≃ (A' →ₐ[R] B') where
  toFun F :=
    { toFun := F.toLinearMap
      map_one' := by
        rw [← one_ofAlgebra (R := R) A', one, oact, F.map_act, ← one_ofAlgebra (R := R) B']
        exact congrArg _ (funext fun k => k.elim0)
      map_mul' := fun x y => by
        rw [← mul_ofAlgebra (R := R) A', mul, oact, F.map_act, ← mul_ofAlgebra (R := R) B']
        show _ = (ofAlgebra R B').act _ ![_, _]
        congr 1
        funext k
        fin_cases k <;> rfl
      map_zero' := F.toLinearMap.map_zero
      map_add' := F.toLinearMap.map_add
      commutes' := fun c => by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
        show F.toLinearMap (c • 1) = c • 1
        rw [map_smul, ← one_ofAlgebra (R := R) A', one, oact, F.map_act,
          ← one_ofAlgebra (R := R) B']
        congr 2
        funext k
        exact k.elim0 }
  invFun f :=
    { toLinearMap := f.toLinearMap
      map_act := fun p s => by
        induction p using Finsupp.induction_linear with
        | zero =>
          rw [SymAlgebra.act, SymAlgebra.act, map_zero, map_zero, MultilinearMap.zero_apply,
            MultilinearMap.zero_apply, map_zero]
        | add p q hp hq =>
          rw [SymAlgebra.act, SymAlgebra.act, map_add, map_add, MultilinearMap.add_apply,
            MultilinearMap.add_apply, map_add]
          exact congrArg₂ (· + ·) hp hq
        | single ℓ c =>
          rw [ofAlgebra_act_smul, ofAlgebra_act_smul, map_smul]
          exact congrArg (c • ·) (map_oprod f ℓ s) }
  left_inv _ := rfl
  right_inv _ := rfl

end Hom

end AssAlg

end Sym

/-! ## The free `Ass`-algebra -/

namespace Schur

open Sym

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

noncomputable instance instRingAss : Ring (Schur R (Sym.Ass R) V) :=
  AssAlg.toRing (algebra R (Sym.Ass R) V)

noncomputable instance instAlgebraAss : Algebra R (Schur R (Sym.Ass R) V) :=
  AssAlg.toAlgebra (algebra R (Sym.Ass R) V)

/-- In the free `Ass`-algebra, an order acts as the ordered product. -/
lemma act_ass {A : Type} [Fintype A] [DecidableEq A] (ℓ : LinOrd A) (c : R)
    (s : A → Schur R (Sym.Ass R) V) : act (Finsupp.single ℓ c) s = c • ℓ.oprod s := by
  rw [show Finsupp.single ℓ c = c • Finsupp.single ℓ (1 : R) by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one], act_smul]
  exact congrArg (c • ·) (AssAlg.act_eq (algebra R (Sym.Ass R) V) ℓ s)

/-- The `Ass`-algebra morphism of an algebra morphism out of the free `Ass`-algebra. -/
noncomputable def assHom {B : Type w} [Ring B] [Algebra R B]
    (f : Schur R (Sym.Ass R) V →ₐ[R] B) :
    SymAlgebraHom (algebra R (Sym.Ass R) V) (AssAlg.ofAlgebra R B) where
  toLinearMap := f.toLinearMap
  map_act p s := by
    induction p using Finsupp.induction_linear with
    | zero => simp only [SymAlgebra.act, map_zero, MultilinearMap.zero_apply]
    | add p q hp hq =>
      simp only [SymAlgebra.act, map_add, MultilinearMap.add_apply] at hp hq ⊢
      rw [hp, hq]
    | single ℓ c =>
      rw [algebra_act, act_ass, AssAlg.ofAlgebra_act_smul, AlgHom.toLinearMap_apply, map_smul,
        AssAlg.map_oprod]
      rfl

/-- The algebra morphism of an `Ass`-algebra morphism out of the free `Ass`-algebra. -/
noncomputable def algHomOfAss {B : Type w} [Ring B] [Algebra R B]
    (F : SymAlgebraHom (algebra R (Sym.Ass R) V) (AssAlg.ofAlgebra R B)) :
    Schur R (Sym.Ass R) V →ₐ[R] B where
  toFun := F.toLinearMap
  map_one' := by
    show F.toLinearMap (AssAlg.oact (algebra R (Sym.Ass R) V) (LinOrd.std 0) Fin.elim0) = 1
    rw [AssAlg.oact, F.map_act, ← AssAlg.one_ofAlgebra (R := R) B]
    exact congrArg _ (funext fun k => k.elim0)
  map_mul' x y := by
    show F.toLinearMap (AssAlg.oact (algebra R (Sym.Ass R) V) (LinOrd.std 2) ![x, y]) = _
    rw [AssAlg.oact, F.map_act, ← AssAlg.mul_ofAlgebra (R := R) B]
    show (AssAlg.ofAlgebra R B).act _ _ = (AssAlg.ofAlgebra R B).act _ ![_, _]
    congr 1
    funext k
    fin_cases k <;> rfl
  map_zero' := F.toLinearMap.map_zero
  map_add' := F.toLinearMap.map_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    show F.toLinearMap (c • AssAlg.oact (algebra R (Sym.Ass R) V) (LinOrd.std 0) Fin.elim0) = c • 1
    rw [map_smul, AssAlg.oact, F.map_act, ← AssAlg.one_ofAlgebra (R := R) B]
    congr 2
    funext k
    exact k.elim0

/-- The algebra morphism from the free `Ass`-algebra to the tensor algebra. -/
noncomputable def toTensorAlgebra : Schur R (Sym.Ass R) V →ₐ[R] TensorAlgebra R V :=
  algHomOfAss (liftHom (AssAlg.ofAlgebra R (TensorAlgebra R V)) (TensorAlgebra.ι R))

lemma toTensorAlgebra_ι (v : V) : toTensorAlgebra (ι R (Sym.Ass R) V v) = TensorAlgebra.ι R v :=
  liftHom_ι _ _ v

theorem lift_comp_toTensorAlgebra :
    (TensorAlgebra.lift R (ι R (Sym.Ass R) V)).comp toTensorAlgebra = AlgHom.id R _ := by
  have h := algHom_ext (F := assHom ((TensorAlgebra.lift R (ι R (Sym.Ass R) V)).comp
      toTensorAlgebra)) (G := assHom (AlgHom.id R _)) fun v => by
    show TensorAlgebra.lift R (ι R (Sym.Ass R) V) (toTensorAlgebra (ι R (Sym.Ass R) V v)) =
      ι R (Sym.Ass R) V v
    rw [toTensorAlgebra_ι, TensorAlgebra.lift_ι_apply]
  exact AlgHom.ext fun x => congrArg (fun F => F.toLinearMap x) h

theorem toTensorAlgebra_comp_lift :
    toTensorAlgebra.comp (TensorAlgebra.lift R (ι R (Sym.Ass R) V)) = AlgHom.id R _ := by
  refine TensorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
  show toTensorAlgebra (TensorAlgebra.lift R (ι R (Sym.Ass R) V) (TensorAlgebra.ι R v)) =
    TensorAlgebra.ι R v
  rw [TensorAlgebra.lift_ι_apply, toTensorAlgebra_ι]

/-- **The free `Ass`-algebra on `V` is the tensor algebra of `V`.** -/
noncomputable def tensorAlgebraEquiv : TensorAlgebra R V ≃ₐ[R] Schur R (Sym.Ass R) V :=
  AlgEquiv.ofAlgHom (TensorAlgebra.lift R (ι R (Sym.Ass R) V)) toTensorAlgebra
    lift_comp_toTensorAlgebra toTensorAlgebra_comp_lift

lemma tensorAlgebraEquiv_ι (v : V) :
    tensorAlgebraEquiv (TensorAlgebra.ι R v) = ι R (Sym.Ass R) V v :=
  TensorAlgebra.lift_ι_apply _ _

end Schur

end Operad
