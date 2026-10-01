/-
# Regular operads: the symmetrization of a planar set operad

The forgetful functor from symmetric to planar set operads (`SetOperad.toNSSet`) has a left
adjoint, the **symmetrization** `Reg N`: an operation of `Reg N` with inputs `A` is a linear order
on `A` together with an operation of `N` of arity `|A|`. Composition inserts the orders as for the
associative operad and composes in `N` at the rank of the input (`Reg.instSetOperad`). Operads of
this form are the *regular* ones: the associative operad, and those of dialgebras and of
trialgebras.

* `Reg.eta`: the unit, `N → toNSSet (Reg N)`, an operation in the standard order;
* `Reg.lift`: a planar morphism `N → toNSSet S` extends uniquely to a morphism `Reg N → S`, the
  operation placed along the order; **the adjunction**
  `Reg.homEquiv : (Reg N → S) ≃ (N → toNSSet S)`;
* `Reg.hadamardIso`: for a symmetric set operad `S`, the Hadamard product with the linear orders
  is the symmetrization of the underlying planar operad, `LinOrd ×_H S ≅ Reg (toNSSet S)`.

* `Reg.presIso`: **presentations transfer**. The symmetrization of the planar operad presented by
  `T` and `ρ` is the symmetric operad presented by `T`, without symmetries, and the relations `ρ`
  with their inputs in order (`symRel`), whose respecting generator values are those respecting
  `ρ` in the underlying planar operad (`respects_symRel_iff`).

The rank of an input in a composite of linear orders is computed in
`Sym.LinOrd.rank_comp_inl_of_lt`, `rank_comp_inl_of_gt` and `rank_comp_inr`.
-/
import Operad.SetHadamard
import Operad.NSSetArr
import Operad.SetPresentation

universe v w

namespace Operad

open Sym

namespace Sym.LinOrd

variable {A B : Type} [Fintype A] [Fintype B]

open Classical in
lemma rank_eq_sum (x : LinOrd A) (a : A) :
    x.rank a = ∑ b, if x.lt b a then 1 else 0 := by
  unfold rank
  rw [Finset.card_filter]

/-- Relabelling preserves ranks. -/
lemma rank_map (e : A ≃ B) (x : LinOrd A) (b : B) : (map e x).rank b = x.rank (e.symm b) := by
  classical
  rw [rank_eq_sum, rank_eq_sum, ← e.sum_comp]
  simp only [map_lt, Equiv.symm_apply_apply]

variable [DecidableEq A]

lemma rank_comp_inr (i : A) (x : LinOrd A) (y : LinOrd B) (b : B) :
    (comp i x y).rank (Sum.inr b) = x.rank i + y.rank b := by
  classical
  rw [rank_eq_sum, rank_eq_sum, rank_eq_sum, Fintype.sum_sum_type]
  congr 1
  show (∑ a : Without A i, if x.lt a.1 i then 1 else 0) = _
  rw [← Finset.sum_subtype (Finset.univ.filter (· ≠ i)) (by simp)
    (fun a => if x.lt a i then 1 else 0)]
  refine Finset.sum_filter_of_ne fun a _ ha => ?_
  rintro rfl
  exact ha (if_neg (x.irrefl a))

lemma rank_comp_inl_of_lt (i : A) (x : LinOrd A) (y : LinOrd B) (a : Without A i)
    (h : x.lt a.1 i) : (comp i x y).rank (Sum.inl a) = x.rank a.1 := by
  classical
  rw [rank_eq_sum, rank_eq_sum, Fintype.sum_sum_type]
  have h2 : (∑ b : B, if (comp i x y).lt (Sum.inr b) (Sum.inl a) then 1 else 0) = 0 := by
    refine Finset.sum_eq_zero fun b _ => if_neg ?_
    exact fun h' => x.irrefl _ (x.trans _ _ _ h h')
  rw [h2, add_zero]
  show (∑ a' : Without A i, if x.lt a'.1 a.1 then 1 else 0) = _
  rw [← Finset.sum_subtype (Finset.univ.filter (· ≠ i)) (by simp)
    (fun a' => if x.lt a' a.1 then 1 else 0)]
  refine Finset.sum_filter_of_ne fun a' _ ha' => ?_
  rintro rfl
  exact ha' (if_neg fun h' => x.irrefl _ (x.trans _ _ _ h h'))

lemma rank_comp_inl_of_gt (i : A) (x : LinOrd A) (y : LinOrd B) (a : Without A i)
    (h : x.lt i a.1) :
    (comp i x y).rank (Sum.inl a) = x.rank a.1 - 1 + Fintype.card B := by
  classical
  rw [rank_eq_sum, rank_eq_sum, Fintype.sum_sum_type]
  have h2 : (∑ b : B, if (comp i x y).lt (Sum.inr b) (Sum.inl a) then 1 else 0)
      = Fintype.card B := by
    refine (Finset.sum_congr rfl fun b _ =>
      if_pos (show (comp i x y).lt (Sum.inr b) (Sum.inl a) from h)).trans ?_
    simp
  rw [h2]
  have h1 : (∑ a' : Without A i, if (comp i x y).lt (Sum.inl a') (Sum.inl a) then 1 else 0) + 1
      = ∑ a' : A, if x.lt a' a.1 then 1 else 0 := by
    show (∑ a' : Without A i, if x.lt a'.1 a.1 then 1 else 0) + 1 = _
    rw [← Finset.sum_subtype (Finset.univ.filter (· ≠ i)) (by simp)
      (fun a' => if x.lt a' a.1 then 1 else 0), Finset.filter_ne',
      ← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i), if_pos h]
  omega

end Sym.LinOrd

namespace Sym.LinOrd

lemma rank_std (n : ℕ) (k : Fin n) : (std n).rank k = k :=
  rank_ofRank (Equiv.refl (Fin n)) k

lemma rank_one (u : Unit) : LinOrd.one.rank u = 0 := by
  classical
  rw [rank_eq_sum]
  exact Finset.sum_eq_zero fun _ _ => if_neg id

lemma toRank_apply {A : Type} [Fintype A] (x : LinOrd A) (a : A) :
    (x.toRank a : ℕ) = x.rank a := rfl

/-- There is one linear order on at most one point. -/
lemma eq_of_subsingleton {A : Type} [Subsingleton A] (x y : LinOrd A) : x = y :=
  LinOrd.ext fun a b => by
    rw [Subsingleton.elim a b]
    exact ⟨fun h => absurd h (x.irrefl b), fun h => absurd h (y.irrefl b)⟩

end Sym.LinOrd

/-! ## The underlying planar morphism -/

namespace SetOperadHom

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  {T : (A : Type) → [Fintype A] → [DecidableEq A] → Type w} [SetOperad S] [SetOperad T]

/-- **A morphism of symmetric set operads restricts** to the underlying planar operads. -/
def toNSSet (φ : SetOperadHom S T) :
    NSSetOperadHom (SetOperad.toNSSet S) (SetOperad.toNSSet T) where
  app n := φ.app (Fin n)
  app_one := by
    show φ.app _ (SetOperad.map unitFinOne SetOperad.one) = SetOperad.map unitFinOne SetOperad.one
    rw [φ.app_map, φ.app_one]
  app_comp a b n x y := by
    show φ.app _ (SetOperad.map _ (SetOperad.comp _ x y))
      = SetOperad.map _ (SetOperad.comp _ (φ.app _ x) (φ.app _ y))
    rw [φ.app_map, φ.app_comp]

@[simp] lemma toNSSet_app (φ : SetOperadHom S T) (n : ℕ) (x : SetOperad.toNSSet S n) :
    φ.toNSSet.app n x = φ.app (Fin n) x := rfl

end SetOperadHom

/-! ## The symmetrization -/

open NSSetOperad SetOperad

variable (N : ℕ → Type v)

/-- **The symmetrization of a planar set operad**: an operation with inputs `A` is a linear order
on `A` and an operation of `N` of arity `|A|`. -/
def Reg (A : Type) [Fintype A] [DecidableEq A] : Type v :=
  LinOrd A × {X : Arr N // X.1 = Fintype.card A}

namespace Reg

variable {N}
variable {A B C D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

lemma ext {x y : Reg N A} (h1 : x.1 = y.1) (h2 : x.2.1 = y.2.1) : x = y :=
  Prod.ext h1 (Subtype.ext h2)

lemma card_without (i : A) : Fintype.card (Without A i) = Fintype.card A - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

/-- Relabelling: the order is transported, the planar operation is kept. -/
def mapR (e : A ≃ B) (x : Reg N A) : Reg N B :=
  (LinOrd.map e x.1, ⟨x.2.1, x.2.2.trans (Fintype.card_congr e)⟩)

lemma rank_lt (x : Reg N A) (i : A) : x.1.rank i < x.2.1.1 := by
  rw [x.2.2]
  exact x.1.rank_lt_card i

variable [NSSetOperad N]

/-- The identity. -/
def oneR : Reg N Unit := (LinOrd.one, ⟨Arr.one, rfl⟩)

/-- **Composition**: the orders are inserted, the planar operations composed at the rank of the
input. -/
noncomputable def compR (i : A) (x : Reg N A) (y : Reg N B) : Reg N (Without A i ⊕ B) :=
  (LinOrd.comp i x.1 y.1, ⟨Arr.comp x.2.1 (x.1.rank i) y.2.1, by
    have h1 := x.2.2
    have h2 := y.2.2
    have h3 := card_without i
    have h4 := Fintype.card_pos_iff.2 ⟨i⟩
    rw [Arr.comp_fst (rank_lt x i), Fintype.card_sum]
    omega⟩)

lemma compR_fst (i : A) (x : Reg N A) (y : Reg N B) :
    (compR i x y).2.1 = Arr.comp x.2.1 (x.1.rank i) y.2.1 := rfl

/-- **The symmetrization is a symmetric set operad.** -/
noncomputable instance instSetOperad : SetOperad (Reg N) where
  map e x := mapR e x
  map_refl x := ext (SetOperad.map_refl (S := fun A _ _ => LinOrd A) x.1) rfl
  map_trans e f x := ext (SetOperad.map_trans (S := fun A _ _ => LinOrd A) e f x.1) rfl
  one := oneR
  comp i x y := compR i x y
  map_comp σ τ i x y := by
    refine ext (SetOperad.map_comp (S := fun A _ _ => LinOrd A) σ τ i x.1 y.1) ?_
    show Arr.comp x.2.1 (x.1.rank i) y.2.1 = Arr.comp x.2.1 ((LinOrd.map σ x.1).rank (σ i)) y.2.1
    rw [LinOrd.rank_map, Equiv.symm_apply_apply]
  comp_one i x := ext (SetOperad.comp_one (S := fun A _ _ => LinOrd A) i x.1)
    (Arr.comp_one (rank_lt x i))
  one_comp y := by
    refine ext (SetOperad.one_comp (S := fun A _ _ => LinOrd A) y.1) ?_
    show Arr.comp Arr.one (LinOrd.one.rank ()) y.2.1 = y.2.1
    rw [LinOrd.rank_one, Arr.one_comp]
  comp_assoc_seq i j x y z := by
    refine ext (SetOperad.comp_assoc_seq (S := fun A _ _ => LinOrd A) i j x.1 y.1 z.1) ?_
    show Arr.comp (Arr.comp x.2.1 (x.1.rank i) y.2.1) ((LinOrd.comp i x.1 y.1).rank (Sum.inr j))
        z.2.1 = Arr.comp x.2.1 (x.1.rank i) (Arr.comp y.2.1 (y.1.rank j) z.2.1)
    rw [LinOrd.rank_comp_inr, Arr.comp_comp_nested _ (rank_lt x i) (rank_lt y j)]
  comp_assoc_par {A B D} _ _ _ _ _ _ i k hik x y z := by
    refine ext (SetOperad.comp_assoc_par (S := fun A _ _ => LinOrd A) hik x.1 y.1 z.1) ?_
    show Arr.comp (Arr.comp x.2.1 (x.1.rank i) y.2.1)
        ((LinOrd.comp i x.1 y.1).rank (Sum.inl ⟨k, Ne.symm hik⟩)) z.2.1
      = Arr.comp (Arr.comp x.2.1 (x.1.rank k) z.2.1)
        ((LinOrd.comp k x.1 z.1).rank (Sum.inl ⟨i, hik⟩)) y.2.1
    rcases x.1.total i k hik with h | h
    · rw [LinOrd.rank_comp_inl_of_gt _ _ _ _ h, LinOrd.rank_comp_inl_of_lt _ _ _ _ h]
      have hr := x.1.rank_lt_rank h
      have hy := y.2.2
      rw [show x.1.rank k - 1 + Fintype.card B = x.1.rank k + y.2.1.1 - 1 by omega]
      exact Arr.comp_comp_disjoint _ _ hr (rank_lt x k)
    · rw [LinOrd.rank_comp_inl_of_lt _ _ _ _ h, LinOrd.rank_comp_inl_of_gt _ _ _ _ h]
      have hr := x.1.rank_lt_rank h
      have hz := z.2.2
      rw [show x.1.rank i - 1 + Fintype.card D = x.1.rank i + z.2.1.1 - 1 by omega]
      exact (Arr.comp_comp_disjoint _ _ hr (rank_lt x i)).symm

@[simp] lemma map_def (e : A ≃ B) (x : Reg N A) : SetOperad.map e x = mapR e x := rfl

@[simp] lemma comp_def (i : A) (x : Reg N A) (y : Reg N B) :
    SetOperad.comp i x y = compR i x y := rfl

@[simp] lemma one_def : (SetOperad.one : Reg N Unit) = oneR := rfl

/-! ## The unit -/

/-- An operation of `N`, in the standard order. -/
def std {n : ℕ} (x : N n) : Reg N (Fin n) := (LinOrd.std n, ⟨⟨n, x⟩, (Fintype.card_fin n).symm⟩)

/-- **The unit of the adjunction**, an operation of `N` in the standard order. -/
noncomputable def eta : NSSetOperadHom N (toNSSet (Reg N)) where
  app n x := std x
  app_one := ext (LinOrd.eq_of_subsingleton _ _) rfl
  app_comp a b n x y := by
    refine ext (LinOrd.map_insertEquiv_comp_std a b n).symm ?_
    show (⟨a + n + b, NSSetOperad.comp a b x y⟩ : Arr N)
      = Arr.comp ⟨a + 1 + b, x⟩ ((LinOrd.std (a + 1 + b)).rank ⟨a, by omega⟩) ⟨n, y⟩
    rw [LinOrd.rank_std, Arr.mk_comp]

lemma eta_app {n : ℕ} (x : N n) : (eta (N := N)).app n x = std x := rfl

omit [NSSetOperad N] in
/-- **Every operation is a relabelling of one in the standard order.** -/
lemma eq_map_std (x : Reg N A) :
    x = mapR ((finCongr x.2.2).trans x.1.toRank.symm) (std x.2.1.2) := by
  refine ext ?_ rfl
  refine LinOrd.ext fun a b => ?_
  simp only [mapR, std, LinOrd.map_lt, LinOrd.std_lt, Equiv.symm_trans_apply, Equiv.symm_symm,
    Fin.lt_def, finCongr_symm_apply_coe]
  rw [LinOrd.toRank_apply, LinOrd.toRank_apply]
  exact x.1.lt_iff_rank_lt a b

/-! ## The extension of a planar morphism -/

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type w} [SetOperad S]

/-- An operation of `S` with inputs `Fin n`, placed along a linear order. -/
noncomputable def place (L : LinOrd A) (X : Arr (toNSSet S)) (h : X.1 = Fintype.card A) : S A :=
  SetOperad.map ((finCongr h).trans L.toRank.symm) X.2

lemma place_map (e : A ≃ B) (L : LinOrd A) (X : Arr (toNSSet S)) (h : X.1 = Fintype.card A)
    (h' : X.1 = Fintype.card B) :
    place (LinOrd.map e L) X h' = SetOperad.map e (place L X h) := by
  unfold place
  rw [← SetOperad.map_trans]
  congr 1
  refine Equiv.ext fun k => ?_
  apply (LinOrd.map e L).toRank.injective
  rw [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.trans_apply, Equiv.trans_apply]
  refine Fin.ext ?_
  rw [LinOrd.toRank_apply, LinOrd.rank_map, Equiv.symm_apply_apply, ← LinOrd.toRank_apply,
    Equiv.apply_symm_apply]
  simp

lemma place_congr {L : LinOrd A} {X X' : Arr (toNSSet S)} (e : X = X')
    (h : X.1 = Fintype.card A) : place L X h = place L X' (e ▸ h) := by
  subst e
  rfl

omit [DecidableEq A] in
lemma rank_toRank_symm (L : LinOrd A) (k : Fin (Fintype.card A)) :
    L.rank (L.toRank.symm k) = k := by
  rw [← LinOrd.toRank_apply, Equiv.apply_symm_apply]

/-- **Placing a planar composite along a composite order** is the composite of the placed
operations. -/
lemma place_comp (i : A) (L : LinOrd A) (M : LinOrd B) (X Y : Arr (toNSSet S))
    (hX : X.1 = Fintype.card A) (hY : Y.1 = Fintype.card B) (h) :
    place (LinOrd.comp i L M) (Arr.comp X (L.rank i) Y) h
      = SetOperad.comp i (place L X hX) (place M Y hY) := by
  obtain ⟨m, y⟩ := Y
  have hrlt := L.rank_lt_card i
  generalize hrdef : L.rank i = r at h ⊢
  obtain ⟨c, x, rfl⟩ := Arr.exists_mk X (show r < X.1 by omega)
  simp only at hX hY
  clear hrlt
  have hi : ((finCongr hX).trans L.toRank.symm)
      ⟨r, Nat.lt_of_lt_of_le (Nat.lt_succ_self r) (Nat.le_add_right _ _)⟩ = i := by
    apply L.toRank.injective
    refine Fin.ext ?_
    rw [Equiv.trans_apply, Equiv.apply_symm_apply, LinOrd.toRank_apply, hrdef]
    rfl
  subst hi
  rw [place_congr (Arr.mk_comp r c x y)]
  unfold place
  simp only [SetOperad.toNSSet_comp, SetOperad.nsCompSet]
  rw [← SetOperad.map_trans, ← SetOperad.map_comp]
  congr 1
  refine Equiv.ext fun u => ?_
  change (LinOrd.comp _ L M).toRank.symm (finCongr _ (insertEquiv r c m u)) = _
  rw [Equiv.symm_apply_eq]
  refine Fin.ext ?_
  rw [LinOrd.toRank_apply, finCongr_apply, Fin.val_cast]
  symm
  rcases u with k | j
  · have hk : (k.1 : ℕ) ≠ r := fun e => k.2 (Fin.ext e)
    have hrk : L.rank ((finCongr hX).trans L.toRank.symm k.1) = k.1 := by
      rw [Equiv.trans_apply, rank_toRank_symm]
      rfl
    have hrr : L.rank ((finCongr hX).trans L.toRank.symm ⟨r, by omega⟩) = r := by
      rw [Equiv.trans_apply, rank_toRank_symm]
      rfl
    rw [compEquiv_inl, insertEquiv_inl_val]
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · rw [LinOrd.rank_comp_inl_of_lt _ _ _ _ (by rw [L.lt_iff_rank_lt, hrk, hrr]; exact hlt),
        hrk, if_pos hlt]
    · rw [LinOrd.rank_comp_inl_of_gt _ _ _ _ (by rw [L.lt_iff_rank_lt, hrk, hrr]; exact hgt),
        hrk, if_neg (by omega), ← hY]
      omega
  · rw [compEquiv_inr, LinOrd.rank_comp_inr, insertEquiv_inr_val, Equiv.trans_apply,
      rank_toRank_symm, Equiv.trans_apply, rank_toRank_symm]
    rfl

/-- **The extension of a planar morphism** into the underlying planar operad of `S`: the image of
the planar operation, placed along the order. -/
noncomputable def lift (F : NSSetOperadHom N (toNSSet S)) : SetOperadHom (Reg N) S where
  app A _ _ x := place x.1 (Arr.map F x.2.1) x.2.2
  app_map e x := place_map e x.1 _ _ _
  app_one := by
    show place LinOrd.one (Arr.map F Arr.one) _ = SetOperad.one
    rw [place_congr (Arr.map_one F)]
    show SetOperad.map _ (SetOperad.map unitFinOne SetOperad.one) = _
    rw [← SetOperad.map_trans]
    convert SetOperad.map_refl (S := S) SetOperad.one
  app_comp i x y := by
    show place (LinOrd.comp i x.1 y.1) (Arr.map F (Arr.comp x.2.1 (x.1.rank i) y.2.1)) _ = _
    rw [place_congr (Arr.map_comp F _ _ _)]
    exact place_comp i x.1 y.1 _ _ x.2.2 y.2.2 _

lemma lift_app (F : NSSetOperadHom N (toNSSet S)) (x : Reg N A) :
    (lift F).app A x = place x.1 (Arr.map F x.2.1) x.2.2 := rfl

/-- **The extension restricts to the planar morphism** on operations in the standard order. -/
theorem lift_std (F : NSSetOperadHom N (toNSSet S)) {n : ℕ} (x : N n) :
    (lift F).app (Fin n) (std x) = F.app n x := by
  show SetOperad.map _ (F.app n x) = F.app n x
  convert SetOperad.map_refl (S := S) (F.app n x)
  refine Equiv.ext fun k => ?_
  change (LinOrd.std n).toRank.symm (finCongr _ k) = k
  rw [Equiv.symm_apply_eq]
  exact Fin.ext (by rw [LinOrd.toRank_apply, LinOrd.rank_std]; rfl)

/-- **Morphisms out of the symmetrization are determined on operations in the standard
order.** -/
theorem hom_ext {G G' : SetOperadHom (Reg N) S}
    (h : ∀ (n : ℕ) (x : N n), G.app (Fin n) (std x) = G'.app (Fin n) (std x)) : G = G' := by
  ext A _ _ x
  rw [eq_map_std x, ← map_def, G.app_map, G'.app_map, h]

/-- **The symmetrization is left adjoint to the underlying planar operad**: a morphism out of
`Reg N` is a planar morphism out of `N`. -/
noncomputable def homEquiv : SetOperadHom (Reg N) S ≃ NSSetOperadHom N (toNSSet S) where
  toFun G := G.toNSSet.comp eta
  invFun F := lift F
  left_inv _ := hom_ext fun _ x => lift_std _ x
  right_inv F := NSSetOperadHom.ext fun _ x => lift_std F x

@[simp] lemma homEquiv_apply (G : SetOperadHom (Reg N) S) {n : ℕ} (x : N n) :
    (homEquiv G).app n x = G.app (Fin n) (std x) := rfl

@[simp] lemma homEquiv_symm_apply (F : NSSetOperadHom N (toNSSet S)) :
    homEquiv.symm F = lift F := rfl

/-! ## The Hadamard product with the linear orders -/

/-- The order of an operation. -/
def toLinOrd : SetOperadHom (Reg N) (fun A _ _ => LinOrd A) where
  app _ _ _ x := x.1
  app_map _ _ := rfl
  app_one := rfl
  app_comp _ _ _ := rfl

/-- **The counit**: an operation of the underlying planar operad, placed along the order. -/
noncomputable def counit : SetOperadHom (Reg (toNSSet S)) S := lift NSSetOperadHom.id

/-- The comparison with the Hadamard product. -/
noncomputable def toHadamard :
    SetOperadHom (Reg (toNSSet S)) (Hadamard (fun A _ _ => LinOrd A) S) :=
  Hadamard.lift toLinOrd counit

lemma toHadamard_bijective (A : Type) [Fintype A] [DecidableEq A] :
    Function.Bijective (toHadamard (S := S) |>.app A) := by
  constructor
  · rintro ⟨L, ⟨k, x⟩, hx⟩ ⟨L', ⟨k', x'⟩, hx'⟩ h
    simp only at hx hx'
    subst hx
    subst hx'
    obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h
    change L = L' at h1
    subst h1
    have hxx : x = x' := SetOperad.map_injective _ h2
    subst hxx
    rfl
  · rintro ⟨L, s⟩
    refine ⟨(L, ⟨⟨Fintype.card A, SetOperad.map L.toRank s⟩, rfl⟩), Prod.ext rfl ?_⟩
    show SetOperad.map _ (SetOperad.map L.toRank s) = s
    rw [← SetOperad.map_trans]
    convert SetOperad.map_refl (S := S) s
    exact Equiv.ext fun a => by simp

end Reg

/-- A morphism of set operads with bijective components is an isomorphism. -/
noncomputable def SetOperadIso.ofBijective
    {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
    {T : (A : Type) → [Fintype A] → [DecidableEq A] → Type w} [SetOperad S] [SetOperad T]
    (φ : SetOperadHom S T)
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A], Function.Bijective (φ.app A)) :
    SetOperadIso S T where
  hom := φ
  inv :=
    { app := fun A _ _ => (Equiv.ofBijective _ (h A)).symm
      app_map := fun e y => by
        apply (h _).1
        rw [Equiv.ofBijective_apply_symm_apply (φ.app _) (h _), φ.app_map,
          Equiv.ofBijective_apply_symm_apply (φ.app _) (h _)]
      app_one := by
        apply (h _).1
        rw [Equiv.ofBijective_apply_symm_apply (φ.app _) (h _), φ.app_one]
      app_comp := fun i x y => by
        apply (h _).1
        rw [Equiv.ofBijective_apply_symm_apply (φ.app _) (h _), φ.app_comp,
          Equiv.ofBijective_apply_symm_apply (φ.app _) (h _),
          Equiv.ofBijective_apply_symm_apply (φ.app _) (h _)] }
  hom_inv_id := SetOperadHom.ext fun A _ _ x => Equiv.ofBijective_symm_apply_apply _ (h A) x
  inv_hom_id := SetOperadHom.ext fun A _ _ y => Equiv.ofBijective_apply_symm_apply _ (h A) y

namespace Reg

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type w} [SetOperad S]

/-- **The Hadamard product with the linear orders is the symmetrization of the underlying planar
operad**: `LinOrd ×_H S ≅ Reg (toNSSet S)`. -/
noncomputable def hadamardIso :
    SetOperadIso (Reg (toNSSet S)) (Hadamard (fun A _ _ => LinOrd A) S) :=
  SetOperadIso.ofBijective toHadamard toHadamard_bijective

end Reg

/-! ## Isomorphisms -/

namespace SetOperadIso

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  {T : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  {U : (A : Type) → [Fintype A] → [DecidableEq A] → Type*} [SetOperad S] [SetOperad T]
  [SetOperad U]

/-- The inverse isomorphism. -/
def symm (φ : SetOperadIso S T) : SetOperadIso T S := ⟨φ.inv, φ.hom, φ.inv_hom_id, φ.hom_inv_id⟩

/-- The composite of two isomorphisms. -/
def trans (φ : SetOperadIso S T) (ψ : SetOperadIso T U) : SetOperadIso S U where
  hom := ψ.hom.comp φ.hom
  inv := φ.inv.comp ψ.inv
  hom_inv_id := SetOperadHom.ext fun A _ _ x => by
    show φ.inv.app A (ψ.inv.app A (ψ.hom.app A (φ.hom.app A x))) = x
    rw [show ψ.inv.app A (ψ.hom.app A (φ.hom.app A x)) = φ.hom.app A x from
      congrArg (fun χ : SetOperadHom T T => χ.app A (φ.hom.app A x)) ψ.hom_inv_id]
    exact congrArg (fun χ : SetOperadHom S S => χ.app A x) φ.hom_inv_id
  inv_hom_id := SetOperadHom.ext fun A _ _ x => by
    show ψ.hom.app A (φ.hom.app A (φ.inv.app A (ψ.inv.app A x))) = x
    rw [show φ.hom.app A (φ.inv.app A (ψ.inv.app A x)) = ψ.inv.app A x from
      congrArg (fun χ : SetOperadHom T T => χ.app A (ψ.inv.app A x)) φ.inv_hom_id]
    exact congrArg (fun χ : SetOperadHom U U => χ.app A x) ψ.inv_hom_id

/-- **Precomposition with an isomorphism**: morphisms out of `T` are morphisms out of `S`. -/
def precompEquiv (φ : SetOperadIso S T) : SetOperadHom T U ≃ SetOperadHom S U where
  toFun ψ := ψ.comp φ.hom
  invFun χ := χ.comp φ.inv
  left_inv ψ := SetOperadHom.ext fun A _ _ x => by
    show ψ.app A (φ.hom.app A (φ.inv.app A x)) = ψ.app A x
    rw [show φ.hom.app A (φ.inv.app A x) = x from
      congrArg (fun χ : SetOperadHom T T => χ.app A x) φ.inv_hom_id]
  right_inv χ := SetOperadHom.ext fun A _ _ x => by
    show χ.app A (φ.inv.app A (φ.hom.app A x)) = χ.app A x
    rw [show φ.inv.app A (φ.hom.app A x) = x from
      congrArg (fun χ : SetOperadHom S S => χ.app A x) φ.hom_inv_id]

@[simp] lemma precompEquiv_apply (φ : SetOperadIso S T) (ψ : SetOperadHom T U) :
    φ.precompEquiv ψ = ψ.comp φ.hom := rfl

end SetOperadIso

/-! ## Functoriality -/

namespace Reg

variable {N} [NSSetOperad N] {N' : ℕ → Type w} [NSSetOperad N']

/-- **The symmetrization of a planar morphism.** -/
noncomputable def mapHom (φ : NSSetOperadHom N N') : SetOperadHom (Reg N) (Reg N') :=
  lift ((eta (N := N')).comp φ)

@[simp] lemma mapHom_std (φ : NSSetOperadHom N N') {n : ℕ} (x : N n) :
    (mapHom φ).app (Fin n) (std x) = std (φ.app n x) :=
  lift_std _ x

/-- **The symmetrization of a planar isomorphism.** -/
noncomputable def mapIso (φ : NSSetOperadIso N N') : SetOperadIso (Reg N) (Reg N') where
  hom := mapHom φ.hom
  inv := mapHom φ.inv
  hom_inv_id := hom_ext fun n x => by
    show (mapHom φ.inv).app _ ((mapHom φ.hom).app _ (std x)) = std x
    rw [mapHom_std, mapHom_std]
    exact congrArg std (congrArg (fun χ : NSSetOperadHom N N => χ.app n x) φ.hom_inv_id)
  inv_hom_id := hom_ext fun n x => by
    show (mapHom φ.hom).app _ ((mapHom φ.inv).app _ (std x)) = std x
    rw [mapHom_std, mapHom_std]
    exact congrArg std (congrArg (fun χ : NSSetOperadHom N' N' => χ.app n x) φ.inv_hom_id)

end Reg

/-! ## Presentations -/

namespace NSSyn

variable {T : ℕ → Type w}

/-- **A planar expression as a symmetric one**, its inputs in their planar order. -/
def toSyn : {n : ℕ} → NSSyn T n → Syn T (Fin n)
  | _, .one => Syn.map unitFinOne Syn.one
  | _, .gen g => Syn.gen g
  | _, .comp a b x y => Syn.map (insertEquiv a b _) (Syn.comp ⟨a, by omega⟩ (toSyn x) (toSyn y))

/-- **Evaluating the symmetric expression is evaluating the planar one** in the underlying planar
operad. -/
lemma eval_toSyn {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
    (f : ∀ n, T n → S (Fin n)) : ∀ {n : ℕ} (p : NSSyn T n),
    Syn.eval f p.toSyn = NSSyn.eval (S := toNSSet S) f p
  | _, .one => rfl
  | _, .gen _ => rfl
  | _, .comp a b x y => by
    simp only [toSyn, Syn.eval_map, Syn.eval_comp, eval_toSyn f x, eval_toSyn f y]
    rfl

end NSSyn

variable {T : ℕ → Type w}

/-- **The symmetric relations of a planar presentation**: the planar relations, with their inputs
in the planar order, relabelled along any bijection. -/
def symRel (ρ : ∀ n : ℕ, NSSyn T n → NSSyn T n → Prop) :
    ∀ {A : Type} [Fintype A] [DecidableEq A], Syn T A → Syn T A → Prop :=
  fun {A} _ _ x y => ∃ (n : ℕ) (p q : NSSyn T n) (e : Fin n ≃ A),
    ρ n p q ∧ x = Syn.map e p.toSyn ∧ y = Syn.map e q.toSyn

/-- **Generator values respect the symmetric relations exactly when they respect the planar
ones** in the underlying planar operad. -/
lemma respects_symRel_iff {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
    [SetOperad S] (ρ : ∀ n : ℕ, NSSyn T n → NSSyn T n → Prop) (f : ∀ n, T n → S (Fin n)) :
    Pres.Respects (symRel ρ) f ↔ NSPres.Respects (S := toNSSet S) ρ f := by
  constructor
  · intro h n p q hpq
    have := h _ _ ⟨n, p, q, Equiv.refl _, hpq, rfl, rfl⟩
    rwa [Syn.eval_map, Syn.eval_map, SetOperad.map_refl, SetOperad.map_refl, NSSyn.eval_toSyn,
      NSSyn.eval_toSyn] at this
  · rintro h A _ _ x y ⟨n, p, q, e, hpq, rfl, rfl⟩
    rw [Syn.eval_map, Syn.eval_map, NSSyn.eval_toSyn, NSSyn.eval_toSyn, h p q hpq]

namespace Reg

variable {ρ : ∀ n : ℕ, NSSyn T n → NSSyn T n → Prop}

lemma respects_gen :
    NSPres.Respects (S := toNSSet (Pres T (symRel ρ))) ρ (fun _ g => Pres.gen g) :=
  (respects_symRel_iff ρ _).1 (Pres.respects_app SetOperadHom.id)

/-- The comparison morphism, out of the symmetric presentation. -/
noncomputable def presHom : SetOperadHom (Pres T (symRel ρ)) (Reg (NSPres T ρ)) :=
  Pres.lift (fun _ g => std (NSPres.gen g))
    ((respects_symRel_iff ρ _).2 (NSPres.respects_app (eta (N := NSPres T ρ))))

/-- The inverse comparison, extended from the planar presentation. -/
noncomputable def presInv : SetOperadHom (Reg (NSPres T ρ)) (Pres T (symRel ρ)) :=
  lift (NSPres.lift (fun _ g => Pres.gen g) respects_gen)

/-- **The symmetrization of a planar presentation is presented by the same generators and
relations**: the generators without symmetries, and the relations with their inputs in order and
all their relabellings. -/
noncomputable def presIso : SetOperadIso (Pres T (symRel ρ)) (Reg (NSPres T ρ)) where
  hom := presHom
  inv := presInv
  hom_inv_id := Pres.hom_ext fun _ g => by
    show presInv.app _ (std (NSPres.gen g)) = Pres.gen g
    rw [presInv, lift_std]
    rfl
  inv_hom_id := hom_ext fun n x => by
    show presHom.app _ (presInv.app _ (std x)) = std x
    rw [presInv, lift_std]
    have h := NSPres.hom_ext (φ := (presHom (ρ := ρ)).toNSSet.comp
      (NSPres.lift (fun _ g => Pres.gen g) respects_gen)) (ψ := eta) fun _ _ => rfl
    exact congrArg (fun χ : NSSetOperadHom (NSPres T ρ) _ => χ.app n x) h

end Reg

end Operad
