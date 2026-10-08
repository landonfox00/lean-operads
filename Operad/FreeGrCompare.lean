/-
# Comparison of free graded operads with differentials raising the number of vertices

Let `V` and `W` be reduced graded linear species with odd differentials `d`, and consider on the
free graded operad `T(V)` a differential `D = -δ + D₁`, `δ` the derivation extending `d` and `D₁`
an odd derivation raising the number of vertices by one, as for cobar constructions. A morphism
`f : V → W` commuting with the differentials, whose extension `F = T(f)` commutes with `D₁`,
induces a morphism of the filtrations of `T(V)` and `T(W)` by the number of vertices, finite in
each arity, with associated graded `(T(V), -δ)`.

Over a field of characteristic zero, splittings `p, h` of the differentials of the generators
make `T(p)` a retraction of `(T(V), δ)` onto `T(im p)` with acyclic kernel (`Splitting.retract`).
When `p' f p` is inverted by `k` on the arities at most `m` (`exists_compat`), `T(k)` inverts
`T(p' f p)` on the trees with vertices of at most `m` inputs, so:

* **`F` is a quasi-isomorphism in arity `A` as soon as `f` is one in the arities at most `|A|`**
  (`FreeGrL.qiso_of_le`), and **`F` is a quasi-isomorphism when `f` is**
  (`FreeGrL.qiso_of_qiso`);
* **`f` is a quasi-isomorphism when `F` is** (`FreeGrL.qiso_of_qiso_free`), by induction on the
  arity: the trees with at least two vertices in arity `m + 1` only involve the generators of at
  most `m` inputs, so `F` is a quasi-isomorphism on them, hence on the trees with one vertex, the
  generators (`FreeGrL.eq_ι_genCoef`, `FreeGrL.ι_injective`).
-/
import Operad.FreeGrGenCoef
import Operad.SpSplitting
import Mathlib.Algebra.Algebra.Rat

universe u v w

namespace Operad

open Sym GerBV

section General

variable {R : Type u} [CommRing R]
  {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)] [GrSpecies R W]

namespace FreeGrL

variable (R V) in
/-- The trees with `k` vertices: the eigenspace of the vertex count for `k`. -/
noncomputable abbrev vx (k : ℕ) (A : Type) [Fintype A] [DecidableEq A] :
    Submodule R (FreeGrL R V A) :=
  eig R V (GrSpEnd.id R V) k A

variable (R V) in
/-- The trees with at least `p` vertices. -/
noncomputable abbrev vxGe (p : ℕ) (A : Type) [Fintype A] [DecidableEq A] :
    Submodule R (FreeGrL R V A) :=
  ⨆ k : {k : ℕ // p ≤ k}, vx R V k.1 A

/-- The differential `-δ + D₁`. -/
noncomputable def totD (d : GrSpEnd R V true) (D₁ : GrDer (GrOperadHom.id R (FreeGrL R V)) true)
    (A : Type) [Fintype A] [DecidableEq A] : FreeGrL R V A →ₗ[R] FreeGrL R V A :=
  -(derSp d).app A + D₁.app A

/-- **The data of a comparison**: reduced species, differentials `-δ + D₁` squaring to zero with
`D₁` raising the number of vertices by one, and a morphism of the generators commuting with
the differentials whose extension commutes with `D₁`. -/
structure CompareData (dV : GrSpEnd R V true) (dW : GrSpEnd R W true)
    (D₁ : GrDer (GrOperadHom.id R (FreeGrL R V)) true)
    (D₁' : GrDer (GrOperadHom.id R (FreeGrL R W)) true) (f : GrSpeciesHom R V W) : Prop where
  redV : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ v : V B, v = 0
  redW : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ v : W B, v = 0
  ddV : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : V A), dV.app A (dV.app A x) = 0
  ddW : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : W A), dW.app A (dW.app A x) = 0
  dd : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : FreeGrL R V A),
    totD dV D₁ A (totD dV D₁ A x) = 0
  dd' : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : FreeGrL R W A),
    totD dW D₁' A (totD dW D₁' A x) = 0
  raise : ∀ (A : Type) [Fintype A] [DecidableEq A] (k : ℕ) (x : FreeGrL R V A),
    x ∈ vx R V k A → D₁.app A x ∈ vx R V (k + 1) A
  raise' : ∀ (A : Type) [Fintype A] [DecidableEq A] (k : ℕ) (x : FreeGrL R W A),
    x ∈ vx R W k A → D₁'.app A x ∈ vx R W (k + 1) A
  comm : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : V A),
    dW.app A (f.app A x) = f.app A (dV.app A x)
  commD : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : FreeGrL R V A),
    D₁'.app A ((mapSp f).app A x) = (mapSp f).app A (D₁.app A x)

/-! ## The filtration by the number of vertices -/

section Filtration

variable {X : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (X A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (X A)] [GrSpecies R X]
  {Y : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Y A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Y A)] [GrSpecies R Y]
  {A : Type} [Fintype A] [DecidableEq A]

/-- The derivation extending an odd endomorphism preserves the number of vertices. -/
lemma derSp_mem_vx {d : GrSpEnd R X true} {k : ℕ} {x : FreeGrL R X A} (hx : x ∈ vx R X k A) :
    (derSp d).app A x ∈ vx R X k A := by
  refine mem_eig.2 ?_
  rw [derSp_comm (a := GrSpEnd.id R X) (b := d) (fun A _ _ v => by
    rw [GrSpEnd.id_app, GrSpEnd.id_app, Bool.false_and, σ_false, one_smul]), Bool.false_and,
    σ_false, one_smul, mem_eig.1 hx, map_smul]

lemma vx_disjoint [Algebra ℚ R] (p : ℕ) : Disjoint (vx R X p A) (vxGe R X (p + 1) A) :=
  (iSupIndep_eigenspace_nat _ p).mono_right
    (iSup_le fun k => le_iSup₂_of_le (f := fun (j : ℕ) (_ : j ≠ p) => vx R X j A) k.1
      (by have := k.2; omega) le_rfl)

lemma vxGe_eq (p : ℕ) : vxGe R X p A = vx R X p A ⊔ vxGe R X (p + 1) A := by
  refine le_antisymm (iSup_le fun k => ?_) (sup_le (le_iSup (fun k : {k : ℕ // p ≤ k} =>
    vx R X k.1 A) ⟨p, le_rfl⟩) (iSup_le fun k => le_iSup (fun k : {k : ℕ // p ≤ k} =>
    vx R X k.1 A) ⟨k.1, by have := k.2; omega⟩))
  rcases eq_or_lt_of_le k.2 with h | h
  · rw [← h]
    exact le_sup_left
  · exact le_sup_of_le_right (le_iSup (fun k : {k : ℕ // p + 1 ≤ k} => vx R X k.1 A) ⟨k.1, h⟩)

lemma vxGe_zero [Algebra ℚ R] : vxGe R X 0 A = ⊤ := by
  refine eq_top_iff.2 ((iSup_eig_eq_top (a := GrSpEnd.id R X) (fun A _ _ v =>
    Submodule.mem_iSup_of_mem 1 (by
      rw [Module.End.mem_eigenspace_iff, Nat.cast_one, one_smul]
      rfl)) A).symm.le.trans (iSup_le fun k => ?_))
  exact le_iSup (fun k : {k : ℕ // 0 ≤ k} => vx R X k.1 A) ⟨k, Nat.zero_le k⟩

lemma vxGe_card [Algebra ℚ R]
    (hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ v : X B, v = 0) :
    vxGe R X (Fintype.card A) A = ⊥ :=
  eq_bot_iff.2 (iSup_le fun k _ hx => (Submodule.mem_bot R).2 (eig_card_eq_bot hred k.2 hx))

lemma mem_vxGe {p k : ℕ} (h : p ≤ k) {x : FreeGrL R X A} (hx : x ∈ vx R X k A) :
    x ∈ vxGe R X p A :=
  Submodule.mem_iSup_of_mem (⟨k, h⟩ : {k : ℕ // p ≤ k}) hx

lemma ι_mem_vx (v : X A) : (ι R X).app A v ∈ vx R X 1 A :=
  mem_eig.2 (by
    rw [derSp_ι, Nat.cast_one, one_smul]
    rfl)

/-- Morphisms extending morphisms of the generators preserve the number of vertices. -/
lemma mapSp_mem_vx {φ : GrSpeciesHom R X Y} {k : ℕ} {x : FreeGrL R X A} (hx : x ∈ vx R X k A) :
    (mapSp φ).app A x ∈ vx R Y k A :=
  mem_eig.2 (by
    rw [derSp_mapSp (a := GrSpEnd.id R X) (b := GrSpEnd.id R Y) (fun _ _ _ _ => rfl),
      mem_eig.1 hx, map_smul])

lemma mapSp_mem_vxGe {φ : GrSpeciesHom R X Y} {p : ℕ} {x : FreeGrL R X A}
    (hx : x ∈ vxGe R X p A) : (mapSp φ).app A x ∈ vxGe R Y p A :=
  (iSup_le (fun k _ hy => mem_vxGe k.2 (mapSp_mem_vx hy)) :
    vxGe R X p A ≤ (vxGe R Y p A).comap ((mapSp φ).app A)) hx

/-- The differential `-δ + D₁` preserves the trees with at least `p` vertices. -/
lemma totD_mem_vxGe {d : GrSpEnd R X true} {D₁ : GrDer (GrOperadHom.id R (FreeGrL R X)) true}
    (hD : ∀ (k : ℕ) (x : FreeGrL R X A), x ∈ vx R X k A → D₁.app A x ∈ vx R X (k + 1) A)
    {p : ℕ} {x : FreeGrL R X A} (hx : x ∈ vxGe R X p A) : totD d D₁ A x ∈ vxGe R X p A :=
  (iSup_le (fun k y hy => by
    rw [Submodule.mem_comap, totD, LinearMap.add_apply, LinearMap.neg_apply]
    exact add_mem (neg_mem (mem_vxGe k.2 (derSp_mem_vx hy)))
      (mem_vxGe (by have := k.2; omega) (hD k.1 y hy))) :
    vxGe R X p A ≤ (vxGe R X p A).comap (totD d D₁ A)) hx

/-- **The splitting of the filtration** by the trees with exactly `p` vertices. -/
lemma split_vx [Algebra ℚ R] {d : GrSpEnd R X true}
    {D₁ : GrDer (GrOperadHom.id R (FreeGrL R X)) true}
    (hdd : ∀ x : FreeGrL R X A, totD d D₁ A (totD d D₁ A x) = 0)
    (hD : ∀ (k : ℕ) (x : FreeGrL R X A), x ∈ vx R X k A → D₁.app A x ∈ vx R X (k + 1) A)
    (p : ℕ) : QIso.Split (-(derSp d).app A) (D₁.app A) (vx R X p A) (vxGe R X (p + 1) A) where
  disj := vx_disjoint p
  dd x := hdd x
  mem₀ _ hu := neg_mem (derSp_mem_vx hu)
  mem₁ u hu := mem_vxGe le_rfl (hD p u hu)
  memW _ hw := totD_mem_vxGe hD hw

/-- **Derivations vanish on the trees without vertices**, over a field of characteristic zero. -/
lemma der_vx_zero [Algebra ℚ R] {e : Bool} {D : GrDer (GrOperadHom.id R (FreeGrL R X)) e}
    {x : FreeGrL R X A} (hx : x ∈ vx R X 0 A) : D.app A x = 0 := by
  have h0 : D.compHom (mapSp (GrSpEnd.zero R X false).toHom) = GrDer.zero _ e :=
    der_eq_zero fun B _ _ v => by
      rw [GrDer.compHom_app, mapSp_ι, GrSpEnd.toHom_app, GrSpEnd.zero_app, map_zero, map_zero]
  have hx' : (mapSp (GrSpEnd.zero R X false).toHom).app A x = x :=
    mapSp_eq_self _ (fun _ _ _ _ => by rw [GrSpEnd.zero_app, GrSpEnd.zero_app]) (mem_eig.2 (by
      rw [derSp_congr (ψ := GrSpEnd.id R X) (fun _ _ _ v => by
        rw [GrSpEnd.compl_app, GrSpEnd.zero_app, sub_zero]
        rfl), mem_eig.1 hx]))
  rw [← hx', ← GrDer.compHom_app, h0]
  rfl

/-! ### Comparing extensions through truncations -/

private lemma comp_trunc_eq {g g' : GrSpeciesHom R X Y} {m : ℕ}
    (hg : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ m →
      ∀ v : X B, g.app B v = g'.app B v)
    (B : Type) [Fintype B] [DecidableEq B] (v : X B) :
    (g.comp (GrSpEnd.trunc R X m).toHom).app B v
      = (g'.comp (GrSpEnd.trunc R X m).toHom).app B v := by
  rw [GrSpeciesHom.comp_app, GrSpeciesHom.comp_app, GrSpEnd.toHom_app, GrSpEnd.trunc_app]
  rcases le_or_gt (Fintype.card B) m with h | h
  · rw [if_pos h, one_smul, hg B h]
  · rw [if_neg (by omega), zero_smul, map_zero, map_zero]

variable [Algebra ℚ R]
  (hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ v : X B, v = 0)
  {g g' : GrSpeciesHom R X Y} {m : ℕ}
  (hg : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ m →
    ∀ v : X B, g.app B v = g'.app B v)
include hred hg

/-- **Morphisms agreeing on the generators of at most `m` inputs agree in the arities at most
`m`.** -/
theorem mapSp_eq_of_card_le (hA : Fintype.card A ≤ m) (x : FreeGrL R X A) :
    (mapSp g).app A x = (mapSp g').app A x := by
  rw [← mapSp_trunc_of_card_le hred hA x, mapSp_comp, mapSp_comp]
  exact mapSp_congr (comp_trunc_eq hg) _

/-- **Morphisms agreeing on the generators of at most `m` inputs agree on the trees with at least
two vertices in arity `m + 1`.** -/
theorem mapSp_eq_of_two_le (hm : 1 ≤ m) (hA : Fintype.card A = m + 1) {k : ℕ} (hk : 2 ≤ k)
    {x : FreeGrL R X A} (hx : x ∈ vx R X k A) : (mapSp g).app A x = (mapSp g').app A x := by
  rw [← mapSp_trunc_of_two_le hred hm hA hk hx, mapSp_comp, mapSp_comp]
  exact mapSp_congr (comp_trunc_eq hg) _

end Filtration

/-! ## Quasi-isomorphisms -/

variable (R) in
/-- **Surjectivity in homology** of a morphism of dg species in arity `A`. -/
def SurjAt (dV : GrSpEnd R V true) (dW : GrSpEnd R W true) (f : GrSpeciesHom R V W)
    (A : Type) [Fintype A] [DecidableEq A] : Prop :=
  ∀ y : W A, dW.app A y = 0 → ∃ x, dV.app A x = 0 ∧ ∃ w', f.app A x - y = dW.app A w'

variable (R) in
/-- **Injectivity in homology** of a morphism of dg species in arity `A`. -/
def InjAt (dV : GrSpEnd R V true) (dW : GrSpEnd R W true) (f : GrSpeciesHom R V W)
    (A : Type) [Fintype A] [DecidableEq A] : Prop :=
  ∀ x : V A, dV.app A x = 0 → ∀ w', f.app A x = dW.app A w' → ∃ z, dV.app A z = x

end FreeGrL

end General

section Field

variable {R : Type u} [Field R] [CharZero R]
  {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)] [GrSpecies R W]

namespace FreeGrL

namespace CompareData

variable {dV : GrSpEnd R V true} {dW : GrSpEnd R W true}
  {D₁ : GrDer (GrOperadHom.id R (FreeGrL R V)) true}
  {D₁' : GrDer (GrOperadHom.id R (FreeGrL R W)) true} {f : GrSpeciesHom R V W}
  (hc : CompareData dV dW D₁ D₁' f) (A : Type) [Fintype A] [DecidableEq A]
include hc

omit [CharZero R] in
lemma hom (p : ℕ) : QIso.SplitHom ((mapSp f).app A) (-(derSp dV).app A) (D₁.app A)
    (-(derSp dW).app A) (D₁'.app A) (vx R V p A) (vxGe R V (p + 1) A) (vx R W p A)
    (vxGe R W (p + 1) A) where
  memU _ hu := mapSp_mem_vx hu
  memW _ hw := mapSp_mem_vxGe hw
  comm₀ x := by
    rw [LinearMap.neg_apply, LinearMap.neg_apply, map_neg, derSp_mapSp (a := dV) hc.comm]
  comm₁ x := (hc.commD A x).symm

/-- **The filtrations by the number of vertices.** -/
lemma filt : QIso.FiltData (fun p => vx R V p A) (fun p => vxGe R V p A)
    (fun p => vx R W p A) (fun p => vxGe R W p A) (Fintype.card A) (-(derSp dV).app A)
    (D₁.app A) (-(derSp dW).app A) (D₁'.app A) ((mapSp f).app A) where
  split p := split_vx (hc.dd A) (hc.raise A) p
  split' p := split_vx (hc.dd' A) (hc.raise' A) p
  hom p := hc.hom A p
  sup p := vxGe_eq p
  sup' p := vxGe_eq p
  top := vxGe_card hc.redV
  top' := vxGe_card hc.redW

/-- **The graded pieces**: `F` is a quasi-isomorphism on the trees with `p` vertices as soon as
`T(k)` inverts `T(p' f p)` there. -/
theorem qiso_vx (s : Splitting dV) (s' : Splitting dW) (k : GrSpeciesHom R W V) (p : ℕ)
    (hGK : ∀ y ∈ vx R W p A, (mapSp (s'.p.toHom.comp (f.comp s.p.toHom))).app A
      ((mapSp k).app A y) = (mapSp s'.p.toHom).app A y)
    (hKG : ∀ x ∈ vx R V p A, (mapSp k).app A
      ((mapSp (s'.p.toHom.comp (f.comp s.p.toHom))).app A x) = (mapSp s.p.toHom).app A x) :
    QIso.Surj (vx R V p A) (vx R W p A) (-(derSp dV).app A) (-(derSp dW).app A)
        ((mapSp f).app A) ∧
      QIso.Inj (vx R V p A) (vx R W p A) (-(derSp dV).app A) (-(derSp dW).app A)
        ((mapSp f).app A) := by
  have hr := (s.retract (GrSpEnd.id R V) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ _ _ _ => rfl) p A).neg
  have hr' := (s'.retract (GrSpEnd.id R W) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ _ _ _ => rfl) p A).neg
  have hFD := (hc.hom A p).comm₀
  have hG : ∀ x, (mapSp s'.p.toHom).app A ((mapSp f).app A ((mapSp s.p.toHom).app A x))
      = (mapSp (s'.p.toHom.comp (f.comp s.p.toHom))).app A x := fun x =>
    (congrArg _ (mapSp_comp _ _ x)).trans (mapSp_comp _ _ _)
  exact ⟨QIso.surj_of_retract hr hr' (fun _ hx => mapSp_mem_vx hx) hFD hG
      (fun _ hy => mapSp_mem_vx hy) hGK,
    QIso.inj_of_retract hr hr' hFD hG hKG⟩

/-- **A quasi-isomorphism of the generators in the arities at most `|A|` induces one in arity
`A`.** -/
theorem qiso_of_le
    (hs : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ Fintype.card A →
      SurjAt R dV dW f B)
    (hi : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ Fintype.card A →
      InjAt R dV dW f B) :
    QIso.Surj ⊤ ⊤ (totD dV D₁ A) (totD dW D₁' A) ((mapSp f).app A) ∧
      QIso.Inj ⊤ ⊤ (totD dV D₁ A) (totD dW D₁' A) ((mapSp f).app A) := by
  obtain ⟨s⟩ := Splitting.exists_of_field dV hc.ddV
  obtain ⟨s'⟩ := Splitting.exists_of_field dW hc.ddW
  obtain ⟨k, hk⟩ := exists_compat f hc.comm s s' (· ≤ Fintype.card A)
    (fun n hn => hs (Fin n) (by rwa [Fintype.card_fin]))
    (fun n hn => hi (Fin n) (by rwa [Fintype.card_fin]))
  have hq := fun p => hc.qiso_vx A s s' k p
    (fun y _ => by
      rw [mapSp_comp]
      exact mapSp_eq_of_card_le hc.redW (fun B _ _ hB v => by exact (hk B hB).2 v) le_rfl y)
    (fun x _ => by
      rw [mapSp_comp]
      exact mapSp_eq_of_card_le hc.redV (fun B _ _ hB v => by exact (hk B hB).1 v) le_rfl x)
  have h := QIso.qiso_filt (hc.filt A) (fun p => (hq p).1) (fun p => (hq p).2) 0
  have e : vxGe R V 0 A = ⊤ := vxGe_zero
  have e' : vxGe R W 0 A = ⊤ := vxGe_zero
  simp only [e, e'] at h
  exact h

/-- **A quasi-isomorphism of the generators induces a quasi-isomorphism.** -/
theorem qiso_of_qiso
    (hs : ∀ (B : Type) [Fintype B] [DecidableEq B], SurjAt R dV dW f B)
    (hi : ∀ (B : Type) [Fintype B] [DecidableEq B], InjAt R dV dW f B) :
    QIso.Surj ⊤ ⊤ (totD dV D₁ A) (totD dW D₁' A) ((mapSp f).app A) ∧
      QIso.Inj ⊤ ⊤ (totD dV D₁ A) (totD dW D₁' A) ((mapSp f).app A) :=
  hc.qiso_of_le A (fun B _ _ _ => hs B) (fun B _ _ _ => hi B)

omit hc in
lemma surjAt_of_vx (hS : QIso.Surj (vx R V 1 A) (vx R W 1 A) (-(derSp dV).app A)
    (-(derSp dW).app A) ((mapSp f).app A)) : SurjAt R dV dW f A := by
  intro y hy
  obtain ⟨x, hx, hdx, z, hz, hxz⟩ := hS ((ι R W).app A y) (ι_mem_vx y)
    (by rw [LinearMap.neg_apply, derSp_ι, hy, map_zero, neg_zero])
  rw [eq_ι_genCoef hx] at hdx hxz
  rw [eq_ι_genCoef hz] at hxz
  rw [LinearMap.neg_apply, derSp_ι, neg_eq_zero, ← map_zero ((ι R V).app A)] at hdx
  refine ⟨genCoef R V A x, ι_injective hdx, -genCoef R W A z, ι_injective (R := R) (V := W) ?_⟩
  rw [map_sub, ← mapSp_ι, hxz, LinearMap.neg_apply, derSp_ι, map_neg, map_neg]

omit hc in
lemma injAt_of_vx (hI : QIso.Inj (vx R V 1 A) (vx R W 1 A) (-(derSp dV).app A)
    (-(derSp dW).app A) ((mapSp f).app A)) : InjAt R dV dW f A := by
  intro x hx w hw
  obtain ⟨z, hz, hdz⟩ := hI ((ι R V).app A x) (ι_mem_vx x)
    (by rw [LinearMap.neg_apply, derSp_ι, hx, map_zero, neg_zero]) (-(ι R W).app A w)
    (neg_mem (ι_mem_vx w)) (by rw [mapSp_ι, hw, LinearMap.neg_apply, map_neg, derSp_ι, neg_neg])
  rw [eq_ι_genCoef hz, LinearMap.neg_apply, derSp_ι, ← map_neg] at hdz
  exact ⟨-genCoef R V A z, by rw [map_neg]; exact ι_injective hdz⟩

/-- **The induction step of the reflection**: a quasi-isomorphism `F` in arity `A` with
`|A| = m + 1 ≥ 2`, with `f` one in the arities at most `m`, makes `f` one in arity `A`. -/
theorem qiso_step {m : ℕ} (hm : 1 ≤ m) (hA : Fintype.card A = m + 1)
    (hs_ : QIso.Surj ⊤ ⊤ (totD dV D₁ A) (totD dW D₁' A) ((mapSp f).app A))
    (hi_ : QIso.Inj ⊤ ⊤ (totD dV D₁ A) (totD dW D₁' A) ((mapSp f).app A))
    (hs : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ m → SurjAt R dV dW f B)
    (hi : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ m → InjAt R dV dW f B) :
    SurjAt R dV dW f A ∧ InjAt R dV dW f A := by
  obtain ⟨s⟩ := Splitting.exists_of_field dV hc.ddV
  obtain ⟨s'⟩ := Splitting.exists_of_field dW hc.ddW
  obtain ⟨k, hk⟩ := exists_compat f hc.comm s s' (· ≤ m)
    (fun n hn => hs (Fin n) (by rwa [Fintype.card_fin]))
    (fun n hn => hi (Fin n) (by rwa [Fintype.card_fin]))
  have hq := fun p (hp : 2 ≤ p) => hc.qiso_vx A s s' k p
    (fun y hy => by
      rw [mapSp_comp]
      exact mapSp_eq_of_two_le hc.redW (fun B _ _ hB v => by exact (hk B hB).2 v) hm hA hp hy)
    (fun x hx => by
      rw [mapSp_comp]
      exact mapSp_eq_of_two_le hc.redV (fun B _ _ hB v => by exact (hk B hB).1 v) hm hA hp hx)
  have hd := hc.filt A
  -- the trees with at least two vertices
  have h2 := QIso.qiso_filt_ge hd (p₀ := 2) (fun p hp => (hq p hp).1) (fun p hp => (hq p hp).2)
    2 le_rfl
  -- the trees without vertices are a direct summand
  have e0 : vxGe R V 0 A = vx R V 0 A ⊔ vxGe R V 1 A := vxGe_eq 0
  have e0' : vxGe R W 0 A = vx R W 0 A ⊔ vxGe R W 1 A := vxGe_eq 0
  have hs0 : QIso.Surj (vx R V 0 A ⊔ vxGe R V 1 A) (vx R W 0 A ⊔ vxGe R W 1 A)
      (-(derSp dV).app A + D₁.app A) (-(derSp dW).app A + D₁'.app A) ((mapSp f).app A) := by
    rw [← e0, ← e0', vxGe_zero, vxGe_zero]
    exact hs_
  have hi0 : QIso.Inj (vx R V 0 A ⊔ vxGe R V 1 A) (vx R W 0 A ⊔ vxGe R W 1 A)
      (-(derSp dV).app A + D₁.app A) (-(derSp dW).app A + D₁'.app A) ((mapSp f).app A) := by
    rw [← e0, ← e0', vxGe_zero, vxGe_zero]
    exact hi_
  have hs1 : QIso.Surj (vxGe R V 1 A) (vxGe R W 1 A)
      (-(derSp dV).app A + D₁.app A) (-(derSp dW).app A + D₁'.app A) ((mapSp f).app A) :=
    QIso.surj_of_sup_right (hd.split 0) (hd.split' 0) (hd.hom 0) (fun _ hu => der_vx_zero hu)
      (fun _ hu => der_vx_zero hu) hs0
  have hi1 : QIso.Inj (vxGe R V 1 A) (vxGe R W 1 A)
      (-(derSp dV).app A + D₁.app A) (-(derSp dW).app A + D₁'.app A) ((mapSp f).app A) :=
    QIso.inj_of_sup_right (hd.split 0) (fun _ hu => der_vx_zero hu) hi0
  -- the trees with one vertex
  have e1 : vxGe R V 1 A = vx R V 1 A ⊔ vxGe R V 2 A := vxGe_eq 1
  have e1' : vxGe R W 1 A = vx R W 1 A ⊔ vxGe R W 2 A := vxGe_eq 1
  rw [e1, e1'] at hs1 hi1
  exact ⟨surjAt_of_vx A (QIso.surj_of_sup (hd.split 1) (hd.split' 1) (hd.hom 1) h2.1 hs1 hi1),
    injAt_of_vx A (QIso.inj_of_sup (hd.split 1) (hd.split' 1) (hd.hom 1) h2.1 h2.2 hi1)⟩

/-- **A morphism of reduced dg species inducing a quasi-isomorphism of the free graded operads
is a quasi-isomorphism.** -/
theorem qiso_of_qiso_free
    (hs_ : ∀ (B : Type) [Fintype B] [DecidableEq B],
      QIso.Surj ⊤ ⊤ (totD dV D₁ B) (totD dW D₁' B) ((mapSp f).app B))
    (hi_ : ∀ (B : Type) [Fintype B] [DecidableEq B],
      QIso.Inj ⊤ ⊤ (totD dV D₁ B) (totD dW D₁' B) ((mapSp f).app B)) :
    SurjAt R dV dW f A ∧ InjAt R dV dW f A := by
  suffices h : ∀ n (B : Type) [Fintype B] [DecidableEq B], Fintype.card B = n →
      SurjAt R dV dW f B ∧ InjAt R dV dW f B from h _ A rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro B _ _ hB
    rcases le_or_gt n 1 with hn | hn
    · exact ⟨fun y _ => ⟨0, map_zero _, 0, by
          rw [hc.redW B (by omega) y, map_zero, map_zero, sub_zero]⟩,
        fun x _ _ _ => ⟨0, by rw [map_zero, hc.redV B (by omega) x]⟩⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact hc.qiso_step B (by omega) hB (hs_ B) (hi_ B)
        (fun C _ _ hC => (ih _ (by omega) C rfl).1) (fun C _ _ hC => (ih _ (by omega) C rfl).2)

end CompareData

end FreeGrL

end Field

end Operad
