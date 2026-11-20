/-
# The convolution product on the cooperad of signed linear orders

For a set operad `S` with finite factorizations and sign data `δ`, the convolution product of
two invariant families `f`, `g` on the twisted linearization `SgnLin R δ`, `g` odd, is on a basis
element the sum over the factorizations of the element of their terms (`SgnLin.repW`,
`SgnLin.star_bas_sigma`), and the term of a factorization is that of its relabellings
(`SgnLin.repW_map`).

For the nonempty linear orders, a factorization at an input is determined by the composite
(`NOrd.comp_injective`), the inputs of the inner order are a window of ranks (`NOrd.mem_block`),
every window of a standard order gives a factorization (`NOrd.exists_fact`), and the term of a
factorization only depends on the sizes of the two orders and on the place of the inner one
(`NOrd.repW_eq_of_fact`). Hence **the convolution product on a standard order is a sum of planar
terms** (`NOrd.star_std`): one for each outer standard order on `j + 1 ≤ N` inputs and each place
`i ≤ j`, the inner standard order having `N - j` inputs (`NOrd.plT`, `NOrd.plTN`, `NOrd.idx`).
This is the shape of the `A∞` relation.
-/
import Operad.OrdCooperad
import Operad.CutStar

universe u v w

namespace Operad

open Sym GerBV
open scoped TensorProduct

/-! ## Convolution on a twisted linearization -/

namespace SgnLin

variable {R : Type u} [CommRing R]
  {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  [SetOperad.FiniteFact S] {δ : SetOperadHom S SgnD}
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
  {A B X Y : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype X]
  [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- **A convolution composite on a basis element**: the signed sum over its factorizations. -/
lemma compC_bas (i : X) (f : ConvOp R (SgnLin R δ) Q X) {g : ConvOp R (SgnLin R δ) Q Y}
    (hg : ConvOp.IsParC true g) (t : S (Without X i ⊕ Y)) :
    ConvOp.toLin (ConvOp.compC i f g) (bas δ R t)
      = ∑ pq ∈ (SetOperad.FiniteFact.finite i t).toFinset,
          σ R (SgnData.sgn i (δ.app X pq.1) (δ.app Y pq.2)) •
            GrOperad.comp (R := R) i
              (ConvOp.toLin f (GrSpecies.tw (R := R) true (bas δ R pq.1)))
              (ConvOp.toLin g (bas δ R pq.2)) := by
  have h2 : GrCooperad.decomp (R := R) (C := SgnLin R δ) i (bas δ R t)
      = ∑ pq ∈ (SetOperad.FiniteFact.finite i t).toFinset,
          σ R (SgnData.sgn i (δ.app X pq.1) (δ.app Y pq.2)) •
            (bas δ R pq.1 ⊗ₜ[R] bas δ R pq.2 : SgnLin R δ X ⊗[R] SgnLin R δ Y) :=
    (decompT_single (R := R) (δ := δ) i t 1).trans (Finset.sum_congr rfl fun pq _ => by
      rw [mul_one]
      rfl)
  rw [ConvOp.toLin_compC, LinearMap.comp_apply, LinearMap.comp_apply, h2, _root_.map_sum,
    _root_.map_sum]
  refine Finset.sum_congr rfl fun pq _ => ?_
  rw [_root_.map_smul, _root_.map_smul, ConvOp.kap_tmul f hg, ConvOp.mu_tmul]

/-- An invariant family commutes with the relabellings. -/
lemma inv_toLin_map (q : GrOperad.Inv R (ConvOp R (SgnLin R δ) Q)) (e : A ≃ B)
    (y : SgnLin R δ A) :
    ConvOp.toLin (q.1 B) (GrOperad.map (R := R) e y)
      = GrOperad.map (R := R) e (ConvOp.toLin (q.1 A) y) := by
  rw [← GrOperad.Inv.map_apply q e]
  show GrOperad.map (R := R) e (ConvOp.toLin _ (GrOperad.map (R := R) e.symm
    (GrOperad.map (R := R) e y))) = _
  rw [map_symm_map]

variable (f g : GrOperad.Inv R (ConvOp R (SgnLin R δ) Q))

/-- **The term of a factorization** `e·(p ∘ᵢ q)` in the convolution product of `f` and an odd
`g`. -/
noncomputable def repW {i : A} (e : Without A i ⊕ B ≃ X) (p : S A) (q : S B) : Q X :=
  GrOperad.map (R := R) e (σ R (SgnData.sgn i (δ.app A p) (δ.app B q)) •
    GrOperad.comp (R := R) i
      (ConvOp.toLin (f.1 A) (GrSpecies.tw (R := R) true (bas δ R p)))
      (ConvOp.toLin (g.1 B) (bas δ R q)))

/-- **The term of a factorization is that of its relabellings.** -/
theorem repW_map {A' B' : Type} [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']
    (α : A ≃ A') (β : B ≃ B') (i : A) (e' : Without A' (α i) ⊕ B' ≃ X) (p : S A) (q : S B) :
    repW f g e' (SetOperad.map α p) (SetOperad.map β q)
      = repW f g ((compEquiv α β i).trans e') p q := by
  have hs : SgnData.sgn (α i) (δ.app A' (SetOperad.map α p)) (δ.app B' (SetOperad.map β q))
      = SgnData.sgn i (δ.app A p) (δ.app B q) := by
    rw [δ.app_map, δ.app_map]
    exact SgnData.sgn_map α β i _ _
  have htw : GrSpecies.tw (R := R) true (GrOperad.map (R := R) α (bas δ R p))
      = GrOperad.map (R := R) α (GrSpecies.tw (R := R) true (bas δ R p)) :=
    (GrSpecies.map_tw true α _).symm
  unfold repW
  rw [hs, ← map_bas, ← map_bas, htw, inv_toLin_map f α, inv_toLin_map g β,
    ← GrOperad.map_comp, GrOperad.map_trans]
  simp only [_root_.map_smul]

/-- **The convolution product on a basis element, factorization by factorization**, for `g`
odd: the sum over the subsets `S'` of the inputs and the factorizations at `S'`. -/
theorem star_bas_sigma (hg : ∀ (B : Type) [Fintype B] [DecidableEq B], ConvOp.IsParC true (g.1 B))
    (t : S X) :
    ConvOp.toLin ((GrOperad.Inv.star R _ f g).1 X) (bas δ R t)
      = ∑ x ∈ (nonempties X).sigma (fun S' => (SetOperad.FiniteFact.finite none
          (SetOperad.map (splitEquiv S').symm t)).toFinset),
          repW f g (splitEquiv x.1) x.2.1 x.2.2 := by
  rw [GrOperad.Inv.star_apply, ConvOp.toLin_sum, LinearMap.coe_sum, Finset.sum_apply,
    Finset.sum_sigma]
  refine Finset.sum_congr rfl fun S' _ => ?_
  show ConvOp.toLin (ConvOp.mapC (splitEquiv S')
    (ConvOp.compC none (f.1 (SOut S')) (g.1 (SIn S')))) _ = _
  rw [ConvOp.mapC_apply]
  show GrOperad.map (R := R) (splitEquiv S') (ConvOp.toLin (ConvOp.compC none _ _)
    (GrOperad.map (R := R) (splitEquiv S').symm _)) = _
  rw [map_bas, compC_bas none _ (hg (SIn S')), map_sum]
  rfl

end SgnLin

/-! ## Linear orders: isomorphisms and restrictions -/

namespace Sym.LinOrd

variable {A A' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']

/-- **Two linear orders on sets of the same size are isomorphic.** -/
lemma exists_map_eq (x : LinOrd A) (y : LinOrd A') (h : Fintype.card A = Fintype.card A') :
    ∃ α : A ≃ A', LinOrd.map α x = y := by
  obtain ⟨e₁, h1⟩ : ∃ e₁ : A ≃ Fin (Fintype.card A'), LinOrd.map e₁ x = LinOrd.std _ :=
    ⟨_, FreeGr.map_toRank x h⟩
  obtain ⟨e₂, h2⟩ : ∃ e₂ : A' ≃ Fin (Fintype.card A'), LinOrd.map e₂ y = LinOrd.std _ :=
    ⟨_, FreeGr.map_toRank y rfl⟩
  refine ⟨e₁.trans e₂.symm, ?_⟩
  have h3 : LinOrd.map e₂.symm (LinOrd.map e₂ y) = y := LinOrd.ext fun a b => by simp
  rw [← h3, h2, ← h1]
  exact LinOrd.ext fun a b => Iff.rfl

omit [DecidableEq A] [DecidableEq A'] in
/-- **An isomorphism of linear orders is unique.** -/
lemma eq_of_map_eq {e e' : A ≃ A'} {x : LinOrd A} (h : LinOrd.map e x = LinOrd.map e' x) :
    e = e' := by
  have key : ∀ (f : A ≃ A') (a : A), (LinOrd.map f x).rank (f a) = x.rank a := fun f a => by
    rw [LinOrd.rank_map, Equiv.symm_apply_apply]
  exact Equiv.ext fun a => (LinOrd.map e' x).rank_injective ((h ▸ key e a).trans (key e' a).symm)

omit [Fintype A] [DecidableEq A] in
/-- The linear order pulled back along an injection into `Fin N`. -/
def comap {N : ℕ} (f : A → Fin N) (hf : Function.Injective f) : LinOrd A where
  lt a b := f a < f b
  irrefl a := lt_irrefl (f a)
  trans _ _ _ h h' := lt_trans h h'
  total _ _ h := lt_or_gt_of_ne fun h' => h (hf h')

end Sym.LinOrd

namespace NOrd

variable {A B A' B' X : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] [Fintype X] [DecidableEq X]

/-- **The standard order** on `Fin n`, for `n` positive. -/
def std (n : ℕ) (h : 0 < n) : NOrd (Fin n) := ⟨LinOrd.std n, ⟨⟨0, h⟩⟩⟩

/-- **A factorization at an input is determined by the composite.** -/
lemma comp_injective (i : A) {p p' : NOrd A} {q q' : NOrd B}
    (h : SetOperad.comp i p q = SetOperad.comp i p' q') : p = p' ∧ q = q' := by
  obtain ⟨b₀⟩ := q.2
  have hL : LinOrd.comp i p.1 q.1 = LinOrd.comp i p'.1 q'.1 := congrArg Subtype.val h
  have key : ∀ u v, (LinOrd.comp i p.1 q.1).lt u v ↔ (LinOrd.comp i p'.1 q'.1).lt u v :=
    fun u v => by rw [hL]
  refine ⟨Subtype.ext (LinOrd.ext fun a a' => ?_),
    Subtype.ext (LinOrd.ext fun b b' => key (.inr b) (.inr b'))⟩
  by_cases ha : a = i
  · by_cases ha' : a' = i
    · rw [ha, ha']
      exact ⟨fun h => (p.1.irrefl _ h).elim, fun h => (p'.1.irrefl _ h).elim⟩
    · rw [ha]
      exact key (.inr b₀) (.inl ⟨a', ha'⟩)
  · by_cases ha' : a' = i
    · rw [ha']
      exact key (.inl ⟨a, ha⟩) (.inr b₀)
    · exact key (.inl ⟨a, ha⟩) (.inl ⟨a', ha'⟩)

/-- **The inputs of the inner order of a factorization form a window of ranks.** -/
lemma mem_block {S' : Finset X} {p : NOrd (SOut S')} {q : NOrd (SIn S')} {t : NOrd X}
    (h : SetOperad.map (splitEquiv S') (SetOperad.comp none p q) = t) (x : X) :
    x ∈ S' ↔ (p.1.rank none ≤ t.1.rank x ∧
      t.1.rank x < p.1.rank none + Fintype.card (SIn S')) := by
  have ht : t.1 = LinOrd.map (splitEquiv S') (LinOrd.comp none p.1 q.1) := by
    rw [← h]
    rfl
  rw [ht, LinOrd.rank_map, LinOrd.mem_window]
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, by simp [splitEquiv, hx]⟩
  · rintro ⟨b, hb⟩
    have := congrArg (splitEquiv S') hb
    rw [Equiv.apply_symm_apply, splitEquiv_inr] at this
    rw [this]
    exact b.2

/-- **A window of `Fin N` gives a factorization of the standard order.** -/
lemma exists_fact {N : ℕ} (hN : 0 < N) {S' : Finset (Fin N)} {r : Fin N} (hr : r ∈ S')
    (hS : ∀ x y, x ∈ S' → y ∈ S' → ∀ z, x ≤ z → z ≤ y → z ∈ S') :
    ∃ (p : NOrd (SOut S')) (q : NOrd (SIn S')),
      SetOperad.comp none p q = SetOperad.map (splitEquiv S').symm (std N hN) := by
  have hrep : Function.Injective fun o : SOut S' => (o.elim r fun x => x.1 : Fin N) := by
    rintro (_ | x) (_ | y) h
    · rfl
    · have h' : r = y.1 := h
      exact (y.2 (h' ▸ hr)).elim
    · have h' : x.1 = r := h
      exact (x.2 (by rw [h']; exact hr)).elim
    · exact congrArg some (Subtype.ext h)
  refine ⟨⟨LinOrd.comap _ hrep, ⟨none⟩⟩,
    ⟨LinOrd.comap (fun s : SIn S' => s.1) Subtype.val_injective, ⟨⟨r, hr⟩⟩⟩,
    Subtype.ext (LinOrd.ext ?_)⟩
  rintro (⟨(_ | x), ho⟩ | s) (⟨(_ | y), ho'⟩ | s')
  · exact absurd rfl ho
  · exact absurd rfl ho
  · exact absurd rfl ho
  · exact absurd rfl ho'
  · exact Iff.rfl
  · show x.1 < r ↔ x.1 < s'.1
    constructor
    · intro h
      by_contra h'
      exact x.2 (hS s'.1 r s'.2 hr x.1 (not_lt.1 h') h.le)
    · intro h
      by_contra h'
      exact x.2 (hS r s'.1 hr s'.2 x.1 (not_lt.1 h') h.le)
  · exact absurd rfl ho'
  · show r < y.1 ↔ s.1 < y.1
    constructor
    · intro h
      by_contra h'
      exact y.2 (hS r s.1 hr s.2 y.1 h.le (not_lt.1 h'))
    · intro h
      by_contra h'
      exact y.2 (hS s.1 r s.2 hr y.1 h.le (not_lt.1 h'))
  · exact Iff.rfl

end NOrd

/-! ## The convolution product on the standard orders -/

section Planar

variable {R : Type u} [CommRing R]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
  {A B A' B' X : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] [Fintype X] [DecidableEq X]
  (f g : GrOperad.Inv R (ConvOp R (SgnLin R NOrd.sgnD) Q))

namespace NOrd

/-- **The term of a factorization only depends on the sizes and on the place of the inner
order.** -/
theorem repW_eq_of_fact {i : A} {i' : A'} {p : NOrd A} {q : NOrd B} {p' : NOrd A'}
    {q' : NOrd B'} {e : Without A i ⊕ B ≃ X} {e' : Without A' i' ⊕ B' ≃ X}
    (h : SetOperad.map e (SetOperad.comp i p q) = SetOperad.map e' (SetOperad.comp i' p' q'))
    (hA : Fintype.card A = Fintype.card A') (hB : Fintype.card B = Fintype.card B')
    (hr : p.1.rank i = p'.1.rank i') :
    SgnLin.repW f g e p q = SgnLin.repW f g e' p' q' := by
  obtain ⟨α, hα⟩ := LinOrd.exists_map_eq p.1 p'.1 hA
  obtain ⟨β, hβ⟩ := LinOrd.exists_map_eq q.1 q'.1 hB
  have hp : p' = SetOperad.map α p := Subtype.ext hα.symm
  have hq : q' = SetOperad.map β q := Subtype.ext hβ.symm
  have hi : α i = i' := p'.1.rank_injective (by
    rw [← hr, ← hα, LinOrd.rank_map, Equiv.symm_apply_apply])
  subst hi hp hq
  rw [SgnLin.repW_map]
  rw [← SetOperad.map_comp, ← SetOperad.map_trans] at h
  exact congrArg (fun E => SgnLin.repW f g E p q) (LinOrd.eq_of_map_eq (congrArg Subtype.val h))

/-- **The planar term** of the convolution product: the inner standard order on `l` inputs at
the place `i` of the outer standard order on `n` inputs. -/
noncomputable def plT {n : ℕ} (i : Fin n) (l N : ℕ) (h : N + 1 = n + l) (hl : 0 < l) :
    Q (Fin N) :=
  SgnLin.repW f g (posEquivF i l N h) (std n (Fin.pos i)) (std l hl)

/-- The planar term at the outer size `j + 1` and the place `i`, zero outside the range. -/
noncomputable def plTN (N : ℕ) (x : ℕ × ℕ) : Q (Fin N) :=
  if h : x.2 ≤ x.1 ∧ x.1 < N then
    plT f g (⟨x.2, Nat.lt_succ_of_le h.1⟩ : Fin (x.1 + 1)) (N - x.1) N (by omega) (by omega)
  else 0

/-- The index set of the planar terms: the outer sizes `j + 1 ≤ N` and the places `i ≤ j`. -/
def idx (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range N ×ˢ Finset.range N).filter fun x => x.2 ≤ x.1

lemma mem_idx {N : ℕ} {x : ℕ × ℕ} : x ∈ idx N ↔ x.2 ≤ x.1 ∧ x.1 < N := by
  rw [idx, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  omega

omit [DecidableEq X] in
lemma mem_nonempties {S' : Finset X} : S' ∈ nonempties X ↔ S'.Nonempty := by
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ S')

omit [Fintype X] [DecidableEq X] in
lemma card_SIn (S' : Finset X) : Fintype.card (SIn S') = S'.card := Fintype.card_coe S'

lemma card_SOut (S' : Finset X) : Fintype.card (SOut S') + S'.card = Fintype.card X + 1 := by
  have h1 : Fintype.card (SOut S') = Fintype.card {x : X // x ∉ S'} + 1 :=
    Fintype.card_option
  have h2 : Fintype.card {x : X // x ∉ S'} = Fintype.card X - Fintype.card {x : X // x ∈ S'} :=
    Fintype.card_subtype_compl _
  have h3 : Fintype.card {x : X // x ∈ S'} = S'.card := Fintype.card_coe S'
  have h4 : S'.card ≤ Fintype.card X := Finset.card_le_univ S'
  omega

/-- **The convolution product on a standard order, in planar terms**: for `g` odd, the sum over
the inner standard orders at the places of the outer standard orders. This is the shape of the
`A∞` relation. -/
theorem star_std (hg : ∀ (B : Type) [Fintype B] [DecidableEq B], ConvOp.IsParC true (g.1 B))
    (N : ℕ) (hN : 0 < N) :
    ConvOp.toLin ((GrOperad.Inv.star R _ f g).1 (Fin N)) (SgnLin.bas sgnD R (std N hN))
      = ∑ x ∈ idx N, plTN f g N x := by
  rw [SgnLin.star_bas_sigma f g hg]
  have hfact : ∀ {S' : Finset (Fin N)} {pq : NOrd (SOut S') × NOrd (SIn S')},
      pq ∈ (SetOperad.FiniteFact.finite none
        (SetOperad.map (splitEquiv S').symm (std N hN))).toFinset →
      SetOperad.map (splitEquiv S') (SetOperad.comp none pq.1 pq.2) = std N hN :=
    fun {S' pq} h => by
      rw [(SgnLin.mem_fact_iff none _ pq).1 h, SetOperad.map_map_symm]
  have hrk : ∀ x : Fin N, (std N hN).1.rank x = x := fun x => LinOrd.rank_std N x
  have hrN : ∀ {S' : Finset (Fin N)} (p : NOrd (SOut S')), S'.Nonempty →
      p.1.rank none + S'.card ≤ N := fun {S'} p _ => by
    have h1 := p.1.rank_lt_card none
    have h2 := card_SOut S'
    rw [Fintype.card_fin] at h2
    omega
  refine Finset.sum_bij (fun a _ => (N - a.1.card, a.2.1.1.rank none)) ?_ ?_ ?_ ?_
  · rintro ⟨S', p, q⟩ ha
    obtain ⟨hS, -⟩ := Finset.mem_sigma.1 ha
    have hne : S'.Nonempty := (mem_nonempties.1 hS)
    have := hrN p hne
    have := hne.card_pos
    exact mem_idx.2 ⟨by show p.1.rank none ≤ N - S'.card; omega, by show N - S'.card < N; omega⟩
  · rintro ⟨S₁, p₁, q₁⟩ ha ⟨S₂, p₂, q₂⟩ hb hab
    obtain ⟨hS₁, hf₁⟩ := Finset.mem_sigma.1 ha
    obtain ⟨hS₂, hf₂⟩ := Finset.mem_sigma.1 hb
    have hc₁ := (mem_nonempties.1 hS₁).card_pos
    have hc₂ := (mem_nonempties.1 hS₂).card_pos
    have hl₁ := Finset.card_le_univ S₁
    have hl₂ := Finset.card_le_univ S₂
    rw [Fintype.card_fin] at hl₁ hl₂
    have h1 : N - S₁.card = N - S₂.card := congrArg Prod.fst hab
    have h2 : p₁.1.rank none = p₂.1.rank none := congrArg Prod.snd hab
    have hcard : S₁.card = S₂.card := by omega
    have hSS : S₁ = S₂ := Finset.ext fun x => by
      rw [mem_block (hfact hf₁) x, mem_block (hfact hf₂) x, card_SIn, card_SIn, h2, hcard]
    subst hSS
    have h3 := comp_injective none (((SgnLin.mem_fact_iff none _ (p₁, q₁)).1 hf₁).trans
      ((SgnLin.mem_fact_iff none _ (p₂, q₂)).1 hf₂).symm)
    have h31 : p₁ = p₂ := h3.1
    have h32 : q₁ = q₂ := h3.2
    rw [h31, h32]
  · rintro ⟨j, i⟩ hx
    obtain ⟨hij, hjN⟩ := mem_idx.1 hx
    replace hij : i ≤ j := hij
    replace hjN : j < N := hjN
    let S' : Finset (Fin N) := Finset.univ.filter fun x => i ≤ (x : ℕ) ∧ (x : ℕ) < i + (N - j)
    have hmem : ∀ x : Fin N, x ∈ S' ↔ i ≤ (x : ℕ) ∧ (x : ℕ) < i + (N - j) := fun x => by
      rw [Finset.mem_filter]
      exact and_iff_right (Finset.mem_univ x)
    have hr : (⟨i, by omega⟩ : Fin N) ∈ S' := (hmem _).2 ⟨le_rfl, by show i < i + (N - j); omega⟩
    obtain ⟨p, q, hpq⟩ := exists_fact hN hr fun x y hx hy z hxz hzy => (hmem z).2
      ⟨((hmem x).1 hx).1.trans hxz, lt_of_le_of_lt hzy ((hmem y).1 hy).2⟩
    have hne : S'.Nonempty := ⟨_, hr⟩
    have hf : (p, q) ∈ (SetOperad.FiniteFact.finite none
        (SetOperad.map (splitEquiv S').symm (std N hN))).toFinset :=
      (SgnLin.mem_fact_iff none _ (p, q)).2 hpq
    have hb := fun x => mem_block (hfact hf) x
    simp only [hrk, card_SIn] at hb
    have hrN' := hrN p hne
    have hc := hne.card_pos
    have h1 := (hb ⟨i, by omega⟩).1 hr
    have h2 := (hmem ⟨p.1.rank none, by omega⟩).1 ((hb ⟨p.1.rank none, by omega⟩).2
      ⟨le_rfl, by show p.1.rank none < p.1.rank none + S'.card; omega⟩)
    have h3 := (hb ⟨i + (N - j) - 1, by omega⟩).1 ((hmem ⟨i + (N - j) - 1, by omega⟩).2
      ⟨by show i ≤ i + (N - j) - 1; omega, by show i + (N - j) - 1 < i + (N - j); omega⟩)
    have h4 := (hmem ⟨p.1.rank none + S'.card - 1, by omega⟩).1
      ((hb ⟨p.1.rank none + S'.card - 1, by omega⟩).2
        ⟨by show p.1.rank none ≤ p.1.rank none + S'.card - 1; omega,
          by show p.1.rank none + S'.card - 1 < p.1.rank none + S'.card; omega⟩)
    simp only at h1 h2 h3 h4
    refine ⟨⟨S', p, q⟩, Finset.mem_sigma.2 ⟨mem_nonempties.2 hne, hf⟩, ?_⟩
    show (N - S'.card, p.1.rank none) = (j, i)
    refine Prod.ext ?_ ?_
    · show N - S'.card = j
      omega
    · show p.1.rank none = i
      omega
  · rintro ⟨S', p, q⟩ ha
    obtain ⟨hS, hf⟩ := Finset.mem_sigma.1 ha
    have hne : S'.Nonempty := mem_nonempties.1 hS
    have hrN' := hrN p hne
    have hc := hne.card_pos
    have hcO := card_SOut S'
    rw [Fintype.card_fin] at hcO
    have hcond : p.1.rank none ≤ N - S'.card ∧ N - S'.card < N := by omega
    show SgnLin.repW f g (splitEquiv S') p q = plTN f g N (N - S'.card, p.1.rank none)
    rw [plTN, dif_pos hcond]
    refine repW_eq_of_fact f g ((hfact hf).trans ?_) ?_ ?_ ?_
    · exact (Subtype.ext (map_posEquivF _ _)).symm
    · rw [Fintype.card_fin]
      omega
    · rw [card_SIn, Fintype.card_fin]
      omega
    · exact (LinOrd.rank_std (N - S'.card + 1) ⟨p.1.rank none, by omega⟩).symm

end NOrd

end Planar

end Operad
