/-
# From graded operads to symmetric and shuffle operads

The Koszulness `Koszul.IsKoszul` of a presented graded operad lives in the graded framework
(`GrOperad`, with parities and Koszul signs), and the Koszulness of shuffle operads
(`ShuffleBar.IsKoszul`, `Rules.IsKoszul`) in the shuffle framework (`ShuffleOperad`), which
receives the symmetric operads of `SymOperad` through the forgetful functor
`SymOperad.toShuffle`. This file is the first link between the graded framework and the other
two: the forgetful functor on even operations.

* **Even graded operads are symmetric operads** (`GrOperad.toSymOperad`): a graded operad without
  odd operations (`GrOperad.IsEven`) satisfies the axioms of a symmetric operad, the Koszul sign
  of parallel associativity being `1` on even operations.
* **The even part** (`GrOperad.evenSub`) of any graded operad is a graded suboperad, and an even
  graded operad; as a symmetric operad it is `GrOperad.EvenOp`, hence a shuffle operad
  `Shuf (EvenOp R P)` through `SymOperad.toShuffle`. A morphism of graded operads restricts to a
  morphism of symmetric operads between the even parts (`GrOperadHom.toEven`), and so of shuffle
  operads. For an even graded operad the even part is everything (`GrOperad.evenEquiv`).
* **Free and presented graded operads on even generators are even**
  (`FreeGrL.isEven`, `GrOperadIdeal.isEven_quot`, `Koszul.isEven_pres`): the even part is a
  graded suboperad containing the generators, by the induction principle of presented graded
  operads (`FreeGr.mem_of_presGen`). So for quadratic data `(E, r)` with `E` even the presented
  operad `P = T(E)/(r)` is, arity by arity, the shuffle operad `Shuf (EvenOp R (Pres R E r))`
  (`Koszul.presEvenEquiv`), a quotient of the shuffle operad of `T(E)` (`Koszul.presProjSh`,
  surjective by `Koszul.presProjSh_surjective`).

## What remains for `Koszul.IsKoszul`

The comparison of `Koszul.IsKoszul` with the shuffle notions goes through the Koszul criterion
`Koszul.isKoszul_iff` (`KoszulCriterion.lean`): `P` is Koszul iff `P^¡ → B(P, I)` is a
quasi-isomorphism in the arities at least two. This is the statement matching
`ShuffleBar.IsKoszul`, the homology of the shuffle bar construction vanishing below the diagonal,
whose top homology is the Koszul dual cooperad (`ShuffleKoszulDual.lean`); the Koszul complex
`P^¡ ∘_κ P` of `Koszul.isKoszul_iff_acyclic` has no shuffle counterpart in the library. Two
identifications are open, both arity by arity as complexes of vector spaces:

* the underlying shuffle operad of the free graded operad `T(E)` on an even binary species with
  the free shuffle operad on a basis of `E(2)` (Dotsenko–Khoroshkin). This one is done:
  `GrFreeEven.lean` reduces it to the ungraded free operad `FreeL R E`, and `ShuffleFreeL.lean`
  identifies `Shuf (FreeL R E)` with the free shuffle operad on a basis (`FreeL.shuffleEquiv`);
  for generators with odd parts, `ShuffleFreeGrL.lean` gives the signed shuffle-tree basis of
  the free graded operad (`FreeGrL.shuffleBasis`, `FreeGrL.comp_shEv`);
* the bar construction `B(P, I) = T^c(sI)` with the shuffle bar construction modulo its relator
  subcomplex, `ShuffleBar.C K n s ⧸ ShuffleBar.J K R`, which needs in addition the exactness of
  the cut cooperad.
-/
import Operad.GrKoszulDual
import Operad.GrSuboperad
import Operad.ShuffleOperad

universe u v w

namespace Operad

open Sym GerBV

/-! ## Even graded operads -/

namespace GrOperad

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]

variable (R P) in
/-- **A graded operad is even** when its operations have no odd part. -/
def IsEven : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (x : P A), GrOperad.par (R := R) true x = 0

/-- In an even graded operad every operation is its even part. -/
lemma par_false_of_isEven (h : IsEven R P) {A : Type} [Fintype A] [DecidableEq A] (x : P A) :
    GrOperad.par (R := R) false x = x := by
  have e := GrOperad.par_add (R := R) x
  rwa [h A x, add_zero] at e

/-- **An even graded operad is a symmetric operad**, forgetting the parities: on even operations
the Koszul sign of parallel associativity is `1`. -/
abbrev toSymOperad (h : IsEven R P) : SymOperad R P where
  map := GrOperad.map
  map_refl := GrOperad.map_refl
  map_trans := GrOperad.map_trans
  one := GrOperad.one R
  comp := GrOperad.comp
  map_comp := GrOperad.map_comp
  comp_one := GrOperad.comp_one
  one_comp := GrOperad.one_comp
  comp_assoc_seq := GrOperad.comp_assoc_seq
  comp_assoc_par hik x y z := by
    have e := GrOperad.comp_assoc_par (R := R) hik x (par_false_of_isEven h y)
      (par_false_of_isEven h z)
    rwa [Bool.and_self, σ_false, one_smul] at e

variable (R P) in
/-- **The even part of a graded operad**, a graded suboperad. -/
def evenSub : GrSuboperad R P where
  sub A _ _ := LinearMap.ker (GrOperad.par (R := R) (P := P) (A := A) true)
  par_mem b x hx := by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [GrOperad.par_par]
    cases b
    · rfl
    · exact hx
  map_mem e x hx := by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← GrOperad.map_par, hx, map_zero]
  one_mem := by
    rw [LinearMap.mem_ker, ← GrOperad.par_one (R := R) (P := P), GrOperad.par_par]
    rfl
  comp_mem i x y hx hy := by
    rw [LinearMap.mem_ker] at hx hy ⊢
    have ex : GrOperad.par (R := R) false x = x := by
      have e := GrOperad.par_add (R := R) x
      rwa [hx, add_zero] at e
    have ey : GrOperad.par (R := R) false y = y := by
      have e := GrOperad.par_add (R := R) y
      rwa [hy, add_zero] at e
    have e := GrOperad.comp_par (R := R) i false false x y
    rw [ex, ey] at e
    rw [← e]
    exact GrSpecies.par_par_ne (R := R) (V := P) (by decide) _

lemma mem_evenSub {A : Type} [Fintype A] [DecidableEq A] (x : P A) :
    x ∈ (evenSub R P).sub A ↔ GrOperad.par (R := R) true x = 0 :=
  LinearMap.mem_ker

/-- **The even part of a graded operad is even.** -/
lemma isEven_evenSub : IsEven R (evenSub R P).Op := fun _ _ _ x =>
  Subtype.ext ((mem_evenSub x.1).1 x.2)

/-- In an even graded operad the even part is everything. -/
lemma evenSub_eq_top (h : IsEven R P) (A : Type) [Fintype A] [DecidableEq A] :
    (evenSub R P).sub A = ⊤ :=
  eq_top_iff.2 fun x _ => (mem_evenSub x).2 (h A x)

variable (R P) in
/-- **The even part of a graded operad as a symmetric operad.** -/
def EvenOp (A : Type) [Fintype A] [DecidableEq A] : Type v := (evenSub R P).Op A

instance (A : Type) [Fintype A] [DecidableEq A] : AddCommGroup (EvenOp R P A) :=
  inferInstanceAs (AddCommGroup ((evenSub R P).Op A))

instance (A : Type) [Fintype A] [DecidableEq A] : Module R (EvenOp R P A) :=
  inferInstanceAs (Module R ((evenSub R P).Op A))

/-- **The even part of a graded operad is a symmetric operad**, and so, through
`SymOperad.toShuffle`, the shuffle operad `Shuf (EvenOp R P)`. -/
instance EvenOp.instSymOperad : SymOperad R (EvenOp R P) :=
  toSymOperad (R := R) (P := (evenSub R P).Op) isEven_evenSub

/-- The underlying operation of an even operation. -/
def EvenOp.val {A : Type} [Fintype A] [DecidableEq A] (x : EvenOp R P A) : P A :=
  Subtype.val (p := fun y => y ∈ (evenSub R P).sub A) x

lemma EvenOp.ext {A : Type} [Fintype A] [DecidableEq A] {x y : EvenOp R P A}
    (h : x.val = y.val) : x = y :=
  Subtype.ext h

@[simp] lemma EvenOp.val_add {A : Type} [Fintype A] [DecidableEq A] (x y : EvenOp R P A) :
    (x + y).val = x.val + y.val := rfl

@[simp] lemma EvenOp.val_smul {A : Type} [Fintype A] [DecidableEq A] (c : R)
    (x : EvenOp R P A) : (c • x).val = c • x.val := rfl

@[simp] lemma EvenOp.val_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (e : A ≃ B) (x : EvenOp R P A) :
    (SymOperad.map (R := R) e x).val = GrOperad.map (R := R) e x.val := rfl

@[simp] lemma EvenOp.val_one : (SymOperad.one R : EvenOp R P Unit).val = GrOperad.one (R := R) :=
  rfl

@[simp] lemma EvenOp.val_comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (i : A) (x : EvenOp R P A) (y : EvenOp R P B) :
    (SymOperad.comp (R := R) i x y).val = GrOperad.comp (R := R) i x.val y.val := rfl

/-- **For an even graded operad the even part is everything**, arity by arity. -/
noncomputable def evenEquiv (h : IsEven R P) (A : Type) [Fintype A] [DecidableEq A] :
    EvenOp R P A ≃ₗ[R] P A :=
  (LinearEquiv.ofEq _ _ (evenSub_eq_top h A)).trans Submodule.topEquiv

@[simp] lemma evenEquiv_apply (h : IsEven R P) {A : Type} [Fintype A] [DecidableEq A]
    (x : EvenOp R P A) : evenEquiv h A x = x.val := rfl

end GrOperad

namespace GrOperadHom

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]

/-- **A morphism of graded operads restricts to the even parts**, a morphism of symmetric
operads; through `SymOperadHom.toShuffle` it is a morphism of shuffle operads. -/
def toEven (φ : GrOperadHom R P Q) : SymOperadHom R (GrOperad.EvenOp R P) (GrOperad.EvenOp R Q)
    where
  app A _ _ := (φ.app A).restrict fun x hx => by
    rw [GrOperad.mem_evenSub] at hx ⊢
    rw [← φ.app_par, hx, map_zero]
  app_map e x := GrOperad.EvenOp.ext (φ.app_map e x.val)
  app_one := GrOperad.EvenOp.ext φ.app_one
  app_comp i x y := GrOperad.EvenOp.ext (φ.app_comp i x.val y.val)

@[simp] lemma toEven_app_val (φ : GrOperadHom R P Q) {A : Type} [Fintype A] [DecidableEq A]
    (x : GrOperad.EvenOp R P A) : (φ.toEven.app A x).val = φ.app A x.val := rfl

/-- A morphism of graded operads surjective in an arity, between even graded operads, is
surjective on the even parts. -/
lemma toEven_surjective (φ : GrOperadHom R P Q) (hP : GrOperad.IsEven R P)
    (hQ : GrOperad.IsEven R Q) {A : Type} [Fintype A] [DecidableEq A]
    (hφ : Function.Surjective (φ.app A)) : Function.Surjective (φ.toEven.app A) := by
  intro y
  obtain ⟨x, hx⟩ := hφ (GrOperad.evenEquiv hQ A y)
  refine ⟨(GrOperad.evenEquiv hP A).symm x, GrOperad.EvenOp.ext ?_⟩
  rw [toEven_app_val]
  have e := (GrOperad.evenEquiv hP A).apply_symm_apply x
  rw [GrOperad.evenEquiv_apply] at e
  rw [e, hx, GrOperad.evenEquiv_apply]

end GrOperadHom

/-! ## Presented graded operads on even generators -/

namespace GrSpecies

variable (R : Type u) [CommRing R] (V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]

/-- **A graded linear species is even** when its elements have no odd part. -/
def IsEven : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (v : V A), GrSpecies.par (R := R) true v = 0

end GrSpecies

namespace GrOperadIdeal

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]

/-- **A quotient of an even graded operad is even.** -/
theorem isEven_quot (I : GrOperadIdeal R P) (h : GrOperad.IsEven R P) :
    GrOperad.IsEven R I.Quot := by
  intro A _ _ X
  obtain ⟨x, rfl⟩ := I.proj_surjective A X
  show GrOperad.par (R := R) true (I.projHom.app A x) = 0
  rw [← I.projHom.app_par, h A x, map_zero]

end GrOperadIdeal

namespace FreeGrL

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]

/-- **The free graded operad on an even graded linear species is even**: its even part is a
graded suboperad containing the generators, the odd generators being zero. -/
theorem isEven (hV : GrSpecies.IsEven R V) : GrOperad.IsEven R (FreeGrL R V) := by
  intro A _ _ x
  refine (GrOperad.mem_evenSub x).1 (FreeGr.mem_of_presGen _ (fun k e => ?_) x)
  obtain ⟨⟨v, b⟩, hvb⟩ := e
  rw [GrOperad.mem_evenSub]
  cases b
  · have e := FreeGr.par_presGen (R := R) (r := grLinRel R V)
      (⟨(v, false), hvb⟩ : GrGen R V k)
    rw [← e]
    exact GrSpecies.par_par_ne (R := R) (V := FreeGrL R V) (show true ≠ false by decide) _
  · have hv : v = 0 := hvb.symm.trans (hV _ v)
    rw [← ι_app_hom hvb]
    subst hv
    rw [map_zero, map_zero]

end FreeGrL

namespace Koszul

variable {R : Type u} [Field R]
  {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (E A)] [GrSpecies R E]
  (r : ∀ n : ℕ, Set (FreeGrL R E (Fin n)))

/-- **A graded operad presented on even generators is even.** -/
theorem isEven_pres (hE : GrSpecies.IsEven R E) : GrOperad.IsEven R (Pres R E r) :=
  (GrOperadIdeal.span R r).isEven_quot (FreeGrL.isEven hE)

/-- **The presented operad as a shuffle operad**, arity by arity: for even generators the
presented graded operad is its even part, whose underlying shuffle operad is
`Shuf (EvenOp R (Pres R E r))`. -/
noncomputable def presEvenEquiv (hE : GrSpecies.IsEven R E) (A : Type) [Fintype A]
    [DecidableEq A] : GrOperad.EvenOp R (Pres R E r) A ≃ₗ[R] Pres R E r A :=
  GrOperad.evenEquiv (isEven_pres r hE) A

/-- **The quotient map `T(E) → P` as a morphism of shuffle operads**, between the underlying
shuffle operads of the even parts. -/
noncomputable def presProjSh :
    ShuffleOperadHom R (Shuf (GrOperad.EvenOp R (FreeGrL R E)))
      (Shuf (GrOperad.EvenOp R (Pres R E r))) :=
  (GrOperadIdeal.span R r).projHom.toEven.toShuffle

/-- For even generators, **`P` is a quotient of `T(E)` as a shuffle operad**: the quotient map is
surjective in every arity. -/
theorem presProjSh_surjective (hE : GrSpecies.IsEven R E) (A : Type) [Fintype A]
    [LinearOrder A] : Function.Surjective ((presProjSh r).app A) :=
  (GrOperadIdeal.span R r).projHom.toEven_surjective (FreeGrL.isEven hE) (isEven_pres r hE)
    ((GrOperadIdeal.span R r).proj_surjective A)

end Koszul

end Operad
