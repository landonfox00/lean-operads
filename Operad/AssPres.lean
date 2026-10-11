/-
# The presentation of `Ass`

The associative operad is regular: its set operad, the linear orders on nonempty sets (`AssSet`),
is the symmetrization of the planar operad with one operation in each positive arity, the
underlying planar operad of the commutative set operad (`Reg.hadamardIso`). That planar operad is
presented
by one binary operation and associativity: every operation of the presented operad is a right
comb (`Arr.pres_isRComb`), and there is one right comb in each arity (`PAss.presIso`). So `Ass` is
presented by one binary operation, without symmetries, and associativity with all its relabellings
(`AssSet.presIso`), and a morphism of operads in modules out of `Ass` is an associative binary
operation (`Ass.homEquiv`).
-/
import Operad.Regular
import Operad.ComSet

universe u v w

namespace Operad

open Sym NSSetOperad NSSetOperad.Arr

/-- The generator of the associative operad. -/
inductive AssGen : ℕ → Type
  | m : AssGen 2

/-- The left comb `m ∘₁ m`, as an expression. -/
def AssGen.lc : NSSyn AssGen 3 := NSSyn.comp 0 1 (NSSyn.gen AssGen.m) (NSSyn.gen AssGen.m)

/-- The right comb `m ∘₂ m`, as an expression. -/
def AssGen.rc : NSSyn AssGen 3 := NSSyn.comp 1 0 (NSSyn.gen AssGen.m) (NSSyn.gen AssGen.m)

/-- **Associativity**: `(x y) z = x (y z)`. -/
inductive AssRel : ∀ n : ℕ, NSSyn AssGen n → NSSyn AssGen n → Prop
  | assoc : AssRel 3 AssGen.lc AssGen.rc

/-- **An associative binary operation** in a planar set operad. -/
structure AssData (S : ℕ → Type v) [NSSetOperad S] where
  /-- The operation. -/
  m : S 2
  assoc : leftComb m m = rightComb m m

namespace AssData

variable {S : ℕ → Type v} [NSSetOperad S] (d : AssData S)

/-- The generator value. -/
def gens : ∀ n, AssGen n → S n := fun _ g => match g with | .m => d.m

lemma eval_lc : (⟨3, NSSyn.eval d.gens AssGen.lc⟩ : Arr S) = leftComb d.m d.m :=
  (leftComb_eq _ _).symm

lemma eval_rc : (⟨3, NSSyn.eval d.gens AssGen.rc⟩ : Arr S) = rightComb d.m d.m :=
  (rightComb_eq _ _).symm

/-- The generator value respects associativity. -/
theorem respects : NSPres.Respects AssRel d.gens := by
  intro n x y h
  cases h
  exact mk_eq_mk_iff.1 (by rw [eval_lc, eval_rc]; exact d.assoc)

theorem rotClosed : RotClosed ({d.m} : Set (S 2)) := by
  rintro _ rfl _ rfl
  exact ⟨d.m, rfl, d.m, rfl, d.assoc⟩

/-- **Generator values respecting associativity are associative operations.** -/
def equivRespects : {f : ∀ n, AssGen n → S n // NSPres.Respects AssRel f} ≃ AssData S where
  toFun f :=
    { m := f.1 2 .m
      assoc := by
        rw [leftComb_eq, rightComb_eq]
        exact mk_eq_mk_iff.2 (f.2 _ _ AssRel.assoc) }
  invFun d := ⟨d.gens, d.respects⟩
  left_inv f := Subtype.ext (funext fun _ => funext fun g => by cases g; rfl)
  right_inv _ := rfl

end AssData

/-- **The planar operad with one operation in each positive arity**, the planar version of the
associative operad. -/
abbrev PAss : ℕ → Type := SetOperad.toNSSet ComSet

namespace PAss

instance (n : ℕ) : Subsingleton (PAss n) := inferInstanceAs (Subsingleton (ComSet (Fin n)))

/-- The generator of the presented operad. -/
def presData : AssData (NSPres AssGen AssRel) where
  m := NSPres.gen AssGen.m
  assoc := by
    rw [leftComb_eq, rightComb_eq]
    exact congrArg (fun x => (⟨3, x⟩ : Arr (NSPres AssGen AssRel)))
      (NSPres.mk_eq_mk_of_rel AssRel.assoc)

/-- The binary operation. -/
def mData : AssData PAss where
  m := ComSet.mu
  assoc := by
    rw [leftComb_eq, rightComb_eq]
    exact mk_eq_mk_iff.2 (Subsingleton.elim _ _)

/-- **The evaluation morphism.** -/
def ev : NSSetOperadHom (NSPres AssGen AssRel) PAss := NSPres.lift mData.gens mData.respects

/-- **Every operation of the presented operad is the right comb of its arity.** -/
theorem eq_rcomb (X : Arr (NSPres AssGen AssRel)) :
    X = rcomb (List.replicate (X.1 - 1) presData.m) := by
  obtain ⟨l, hl, rfl⟩ := pres_isRComb presData.rotClosed
    (fun n g => by cases g; exact isRComb_of_mem rfl) X
  have hl' : l = List.replicate l.length presData.m := List.eq_replicate_iff.2 ⟨rfl, hl⟩
  conv_lhs => rw [hl']
  congr 2
  rw [rcomb_fst]
  omega

theorem map_ev_injective : Function.Injective (Arr.map ev) := by
  intro X Y h
  have h1 : X.1 = Y.1 := by simpa using congrArg Sigma.fst h
  rw [eq_rcomb X, eq_rcomb Y, h1]

theorem ev_bijective (n : ℕ) : Function.Bijective (ev.app n) := by
  constructor
  · intro x y h
    exact mk_eq_mk_iff.1 (map_ev_injective (a₁ := ⟨n, x⟩) (a₂ := ⟨n, y⟩)
      (by rw [map_mk, map_mk, h]))
  · intro s
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := by
      obtain ⟨a⟩ := s.down
      exact ⟨n - 1, by have := a.2; omega⟩
    subst hk
    have hX : (rcomb (List.replicate k presData.m)).1 = k + 1 := by simp
    exact ⟨hX ▸ (rcomb (List.replicate k presData.m)).2, Subsingleton.elim _ _⟩

/-- **The planar associative operad is presented by one binary operation and associativity.** -/
noncomputable def presIso : NSSetOperadIso (NSPres AssGen AssRel) PAss :=
  NSSetOperadIso.ofBijective ev ev_bijective

end PAss

/-- **The set operad of non-unital associative algebras**: a linear order on a nonempty set of
inputs. (The operad `Sym.Ass` also has the empty order in arity zero.) -/
abbrev AssSet := Hadamard (fun A _ _ => LinOrd A) ComSet

namespace AssSet

/-- **The presentation of the associative operad**: it is presented by one binary operation,
without symmetries, and associativity with all its relabellings. -/
noncomputable def presIso : SetOperadIso (Pres AssGen (symRel AssRel)) AssSet :=
  Reg.presIso.trans ((Reg.mapIso PAss.presIso).trans Reg.hadamardIso)

end AssSet

namespace Ass

variable (R : Type u) [CommRing R] {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]

/-- **The universal property of the non-unital associative operad**: a morphism of operads in
`R`-modules out of it is an associative binary operation. -/
noncomputable def homEquiv :
    SymOperadHom R (Lin R AssSet) Q ≃ AssData (SetOperad.toNSSet (Und R Q)) :=
  (linHomEquiv R).symm.trans <| AssSet.presIso.precompEquiv.trans <| Pres.homEquiv.trans <|
    (Equiv.subtypeEquivRight (q := fun f =>
      NSPres.Respects (S := SetOperad.toNSSet (Und R Q)) AssRel f)
        fun f => respects_symRel_iff AssRel f).trans AssData.equivRespects

end Ass

end Operad
