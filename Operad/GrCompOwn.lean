/-
# Generators of graded composites by owners

A generator of the graded composite `M ∘ N` at `S` names the inputs by a bijection
`(Σ a, B a) ≃ S`. Equivalently, it assigns to each input `s ∈ S` the input `f s` of the outer
operation it lies above (its **owner**), the inner operation at `a` having as inputs the fibre
`{s // f s = a}` (`GrComposite.ownGen`). Every generator is of this form
(`GrComposite.mk_eq_ownGen`), and relabelling the inputs of the outer operation transports the
owners (`GrComposite.mk_ownGen_outer`).
-/
import Operad.GrComposite

universe u v w

namespace Operad

open Function Sym GerBV

variable {R : Type u} [CommRing R]
  {M : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M A)] [GrSpecies R M]
  {N : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N A)] [GrSpecies R N]

namespace GrComposite

/-- **The fibre of an owner function** over an input of the outer operation. -/
abbrev Fib {S A : Type} (f : S → A) (a : A) : Type := {s : S // f s = a}

variable {S : Type} [Fintype S] [DecidableEq S]

/-- **A generator given by owners**: the inner operation at `a` has as inputs the inputs owned by
`a`. -/
abbrev ownGen {A : Type} [Fintype A] [DecidableEq A] (L : LinOrd A) (m : M A) (f : S → A)
    (y : ∀ a, N (Fib f a)) : GrCompGen M N S :=
  ⟨A, Fib f, L, m, y, Equiv.sigmaFiberEquiv f⟩

/-- The owner of an input of a generator. -/
def owner (g : GrCompGen M N S) (s : S) : g.A := (g.e.symm s).1

/-- The inputs of an inner operation of a generator are the inputs it owns. -/
def fibEquiv (g : GrCompGen M N S) (a : g.A) : g.B a ≃ Fib (owner g) a :=
  (Equiv.sigmaSubtype a).symm.trans (Equiv.subtypeEquiv g.e fun p => by
    simp only [owner, Equiv.symm_apply_apply])

omit [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)] [Fintype S] [DecidableEq S] in
@[simp] lemma fibEquiv_apply (g : GrCompGen M N S) (a : g.A) (b : g.B a) :
    (fibEquiv g a b).1 = g.e ⟨a, b⟩ := rfl

/-- **Every generator is given by owners.** -/
lemma mk_eq_ownGen (g : GrCompGen M N S) :
    mk R g = mk R (ownGen g.L g.m (owner g) fun a => SymSpecies.map (R := R) (fibEquiv g a) (g.y a))
    := by
  refine (mk_inner g (fibEquiv g)).symm.trans ?_
  congr 2
  ext ⟨a, s, hs⟩
  subst hs
  show g.e ((fibEquiv g (owner g s)).symm ⟨s, rfl⟩ |> fun b => (⟨owner g s, b⟩ : Σ a, g.B a)) = s
  have : (⟨owner g s, (fibEquiv g (owner g s)).symm ⟨s, rfl⟩⟩ : Σ a, g.B a) = g.e.symm s := by
    apply g.e.injective
    rw [Equiv.apply_symm_apply]
    exact congrArg Subtype.val ((fibEquiv g (owner g s)).apply_symm_apply ⟨s, rfl⟩)
  simp only [this, Equiv.apply_symm_apply]

/-- The fibres of an owner function, relabelled along a bijection of the inputs. -/
def fibMap {S' A : Type} (e : S ≃ S') (f : S → A) (a : A) : Fib f a ≃ Fib (f ∘ e.symm) a :=
  Equiv.subtypeEquiv e fun s => by simp

omit [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)] [Fintype S] [DecidableEq S] in
@[simp] lemma fibMap_apply {S' A : Type} (e : S ≃ S') (f : S → A) (a : A) (s : Fib f a) :
    (fibMap e f a s).1 = e s.1 := rfl

/-- **Relabelling the inputs of a generator given by owners** relabels the owners. -/
lemma map_mk_ownGen {S' : Type} [Fintype S'] [DecidableEq S'] (e : S ≃ S') {A : Type}
    [Fintype A] [DecidableEq A] (L : LinOrd A) (m : M A) (f : S → A) (y : ∀ a, N (Fib f a)) :
    map e (mk R (ownGen L m f y))
      = mk R (ownGen L m (f ∘ e.symm) fun a => SymSpecies.map (R := R) (fibMap e f a) (y a)) := by
  rw [map_mk]
  refine (mk_inner (GrCompGen.relabel (ownGen L m f y) e) (fibMap e f)).symm.trans ?_
  congr 2
  ext ⟨a, s, hs⟩
  subst hs
  exact e.apply_symm_apply s

/-- The fibres of an owner function, along a bijection of the outer inputs. -/
def fibOuter {A A' : Type} (σ : A' ≃ A) (f : S → A) (a' : A') :
    Fib f (σ a') ≃ Fib (σ.symm ∘ f) a' :=
  Equiv.subtypeEquivRight fun s => by
    simp only [comp_apply]
    exact ⟨fun h => by rw [h, Equiv.symm_apply_apply], fun h => by rw [← h, Equiv.apply_symm_apply]⟩

/-- **Relabelling the inputs of the outer operation of a generator given by owners.** -/
lemma mk_ownGen_outer {A A' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    (σ : A' ≃ A) (L : LinOrd A) (m : M A') (f : S → A) (y : ∀ a, N (Fib f a)) :
    mk R (ownGen L (SymSpecies.map (R := R) σ m) f y)
      = mk R (ownGen (LinOrd.map σ.symm L) m (σ.symm ∘ f)
          fun a' => SymSpecies.map (R := R) (fibOuter σ f a') (y (σ a'))) := by
  refine (mk_outer (ownGen L (SymSpecies.map (R := R) σ m) f y) σ m).trans ?_
  refine (mk_inner (⟨A', fun a => Fib f (σ a), LinOrd.map σ.symm L, m, fun a => y (σ a),
    (Equiv.sigmaCongrLeft σ).trans (Equiv.sigmaFiberEquiv f)⟩ : GrCompGen M N S)
    (fibOuter σ f)).symm.trans ?_
  congr 2
  ext ⟨a', s, hs⟩
  rfl

/-- **Generators given by equal owner functions.** -/
lemma mk_ownGen_congr {A : Type} [Fintype A] [DecidableEq A] (L : LinOrd A) (m : M A)
    {f f' : S → A} (hf : f = f') (y : ∀ a, N (Fib f a)) :
    mk R (ownGen L m f y) = mk R (ownGen L m f' fun a =>
      SymSpecies.map (R := R) (Equiv.subtypeEquivRight fun s => by rw [hf]) (y a)) := by
  subst hf
  congr 2
  funext a
  rw [show (Equiv.subtypeEquivRight _ : Fib f a ≃ Fib f a) = Equiv.refl _ from
    Equiv.ext fun _ => rfl, SymSpecies.map_refl]

end GrComposite

end Operad
