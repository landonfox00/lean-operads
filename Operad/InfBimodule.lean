/-
# Infinitesimal bimodules over a symmetric operad

An *infinitesimal bimodule* over a symmetric operad `P` is a collection `M`, functorial in
bijections, with partial compositions on both sides,

  `actL i : P A → M B → M (A ∖ i ⊔ B)`   (insert an element of `M` into an operation of `P`),
  `actR i : M A → P B → M (A ∖ i ⊔ B)`   (insert an operation of `P` into an element of `M`),

satisfying every operad axiom in which exactly one of the elements involved lies in `M`: the two
equivariances, the two unit laws, and sequential and parallel associativity with the element of
`M` in each position. Every operad is an infinitesimal bimodule over itself (`self`), and an
infinitesimal bimodule restricts along a morphism of operads (`restrict`); a morphism of
infinitesimal bimodules commutes with relabelling and with both actions (`Hom`).

This is the frame of the statement that a value is "a morphism of `Perm`-bimodules": the operad
of games is an infinitesimal bimodule over `Perm` by restriction along the additive games, `Perm`
is one over itself, and the statement is that the value is a morphism between them.
-/
import Operad.Sym

universe u v v' w w'

namespace Operad

open Sym

/-- **An infinitesimal bimodule over a symmetric operad `P`.** -/
class SymInfBimodule (R : Type u) [CommRing R]
    (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]
    (M : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M A)] where
  /-- Relabelling. -/
  map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] :
    (A ≃ B) → M A →ₗ[R] M B
  map_refl {A : Type} [Fintype A] [DecidableEq A] (x : M A) : map (Equiv.refl A) x = x
  map_trans {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (e : A ≃ B) (f : B ≃ C) (x : M A) :
    map (e.trans f) x = map f (map e x)
  /-- Insert an element of `M` at the input `i` of an operation of `P`. -/
  actL {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A) :
    P A →ₗ[R] M B →ₗ[R] M (Without A i ⊕ B)
  /-- Insert an operation of `P` at the input `i` of an element of `M`. -/
  actR {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A) :
    M A →ₗ[R] P B →ₗ[R] M (Without A i ⊕ B)
  map_actL {A A' B B' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] (σ : A ≃ A') (τ : B ≃ B') (i : A)
    (p : P A) (m : M B) :
    map (compEquiv σ τ i) (actL i p m) = actL (σ i) (SymOperad.map (R := R) σ p) (map τ m)
  map_actR {A A' B B' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] (σ : A ≃ A') (τ : B ≃ B') (i : A)
    (m : M A) (p : P B) :
    map (compEquiv σ τ i) (actR i m p) = actR (σ i) (map σ m) (SymOperad.map (R := R) τ p)
  actR_one {A : Type} [Fintype A] [DecidableEq A] (i : A) (m : M A) :
    map (rightUnitEquiv i) (actR i m (SymOperad.one R)) = m
  one_actL {B : Type} [Fintype B] [DecidableEq B] (m : M B) :
    map (leftUnitEquiv B) (actL () (SymOperad.one R) m) = m
  /-- `(m ∘ᵢ p) ∘ⱼ q = m ∘ᵢ (p ∘ⱼ q)`. -/
  seq_mpp {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] (i : A) (j : B) (m : M A) (p : P B) (q : P D) :
    map (seqEquiv i j D) (actR (Sum.inr j) (actR i m p) q)
      = actR i m (SymOperad.comp (R := R) j p q)
  /-- `(p ∘ᵢ m) ∘ⱼ q = p ∘ᵢ (m ∘ⱼ q)`. -/
  seq_pmp {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] (i : A) (j : B) (p : P A) (m : M B) (q : P D) :
    map (seqEquiv i j D) (actR (Sum.inr j) (actL i p m) q) = actL i p (actR j m q)
  /-- `(p ∘ᵢ q) ∘ⱼ m = p ∘ᵢ (q ∘ⱼ m)`. -/
  seq_ppm {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] (i : A) (j : B) (p : P A) (q : P B) (m : M D) :
    map (seqEquiv i j D) (actL (Sum.inr j) (SymOperad.comp (R := R) i p q) m)
      = actL i p (actL j q m)
  /-- `(m ∘ᵢ p) ∘ₖ q = (m ∘ₖ q) ∘ᵢ p`. -/
  par_mpp {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] {i k : A} (hik : i ≠ k) (m : M A) (p : P B) (q : P D) :
    map (parEquiv hik B D) (actR (Sum.inl ⟨k, Ne.symm hik⟩) (actR i m p) q)
      = actR (Sum.inl ⟨i, hik⟩) (actR k m q) p
  /-- `(p ∘ᵢ m) ∘ₖ q = (p ∘ₖ q) ∘ᵢ m`. -/
  par_pmp {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] {i k : A} (hik : i ≠ k) (p : P A) (m : M B) (q : P D) :
    map (parEquiv hik B D) (actR (Sum.inl ⟨k, Ne.symm hik⟩) (actL i p m) q)
      = actL (Sum.inl ⟨i, hik⟩) (SymOperad.comp (R := R) k p q) m
  /-- `(p ∘ᵢ q) ∘ₖ m = (p ∘ₖ m) ∘ᵢ q`. -/
  par_ppm {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] {i k : A} (hik : i ≠ k) (p : P A) (q : P B) (m : M D) :
    map (parEquiv hik B D) (actL (Sum.inl ⟨k, Ne.symm hik⟩) (SymOperad.comp (R := R) i p q) m)
      = actR (Sum.inl ⟨i, hik⟩) (actL k p m) q

namespace SymInfBimodule

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]

/-- **Every operad is an infinitesimal bimodule over itself.** -/
instance self : SymInfBimodule R P P where
  map e := SymOperad.map e
  map_refl := SymOperad.map_refl
  map_trans := SymOperad.map_trans
  actL i := SymOperad.comp i
  actR i := SymOperad.comp i
  map_actL := SymOperad.map_comp
  map_actR := SymOperad.map_comp
  actR_one := SymOperad.comp_one
  one_actL := SymOperad.one_comp
  seq_mpp := SymOperad.comp_assoc_seq
  seq_pmp := SymOperad.comp_assoc_seq
  seq_ppm := SymOperad.comp_assoc_seq
  par_mpp := SymOperad.comp_assoc_par
  par_pmp := SymOperad.comp_assoc_par
  par_ppm := SymOperad.comp_assoc_par

variable {P' : (A : Type) → [Fintype A] → [DecidableEq A] → Type v'}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P' A)] [SymOperad R P']
  {M : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M A)]

/-- **Restriction along a morphism of operads.** -/
@[reducible] def restrict [SymInfBimodule R P M] (f : SymOperadHom R P' P) :
    SymInfBimodule R P' M where
  map e := map (P := P) e
  map_refl := map_refl (P := P)
  map_trans := map_trans (P := P)
  actL i := (actL (P := P) i).comp (f.app _)
  actR i := (actR (P := P) i).compl₂ (f.app _)
  map_actL σ τ i p m := by
    simp only [LinearMap.coe_comp, Function.comp_apply, map_actL, f.app_map]
  map_actR σ τ i m p := by
    simp only [LinearMap.compl₂_apply, map_actR, f.app_map]
  actR_one i m := by
    simp only [LinearMap.compl₂_apply, f.app_one, actR_one]
  one_actL m := by
    simp only [LinearMap.coe_comp, Function.comp_apply, f.app_one, one_actL]
  seq_mpp i j m p q := by
    simp only [LinearMap.compl₂_apply, seq_mpp, f.app_comp]
  seq_pmp i j p m q := by
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.compl₂_apply, seq_pmp]
  seq_ppm i j p q m := by
    simp only [LinearMap.coe_comp, Function.comp_apply, f.app_comp, seq_ppm]
  par_mpp hik m p q := by
    simp only [LinearMap.compl₂_apply, par_mpp]
  par_pmp hik p m q := by
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.compl₂_apply, par_pmp,
      f.app_comp]
  par_ppm hik p q m := by
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.compl₂_apply, f.app_comp,
      par_ppm]

end SymInfBimodule

/-- **A morphism of infinitesimal bimodules** over `P`: components commuting with relabelling and
with both actions. -/
structure SymInfBimodule.Hom (R : Type u) [CommRing R]
    (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]
    (M : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M A)]
    (N : (A : Type) → [Fintype A] → [DecidableEq A] → Type w')
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N A)]
    [SymInfBimodule R P M] [SymInfBimodule R P N] where
  /-- The component at a finite input set. -/
  app (A : Type) [Fintype A] [DecidableEq A] : M A →ₗ[R] N A
  app_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    (x : M A) :
    app B (SymInfBimodule.map (R := R) (P := P) e x)
      = SymInfBimodule.map (R := R) (P := P) e (app A x)
  app_actL {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (p : P A) (m : M B) :
    app (Without A i ⊕ B) (SymInfBimodule.actL (R := R) i p m)
      = SymInfBimodule.actL (R := R) i p (app B m)
  app_actR {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (m : M A) (p : P B) :
    app (Without A i ⊕ B) (SymInfBimodule.actR (R := R) (P := P) i m p)
      = SymInfBimodule.actR (R := R) (P := P) i (app A m) p

end Operad
