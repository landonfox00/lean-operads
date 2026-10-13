/-
# Colored operads

A **colored operad** with colors `C` has operations with a finite set of inputs `A` colored by
`c : A → C` and an output color `d`; the input `i` of an operation can be filled by an operation
whose output color is the color of that input. Relabellings and compositions carry proofs that the
colors match, so that no transport along equalities of colors enters the axioms.

* `ColOperad`: colored operads in `R`-modules, in the species convention of `Operad.SymOperad`.
* `ColOperadHom`: their morphisms.
* `ColEnd R V`: **the endomorphism colored operad** of a family of modules `V : C → Type`, the
  multilinear maps `∏ₐ V (c a) → V d`; `ColAlgebra`: an algebra over a colored operad, a morphism
  into it.
* **Operads are one-colored operads** (`SymOperad.toCol`), with the same algebras
  (`SymOperad.colAlgebraEquiv`).
-/
import Operad.EndOperad

universe u v w x

namespace Operad

open Sym

/-- The colors of the inputs of a composite. -/
abbrev compColor {C : Type w} {A B : Type} [DecidableEq A] (cA : A → C) (i : A) (cB : B → C) :
    Without A i ⊕ B → C :=
  Sum.elim (fun a => cA a.1) cB

/-- **A colored operad in `R`-modules**: relabellings preserving the colors, units of every color,
and partial compositions along matching colors. -/
class ColOperad (R : Type u) [CommRing R] (C : Type w)
    (P : (A : Type) → [Fintype A] → [DecidableEq A] → (A → C) → C → Type v)
    [∀ (A : Type) [Fintype A] [DecidableEq A] (c : A → C) (d : C), AddCommGroup (P A c d)]
    [∀ (A : Type) [Fintype A] [DecidableEq A] (c : A → C) (d : C), Module R (P A c d)] where
  /-- Relabelling the inputs along a bijection preserving the colors. -/
  map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] {c : A → C}
    {c' : B → C} {d : C} (e : A ≃ B) (h : ∀ a, c' (e a) = c a) : P A c d →ₗ[R] P B c' d
  /-- Relabelling along the identity changes nothing. -/
  map_refl {A : Type} [Fintype A] [DecidableEq A] {c : A → C} {d : C}
    (h : ∀ a, c ((Equiv.refl A) a) = c a) (x : P A c d) : map (Equiv.refl A) h x = x
  /-- Relabelling is functorial. -/
  map_trans {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype D]
    [DecidableEq D] {c : A → C} {c' : B → C} {c'' : D → C} {d : C} (e : A ≃ B) (f : B ≃ D)
    (h₁ : ∀ a, c' (e a) = c a) (h₂ : ∀ b, c'' (f b) = c' b) (h₃ : ∀ a, c'' ((e.trans f) a) = c a)
    (x : P A c d) : map (e.trans f) h₃ x = map f h₂ (map e h₁ x)
  /-- The identity operation of each color. -/
  one (c : C) : P Unit (fun _ => c) c
  /-- **Partial composition**: insert an operation with output color `d'` at an input `i` of that
  color. -/
  comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] {cA : A → C}
    {cB : B → C} {d d' : C} (i : A) (h : d' = cA i) :
    P A cA d →ₗ[R] P B cB d' →ₗ[R] P (Without A i ⊕ B) (compColor cA i cB) d
  /-- **Equivariance**: composition is natural in bijections of both input sets. -/
  map_comp {A A' B B' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] {cA : A → C} {cA' : A' → C}
    {cB : B → C} {cB' : B' → C} {d d' : C} (σ : A ≃ A') (τ : B ≃ B') (i : A)
    (hσ : ∀ a, cA' (σ a) = cA a) (hτ : ∀ b, cB' (τ b) = cB b) (h : d' = cA i)
    (h' : d' = cA' (σ i))
    (hc : ∀ z, compColor cA' (σ i) cB' (compEquiv σ τ i z) = compColor cA i cB z)
    (x : P A cA d) (y : P B cB d') :
    map (compEquiv σ τ i) hc (comp i h x y) = comp (σ i) h' (map σ hσ x) (map τ hτ y)
  /-- The right unit law. -/
  comp_one {A : Type} [Fintype A] [DecidableEq A] {cA : A → C} {d : C} (i : A)
    (hc : ∀ z, cA (rightUnitEquiv i z) = compColor cA i (fun _ => cA i) z) (x : P A cA d) :
    map (rightUnitEquiv i) hc (comp i rfl x (one (cA i))) = x
  /-- The left unit law. -/
  one_comp {B : Type} [Fintype B] [DecidableEq B] {cB : B → C} {d : C}
    (hc : ∀ z, cB (leftUnitEquiv B z) = compColor (fun _ : Unit => d) () cB z) (y : P B cB d) :
    map (leftUnitEquiv B) hc (comp () rfl (one d) y) = y
  /-- Sequential associativity. -/
  comp_assoc_seq {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] {cA : A → C} {cB : B → C} {cD : D → C} {dA dB dD : C} (i : A)
    (j : B) (h₁ : dB = cA i) (h₂ : dD = cB j)
    (hc : ∀ z, compColor cA i (compColor cB j cD) (seqEquiv i j D z)
      = compColor (compColor cA i cB) (Sum.inr j) cD z)
    (x : P A cA dA) (y : P B cB dB) (z : P D cD dD) :
    map (seqEquiv i j D) hc (comp (Sum.inr j) h₂ (comp i h₁ x y) z)
      = comp i h₁ x (comp j h₂ y z)
  /-- Parallel associativity. -/
  comp_assoc_par {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] {cA : A → C} {cB : B → C} {cD : D → C} {dA dB dD : C} {i k : A}
    (hik : i ≠ k) (h₁ : dB = cA i) (h₂ : dD = cA k)
    (hc : ∀ z, compColor (compColor cA k cD) (Sum.inl ⟨i, hik⟩) cB (parEquiv hik B D z)
      = compColor (compColor cA i cB) (Sum.inl ⟨k, Ne.symm hik⟩) cD z)
    (x : P A cA dA) (y : P B cB dB) (z : P D cD dD) :
    map (parEquiv hik B D) hc (comp (Sum.inl ⟨k, Ne.symm hik⟩) h₂ (comp i h₁ x y) z)
      = comp (Sum.inl ⟨i, hik⟩) h₁ (comp k h₂ x z) y

/-- **A morphism of colored operads**: a family of linear maps commuting with relabelling,
preserving the units and the compositions. -/
structure ColOperadHom (R : Type u) [CommRing R] (C : Type w)
    (P : (A : Type) → [Fintype A] → [DecidableEq A] → (A → C) → C → Type v)
    (Q : (A : Type) → [Fintype A] → [DecidableEq A] → (A → C) → C → Type x)
    [∀ (A : Type) [Fintype A] [DecidableEq A] (c : A → C) (d : C), AddCommGroup (P A c d)]
    [∀ (A : Type) [Fintype A] [DecidableEq A] (c : A → C) (d : C), Module R (P A c d)]
    [∀ (A : Type) [Fintype A] [DecidableEq A] (c : A → C) (d : C), AddCommGroup (Q A c d)]
    [∀ (A : Type) [Fintype A] [DecidableEq A] (c : A → C) (d : C), Module R (Q A c d)]
    [ColOperad R C P] [ColOperad R C Q] where
  /-- The component at colored inputs and an output color. -/
  app (A : Type) [Fintype A] [DecidableEq A] (c : A → C) (d : C) : P A c d →ₗ[R] Q A c d
  /-- Components commute with relabelling. -/
  app_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] {c : A → C}
    {c' : B → C} {d : C} (e : A ≃ B) (h : ∀ a, c' (e a) = c a) (x : P A c d) :
    app B c' d (ColOperad.map (R := R) e h x) = ColOperad.map (R := R) e h (app A c d x)
  /-- The units go to the units. -/
  app_one (c : C) : app Unit (fun _ => c) c (ColOperad.one R c) = ColOperad.one R c
  /-- Compositions go to compositions. -/
  app_comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] {cA : A → C}
    {cB : B → C} {d d' : C} (i : A) (h : d' = cA i) (x : P A cA d) (y : P B cB d') :
    app (Without A i ⊕ B) (compColor cA i cB) d (ColOperad.comp (R := R) i h x y)
      = ColOperad.comp (R := R) i h (app A cA d x) (app B cB d' y)

/-! ## Operads as one-colored operads -/

/-- **The one-colored species of a species.** -/
@[nolint unusedArguments]
def OneCol (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v) :
    (A : Type) → [Fintype A] → [DecidableEq A] → (A → Unit) → Unit → Type v :=
  fun A _ _ _ _ => P A

section OneCol

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)]

instance OneCol.instAddCommGroup (A : Type) [Fintype A] [DecidableEq A] (c : A → Unit)
    (d : Unit) : AddCommGroup (OneCol P A c d) :=
  inferInstanceAs (AddCommGroup (P A))

instance OneCol.instModule (A : Type) [Fintype A] [DecidableEq A] (c : A → Unit) (d : Unit) :
    Module R (OneCol P A c d) :=
  inferInstanceAs (Module R (P A))

variable [SymOperad R P]

/-- **An operad is a one-colored operad.** -/
noncomputable instance SymOperad.toCol : ColOperad R Unit (OneCol P) where
  map e _ := SymOperad.map (R := R) (P := P) e
  map_refl _ x := SymOperad.map_refl (R := R) (P := P) x
  map_trans e f _ _ _ x := SymOperad.map_trans (R := R) (P := P) e f x
  one _ := SymOperad.one R
  comp i _ := SymOperad.comp (R := R) (P := P) i
  map_comp σ τ i _ _ _ _ _ x y := SymOperad.map_comp (R := R) (P := P) σ τ i x y
  comp_one i _ x := SymOperad.comp_one (R := R) (P := P) i x
  one_comp _ y := SymOperad.one_comp (R := R) (P := P) y
  comp_assoc_seq i j _ _ _ x y z := SymOperad.comp_assoc_seq (R := R) (P := P) i j x y z
  comp_assoc_par hik _ _ _ x y z := SymOperad.comp_assoc_par (R := R) (P := P) hik x y z

end OneCol

/-! ## Morphisms of one-colored operads -/

section OneColHom

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type x}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]

/-- **Morphisms of one-colored operads are morphisms of operads.** -/
def SymOperad.colHomEquiv : ColOperadHom R Unit (OneCol P) (OneCol Q) ≃ SymOperadHom R P Q where
  toFun φ :=
    { app A _ _ := φ.app A (fun _ => ()) ()
      app_map e x := φ.app_map e (fun _ => rfl) x
      app_one := φ.app_one ()
      app_comp i x y := φ.app_comp i rfl x y }
  invFun f :=
    { app A _ _ _ _ := f.app A
      app_map e _ x := f.app_map e x
      app_one _ := f.app_one
      app_comp i _ x y := f.app_comp i x y }
  left_inv φ := by
    obtain ⟨app, h1, h2, h3⟩ := φ
    congr
  right_inv _ := rfl

end OneColHom

/-! ## The endomorphism colored operad -/

section ColEnd

variable {R : Type u} [CommRing R] {C : Type w} {V : C → Type v} [∀ c, AddCommGroup (V c)]
  [∀ c, Module R (V c)]

variable (R V) in
/-- Transport along an equality of colors. -/
def castV : ∀ {c c' : C}, c = c' → V c →ₗ[R] V c'
  | _, _, rfl => LinearMap.id

@[simp] lemma castV_self {c : C} (h : c = c) (x : V c) : castV R V h x = x := rfl

lemma castV_castV {c c' c'' : C} (h : c = c') (h' : c' = c'') (x : V c) :
    castV R V h' (castV R V h x) = castV R V (h.trans h') x := by
  subst h
  subst h'
  rfl

variable (R V) in
/-- **The endomorphism colored operad** of a family of modules: the multilinear maps
`∏ₐ V (c a) → V d`. -/
@[nolint unusedArguments]
abbrev ColEnd (A : Type) [Fintype A] [DecidableEq A] (c : A → C) (d : C) : Type _ :=
  MultilinearMap R (fun a => V (c a)) (V d)

section Feed

variable {A B : Type} [DecidableEq A] {cA : A → C} {cB : B → C} {d' : C}

variable (R) in
/-- Feed `w`, of the color of the input `i`, into that input, the other inputs read off `v`. -/
def cfeed (i : A) (h : d' = cA i) (v : ∀ z : Without A i ⊕ B, V (compColor cA i cB z))
    (w : V d') : ∀ a, V (cA a) :=
  fun a => if ha : a = i then castV R V (h.trans (congrArg cA ha.symm)) w
    else v (Sum.inl ⟨a, ha⟩)

lemma cfeed_self (i : A) (h : d' = cA i) (v : ∀ z : Without A i ⊕ B, V (compColor cA i cB z))
    (w : V d') : cfeed R i h v w i = castV R V h w :=
  dif_pos rfl

lemma cfeed_of_ne {i a : A} (ha : a ≠ i) (h : d' = cA i)
    (v : ∀ z : Without A i ⊕ B, V (compColor cA i cB z)) (w : V d') :
    cfeed R i h v w a = v (Sum.inl ⟨a, ha⟩) :=
  dif_neg ha

variable [DecidableEq B]

lemma cfeed_update_inl (i : A) (h : d' = cA i)
    (v : ∀ z : Without A i ⊕ B, V (compColor cA i cB z)) (w : V d') (a₀ : Without A i)
    (z : V (cA a₀.1)) :
    cfeed R i h (Function.update v (Sum.inl a₀) z) w
      = Function.update (cfeed R i h v w) a₀.1 z := by
  funext a
  by_cases ha : a = i
  · subst ha
    rw [cfeed_self, Function.update_of_ne (Ne.symm a₀.2), cfeed_self]
  · rw [cfeed_of_ne ha]
    by_cases ha₀ : a = a₀.1
    · subst ha₀
      rw [Function.update_self]
      exact (Function.update_self a₀.1 z (cfeed R i h v w)).symm
    · rw [Function.update_of_ne (fun e => ha₀ (congrArg Subtype.val (Sum.inl_injective e))),
        Function.update_of_ne ha₀, cfeed_of_ne ha]

lemma cfeed_update_inr (i : A) (h : d' = cA i)
    (v : ∀ z : Without A i ⊕ B, V (compColor cA i cB z)) (w : V d') (b : B) (z : V (cB b)) :
    cfeed R i h (Function.update v (Sum.inr b) z) w = cfeed R i h v w := by
  funext a
  by_cases ha : a = i
  · subst ha
    rw [cfeed_self, cfeed_self]
  · rw [cfeed_of_ne ha, cfeed_of_ne ha, Function.update_of_ne Sum.inl_ne_inr]

omit [DecidableEq B] in
lemma cfeed_eq_update (i : A) (h : d' = cA i)
    (v : ∀ z : Without A i ⊕ B, V (compColor cA i cB z)) (w : V d') :
    cfeed R i h v w = Function.update (cfeed R i h v 0) i (castV R V h w) := by
  funext a
  by_cases ha : a = i
  · subst ha
    rw [Function.update_self, cfeed_self]
  · rw [Function.update_of_ne ha, cfeed_of_ne ha, cfeed_of_ne ha]

end Feed

variable {A A' B B' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']

omit [Fintype A] [Fintype B] in
lemma castV_update_comp {c : A → C} {c' : B → C} (e : A ≃ B) (hc : ∀ a, c' (e a) = c a)
    (v : ∀ b, V (c' b)) (a₀ : A) (z : V (c' (e a₀))) :
    (fun a => castV R V (hc a) (Function.update v (e a₀) z (e a)))
      = Function.update (fun a => castV R V (hc a) (v (e a))) a₀ (castV R V (hc a₀) z) := by
  funext a
  by_cases ha : a = a₀
  · subst ha
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne (e.injective.ne ha), Function.update_of_ne ha]

variable (R V) in
/-- Relabelling in the endomorphism colored operad, transporting the colors. -/
def ColEnd.map {c : A → C} {c' : B → C} {d : C} (e : A ≃ B) (hc : ∀ a, c' (e a) = c a) :
    ColEnd R V A c d →ₗ[R] ColEnd R V B c' d where
  toFun f := MultilinearMap.mk' (fun v => f fun a => castV R V (hc a) (v (e a)))
    (fun v b x y => by
      obtain ⟨a₀, rfl⟩ := e.surjective b
      simp only [castV_update_comp, map_add, f.map_update_add])
    (fun v b r x => by
      obtain ⟨a₀, rfl⟩ := e.surjective b
      simp only [castV_update_comp, map_smul, f.map_update_smul])
  map_add' _ _ := MultilinearMap.ext fun _ => rfl
  map_smul' _ _ := MultilinearMap.ext fun _ => rfl

@[simp] lemma ColEnd.map_apply {c : A → C} {c' : B → C} {d : C} (e : A ≃ B)
    (hc : ∀ a, c' (e a) = c a) (f : ColEnd R V A c d) (v : ∀ b, V (c' b)) :
    ColEnd.map R V e hc f v = f fun a => castV R V (hc a) (v (e a)) :=
  rfl

omit [Fintype A] [Fintype B] [∀ c, AddCommGroup (V c)] in
private lemma inr_update_inl' {cA : A → C} {cB : B → C} {i : A}
    (v : ∀ z : Without A i ⊕ B, V (compColor cA i cB z)) (a : Without A i) (z : V (cA a.1)) :
    (fun b => Function.update v (Sum.inl a) z (Sum.inr b)) = fun b => v (Sum.inr b) :=
  funext fun _ => Function.update_of_ne Sum.inr_ne_inl _ _

omit [Fintype A] [Fintype B] [∀ c, AddCommGroup (V c)] in
private lemma inr_update_inr' {cA : A → C} {cB : B → C} {i : A}
    (v : ∀ z : Without A i ⊕ B, V (compColor cA i cB z)) (b : B) (z : V (cB b)) :
    (fun b' => Function.update v (Sum.inr b) z (Sum.inr b') : ∀ b', V (cB b'))
      = Function.update (fun b' => v (Sum.inr b') : ∀ b', V (cB b')) b z :=
  Function.update_comp_eq_of_injective' v Sum.inr_injective b z

variable (R V) in
/-- **Feed `g` into the input `i` of `f`.** -/
def ColEnd.compML {cA : A → C} {cB : B → C} {d d' : C} (i : A) (h : d' = cA i)
    (f : ColEnd R V A cA d) (g : ColEnd R V B cB d') :
    ColEnd R V (Without A i ⊕ B) (compColor cA i cB) d :=
  MultilinearMap.mk' (fun v => f (cfeed R i h v (g fun b => v (Sum.inr b))))
    (fun v z x y => by
      rcases z with a | b
      · simp only [inr_update_inl', cfeed_update_inl]
        exact f.map_update_add _ _ _ _
      · simp only [inr_update_inr', cfeed_update_inr]
        erw [g.map_update_add]
        rw [cfeed_eq_update, map_add, f.map_update_add, ← cfeed_eq_update, ← cfeed_eq_update]
        rfl)
    (fun v z r x => by
      rcases z with a | b
      · simp only [inr_update_inl', cfeed_update_inl]
        exact f.map_update_smul _ _ _ _
      · simp only [inr_update_inr', cfeed_update_inr]
        erw [g.map_update_smul]
        rw [cfeed_eq_update, map_smul, f.map_update_smul, ← cfeed_eq_update]
        rfl)

@[simp] lemma ColEnd.compML_apply {cA : A → C} {cB : B → C} {d d' : C} (i : A) (h : d' = cA i)
    (f : ColEnd R V A cA d) (g : ColEnd R V B cB d')
    (v : ∀ z : Without A i ⊕ B, V (compColor cA i cB z)) :
    ColEnd.compML R V i h f g v = f (cfeed R i h v (g fun b => v (Sum.inr b))) :=
  rfl

variable (R V) in
/-- Composition, bilinearly. -/
def ColEnd.compL {cA : A → C} {cB : B → C} {d d' : C} (i : A) (h : d' = cA i) :
    ColEnd R V A cA d →ₗ[R] ColEnd R V B cB d' →ₗ[R]
      ColEnd R V (Without A i ⊕ B) (compColor cA i cB) d :=
  LinearMap.mk₂ R (ColEnd.compML R V i h)
    (fun _ _ _ => MultilinearMap.ext fun _ => rfl)
    (fun _ _ _ => MultilinearMap.ext fun _ => rfl)
    (fun f g g' => MultilinearMap.ext fun v => by
      simp only [ColEnd.compML_apply, MultilinearMap.add_apply]
      rw [cfeed_eq_update, map_add, f.map_update_add, ← cfeed_eq_update, ← cfeed_eq_update])
    (fun r f g => MultilinearMap.ext fun v => by
      simp only [ColEnd.compML_apply, MultilinearMap.smul_apply]
      rw [cfeed_eq_update, map_smul, f.map_update_smul, ← cfeed_eq_update])

variable (R V) in
/-- The unit of each color: the identity. -/
def ColEnd.one (c : C) : ColEnd R V Unit (fun _ => c) c :=
  MultilinearMap.ofSubsingleton R (V c) (V c) () LinearMap.id

@[simp] lemma ColEnd.one_apply (c : C) (v : Unit → V c) : ColEnd.one R V c v = v () := rfl


/-- **The endomorphism colored operad** of a family of modules. -/
noncomputable instance ColEnd.instColOperad : ColOperad R C (ColEnd R V) where
  map e hc := ColEnd.map R V e hc
  map_refl _ _ := MultilinearMap.ext fun _ => rfl
  map_trans e f h₁ h₂ h₃ g := MultilinearMap.ext fun v => by
    simp only [ColEnd.map_apply, castV_castV]
    rfl
  one c := ColEnd.one R V c
  comp i h := ColEnd.compL R V i h
  map_comp σ τ i hσ hτ h h' hc f g := MultilinearMap.ext fun v => by
    show ColEnd.compML R V i h f g _ = ColEnd.compML R V (σ i) h' (ColEnd.map R V σ hσ f)
      (ColEnd.map R V τ hτ g) v
    simp only [ColEnd.compML_apply, ColEnd.map_apply]
    congr 1
    funext a
    by_cases ha : a = i
    · subst ha
      rw [cfeed_self, cfeed_self, castV_castV]
      rfl
    · rw [cfeed_of_ne ha, cfeed_of_ne (σ.injective.ne ha)]
      rfl
  comp_one i hc f := MultilinearMap.ext fun v => by
    show ColEnd.compML R V i rfl f (ColEnd.one R V _) _ = f v
    simp only [ColEnd.compML_apply, ColEnd.one_apply]
    congr 1
    funext a
    by_cases ha : a = i
    · subst ha
      rw [cfeed_self]
      rfl
    · rw [cfeed_of_ne ha]
      rfl
  one_comp hc g := MultilinearMap.ext fun v => by
    show ColEnd.map R V (leftUnitEquiv _) hc (ColEnd.compML R V () _ (ColEnd.one R V _) g) v = g v
    rw [ColEnd.map_apply, ColEnd.compML_apply, ColEnd.one_apply, cfeed_self]
    rfl
  comp_assoc_seq i j h₁ h₂ hc f g k := MultilinearMap.ext fun v => by
    show ColEnd.compML R V (Sum.inr j) h₂ (ColEnd.compML R V i h₁ f g) k _
      = ColEnd.compML R V i h₁ f (ColEnd.compML R V j h₂ g k) v
    simp only [ColEnd.compML_apply]
    congr 1
    funext a
    by_cases ha : a = i
    · subst ha
      rw [cfeed_self, cfeed_self]
      congr 2
      funext b
      by_cases hb : b = j
      · subst hb
        rw [cfeed_self, cfeed_self]
        rfl
      · rw [cfeed_of_ne (show (Sum.inr b : Without _ a ⊕ _) ≠ Sum.inr j from
          fun e => hb (Sum.inr_injective e)), cfeed_of_ne hb]
        rfl
    · rw [cfeed_of_ne ha, cfeed_of_ne (show (Sum.inl ⟨a, ha⟩ : Without _ i ⊕ _) ≠ Sum.inr j from
        Sum.inl_ne_inr), cfeed_of_ne ha]
      rfl
  comp_assoc_par hik h₁ h₂ hc f g k := MultilinearMap.ext fun v => by
    show ColEnd.compML R V (Sum.inl ⟨_, Ne.symm hik⟩) h₂ (ColEnd.compML R V _ h₁ f g) k _
      = ColEnd.compML R V (Sum.inl ⟨_, hik⟩) h₁ (ColEnd.compML R V _ h₂ f k) g v
    simp only [ColEnd.compML_apply]
    congr 1
    funext a
    rename_i i₀ k₀
    by_cases hai : a = i₀
    · subst hai
      rw [cfeed_self, cfeed_of_ne hik, cfeed_self]
      congr 2
    · by_cases hak : a = k₀
      · subst hak
        rw [cfeed_of_ne hai, cfeed_self, cfeed_self]
        congr 2
      · rw [cfeed_of_ne hai, cfeed_of_ne hak,
          cfeed_of_ne (show (Sum.inl ⟨a, hai⟩ : Without _ i₀ ⊕ _) ≠ Sum.inl ⟨k₀, Ne.symm hik⟩ from
            fun e => hak (congrArg Subtype.val (Sum.inl_injective e))),
          cfeed_of_ne (show (Sum.inl ⟨a, hak⟩ : Without _ k₀ ⊕ _) ≠ Sum.inl ⟨i₀, hik⟩ from
            fun e => hai (congrArg Subtype.val (Sum.inl_injective e)))]
        rfl

variable (R V) in
/-- **An algebra over a colored operad** on a family of modules: a morphism into the endomorphism
colored operad. -/
abbrev ColAlgebra (P : (A : Type) → [Fintype A] → [DecidableEq A] → (A → C) → C → Type x)
    [∀ (A : Type) [Fintype A] [DecidableEq A] (c : A → C) (d : C), AddCommGroup (P A c d)]
    [∀ (A : Type) [Fintype A] [DecidableEq A] (c : A → C) (d : C), Module R (P A c d)]
    [ColOperad R C P] :=
  ColOperadHom R C P (ColEnd R V)

end ColEnd

/-! ## Algebras over one-colored operads -/

section OneColAlg

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]
  {V : Type w} [AddCommGroup V] [Module R V]

/-- **Algebras over the one-colored operad of an operad are its algebras.** -/
def SymOperad.colAlgebraEquiv :
    ColAlgebra R (fun _ : Unit => V) (OneCol P) ≃ SymAlgebra R P V where
  toFun φ :=
    { app A _ _ := φ.app A (fun _ => ()) ()
      app_map e x := by
        have := φ.app_map (c := fun _ => ()) (c' := fun _ => ()) (d := ()) e (fun _ => rfl) x
        exact this
      app_one := φ.app_one ()
      app_comp i x y := by
        have := φ.app_comp (cA := fun _ => ()) (cB := fun _ => ()) (d := ()) (d' := ()) i rfl x y
        refine this.trans (MultilinearMap.ext fun v => ?_)
        show ColEnd.compML R (fun _ : Unit => V) i rfl _ _ v = EndOp.compML R V i _ _ v
        simp only [ColEnd.compML_apply, EndOp.compML_apply]
        congr 1 }
  invFun f :=
    { app A _ _ _ _ := f.app A
      app_map e _ x := f.app_map e x
      app_one _ := f.app_one
      app_comp i _ x y := by
        refine (f.app_comp i x y).trans (MultilinearMap.ext fun v => ?_)
        show EndOp.compML R V i _ _ v = _
        simp only [EndOp.compML_apply]
        congr 1 }
  left_inv φ := by
    obtain ⟨app, h1, h2, h3⟩ := φ
    congr
  right_inv _ := rfl

end OneColAlg

end Operad
