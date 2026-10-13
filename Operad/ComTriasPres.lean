/-
# The presentation of `ComTrias`

Vallette's operad of commutative trialgebras is the linearization of the set operad of nonempty
subsets (`ComTrias R = Lin R NonemptySubset`). This file proves that the set operad is presented by
two binary operations, `⊥` commutative and `⊣`, and the relations of commutative trialgebras

  `(x ⊥ y) ⊥ z = x ⊥ (y ⊥ z)`, `(x ⊣ y) ⊣ z = x ⊣ (y ⊣ z) = x ⊣ (z ⊣ y)`,
  `x ⊣ (y ⊥ z) = x ⊣ (y ⊣ z)`, `(x ⊥ y) ⊣ z = x ⊥ (y ⊣ z)`

(`NonemptySubset.presIso`), and that a morphism out of it is such a pair (`NonemptySubset.homEquiv`,
and `ComTrias.homEquiv` into operads in modules).

The content is the universal property (`ComTriasData.lift`): in any set operad, a commutative
associative `⊥` and a `⊣` satisfying the relations define a morphism out of the nonempty subsets,
sending `S ⊊ A` to `⊣(⊥_S, ⊥_{A ∖ S})` and `A` to `⊥_A`, where `⊥_X` is the product of the inputs
`X` (generalized associativity and commutativity, `Operad.ComSet`). That this is a morphism is a
normal-form statement: every composite of `⊥` and `⊣` equals the normal form with the same set of
marked inputs. Its proof rests on one absorption identity, `⊣(X, y) = ⊣(X, ⊥_B)` for `y` a normal
form on `B` (`ComTriasData.bin_left_psi`).
-/
import Operad.SetHadamard
import Operad.ComSet

set_option synthInstance.maxSize 1024

namespace Operad

open Sym SetOperad

namespace NonemptySubset

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

@[ext] lemma ext {s t : NonemptySubset A} (h : ∀ a, s.1 a = t.1 a) : s = t :=
  Subtype.ext (funext h)

lemma map_val {A' : Type} [Fintype A'] [DecidableEq A'] (e : A ≃ A') (s : NonemptySubset A) :
    (SetOperad.map e s).1 = s.1 ∘ e.symm := rfl

lemma comp_val (i : A) (s : NonemptySubset A) (t : NonemptySubset B) :
    (SetOperad.comp i s t).1 = compFun i s.1 t.1 := rfl

end NonemptySubset

/-! ## Generators and relations -/

/-- The generators: `x ⊥ y`, commutative, and `x ⊣ y`. -/
inductive ComTriasGen : ℕ → Type
  | mid : ComTriasGen 2
  | left : ComTriasGen 2

open Syn in
/-- **The relations of commutative trialgebras** (Vallette): `⊥` is commutative and associative,
`(x ⊣ y) ⊣ z = x ⊣ (y ⊣ z) = x ⊣ (z ⊣ y)`, `x ⊣ (y ⊥ z) = x ⊣ (y ⊣ z)`,
`(x ⊥ y) ⊣ z = x ⊥ (y ⊣ z)`. -/
inductive ComTriasRel : ∀ {A : Type} [Fintype A] [DecidableEq A],
    Syn ComTriasGen A → Syn ComTriasGen A → Prop
  | comm : ComTriasRel (.map (Equiv.swap 0 1) (.gen .mid)) (.gen .mid)
  | assoc : ComTriasRel
      (.map (Equiv.sumAssoc Unit Unit Unit) (bin (.gen .mid) (bin (.gen .mid) .one .one) .one))
      (bin (.gen .mid) .one (bin (.gen .mid) .one .one))
  | lassoc : ComTriasRel
      (.map (Equiv.sumAssoc Unit Unit Unit) (bin (.gen .left) (bin (.gen .left) .one .one) .one))
      (bin (.gen .left) .one (bin (.gen .left) .one .one))
  | lperm : ComTriasRel (bin (.gen .left) .one (bin (.gen .left) .one .one))
      (bin (.gen .left) .one (bin (.map (Equiv.swap 0 1) (.gen .left)) .one .one))
  | lmid : ComTriasRel (bin (.gen .left) .one (bin (.gen .mid) .one .one))
      (bin (.gen .left) .one (bin (.gen .left) .one .one))
  | midl : ComTriasRel
      (.map (Equiv.sumAssoc Unit Unit Unit) (bin (.gen .left) (bin (.gen .mid) .one .one) .one))
      (bin (.gen .mid) .one (bin (.gen .left) .one .one))

/-- **Values of `⊥` and `⊣` satisfying the relations of commutative trialgebras**, in a set
operad. -/
structure ComTriasData (S : (A : Type) → [Fintype A] → [DecidableEq A] → Type*) [SetOperad S] where
  /-- The value of `⊥`. -/
  mid : S (Fin 2)
  /-- The value of `⊣`. -/
  left : S (Fin 2)
  comm : IsComm mid
  assoc : IsAssoc mid
  lassoc : map (Equiv.sumAssoc Unit Unit Unit) (bin left (bin left one one) one)
    = bin left one (bin left one one)
  lperm : bin left one (bin left one one) = bin left one (bin (map (Equiv.swap 0 1) left) one one)
  lmid : bin left one (bin mid one one) = bin left one (bin left one one)
  midl : map (Equiv.sumAssoc Unit Unit Unit) (bin left (bin mid one one) one)
    = bin mid one (bin left one one)

/-- Generator values respect the relations exactly when they form a `ComTriasData`. -/
lemma respects_iff {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type*} [SetOperad S]
    (f : ∀ n, ComTriasGen n → S (Fin n)) :
    Pres.Respects ComTriasRel f ↔
      IsComm (f 2 .mid) ∧ IsAssoc (f 2 .mid)
        ∧ map (Equiv.sumAssoc Unit Unit Unit) (bin (f 2 .left) (bin (f 2 .left) one one) one)
          = bin (f 2 .left) one (bin (f 2 .left) one one)
        ∧ bin (f 2 .left) one (bin (f 2 .left) one one)
          = bin (f 2 .left) one (bin (map (Equiv.swap 0 1) (f 2 .left)) one one)
        ∧ bin (f 2 .left) one (bin (f 2 .mid) one one)
          = bin (f 2 .left) one (bin (f 2 .left) one one)
        ∧ map (Equiv.sumAssoc Unit Unit Unit) (bin (f 2 .left) (bin (f 2 .mid) one one) one)
          = bin (f 2 .mid) one (bin (f 2 .left) one one) := by
  constructor
  · intro h
    exact ⟨h _ _ .comm, h _ _ .assoc, h _ _ .lassoc, h _ _ .lperm, h _ _ .lmid, h _ _ .midl⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩ A _ _ x y hxy
    cases hxy with
    | comm => exact h0
    | assoc => exact h1
    | lassoc => exact h2
    | lperm => exact h3
    | lmid => exact h4
    | midl => exact h5

namespace ComTriasData

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type*} [SetOperad S] (D : ComTriasData S)
  {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C]
  [DecidableEq C]

/-! ### The relators, generically -/

lemma lassoc_eq {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (x : S A) (y : S B) (z : S C) :
    bin D.left (bin D.left x y) z
      = map (Equiv.sumAssoc A B C).symm (bin D.left x (bin D.left y z)) :=
  eq_map_symm_of_map_eq (bin_assoc_of D.lassoc x y z)

lemma lmid_eq {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (x : S A) (y : S B) (z : S C) :
    bin D.left x (bin D.mid y z) = bin D.left x (bin D.left y z) :=
  bin_right_of D.lmid x y z

lemma midl_eq {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (x : S A) (y : S B) (z : S C) :
    bin D.mid x (bin D.left y z) = map (Equiv.sumAssoc A B C) (bin D.left (bin D.mid x y) z) :=
  (bin_assoc_of D.midl x y z).symm

/-- The `μ`-product of the inputs. -/
local notation "𝐏" => prod D.comm D.assoc

/-! ### The normal forms -/

lemma nonempty_of_tri (s : NonemptySubset A) : Nonempty A := let ⟨a, _⟩ := s.2; ⟨a⟩

lemma nonempty_true (s : NonemptySubset A) : Nonempty {a // s.1 a = true} := let ⟨a,
    ha⟩ := s.2; ⟨⟨a, ha⟩⟩

lemma nonempty_false {s : NonemptySubset A} (h : ¬ ∀ a,
    s.1 a = true) : Nonempty {a // ¬ s.1 a = true} :=
  let ⟨a, ha⟩ := not_forall.mp h; ⟨⟨a, ha⟩⟩

/-- **The normal form** of a nonempty subset `s` of `A`: `μ_A` if `s = A`, and otherwise
`ν(μ_s, μ_{A ∖ s})`. -/
def psi (A : Type) [Fintype A] [DecidableEq A] (s : NonemptySubset A) : S A :=
  if h : ∀ a, s.1 a = true then 𝐏 A (nonempty_of_tri s)
  else map (Equiv.sumCompl fun a => s.1 a = true)
    (bin D.left (𝐏 {a // s.1 a = true} (nonempty_true s))
      (𝐏 {a // ¬ s.1 a = true} (nonempty_false h)))

lemma psi_of_not_all (s : NonemptySubset A) (h : ¬ ∀ a, s.1 a = true) :
    D.psi A s = map (Equiv.sumCompl fun a => s.1 a = true)
      (bin D.left (𝐏 {a // s.1 a = true} (nonempty_true s))
        (𝐏 {a // ¬ s.1 a = true} (nonempty_false h))) := by
  rw [psi, dif_neg h]

lemma psi_of_all (s : NonemptySubset A) (h : ∀ a, s.1 a = true) (hA : Nonempty A) :
    D.psi A s = 𝐏 A hA := by
  rw [psi, dif_pos h]

/-- **The normal form of a full subset**, along any relabelling. -/
lemma psi_of_all' {X : Type} [Fintype X] [DecidableEq X] (s : NonemptySubset A) (h : ∀ a,
    s.1 a = true)
    (hX : Nonempty X) (E : X ≃ A) : D.psi A s = map E (𝐏 X hX) := by
  rw [psi_of_all D s h (hX.map E), SetOperad.map_prod]

/-- **The normal form of a proper subset**, along any decomposition of the inputs into the
subset and its complement. -/
theorem psi_eq {P N : Type} [Fintype P] [DecidableEq P] [Fintype N] [DecidableEq N]
    (s : NonemptySubset A) (hP : Nonempty P) (hN : Nonempty N) (E : P ⊕ N ≃ A)
    (hEP : ∀ p, s.1 (E (Sum.inl p)) = true) (hEN : ∀ n, s.1 (E (Sum.inr n)) = false) :
    D.psi A s = map E (bin D.left (𝐏 P hP) (𝐏 N hN)) := by
  have h : ¬ ∀ a, s.1 a = true := by
    obtain ⟨n⟩ := hN
    intro h
    have := hEN n
    rw [h] at this
    exact Bool.noConfusion this
  let σ : P ≃ {a // s.1 a = true} := Equiv.ofBijective (fun p => ⟨E (Sum.inl p), hEP p⟩)
    ⟨fun p q hpq => Sum.inl_injective (E.injective (congrArg Subtype.val hpq)), fun ⟨a, ha⟩ => by
      rcases hx : E.symm a with p | n
      · exact ⟨p, Subtype.ext (show E (Sum.inl p) = a by rw [← hx, Equiv.apply_symm_apply])⟩
      · have := hEN n
        rw [← hx, Equiv.apply_symm_apply, ha] at this
        exact Bool.noConfusion this⟩
  let τ : N ≃ {a // ¬ s.1 a = true} := Equiv.ofBijective
    (fun n => ⟨E (Sum.inr n), by rw [hEN n]; exact Bool.false_ne_true⟩)
    ⟨fun p q hpq => Sum.inr_injective (E.injective (congrArg Subtype.val hpq)), fun ⟨a, ha⟩ => by
      rcases hx : E.symm a with p | n
      · have := hEP p
        rw [← hx, Equiv.apply_symm_apply] at this
        exact absurd this ha
      · exact ⟨n, Subtype.ext (show E (Sum.inr n) = a by rw [← hx, Equiv.apply_symm_apply])⟩⟩
  rw [psi, dif_neg h, ← SetOperad.map_prod hP σ, ← SetOperad.map_prod hN τ, bin_map, map_map]
  exact map_congr (fun c => by rcases c with p | n <;> rfl) _

/-- **The normal forms are invariant under relabelling.** -/
theorem psi_map {A' : Type} [Fintype A'] [DecidableEq A'] (e : A ≃ A') (s : NonemptySubset A) :
    D.psi A' (map e s) = map e (D.psi A s) := by
  by_cases h : ∀ a, s.1 a = true
  · obtain ⟨a, _⟩ := s.2
    rw [psi_of_all' D s h ⟨a⟩ (Equiv.refl A),
        psi_of_all' D (map e s) (fun a' => h (e.symm a')) ⟨a⟩ e,
      map_map]
    rfl
  · conv_rhs => rw [psi]
    rw [dif_neg h, map_map]
    refine psi_eq D _ _ _ _ (fun p => ?_) (fun n => ?_)
    · simp only [Equiv.trans_apply, Equiv.sumCompl_apply_inl, NonemptySubset.map_val,
        Function.comp_apply,
        Equiv.symm_apply_apply]
      exact p.2
    · simp only [Equiv.trans_apply, Equiv.sumCompl_apply_inr, NonemptySubset.map_val,
        Function.comp_apply,
        Equiv.symm_apply_apply]
      exact Bool.eq_false_iff.mpr n.2

/-! ### Composing into a product -/

/-- Composing into a product with more than one input. -/
lemma comp_prod_of_nonempty {W : Type} [Fintype W] [DecidableEq W] (hW : Nonempty W) (j : W)
    (h : Nonempty (Without W j)) (y : S B) :
    comp j (𝐏 W hW) y = bin D.mid (𝐏 (Without W j) h) y := by
  rw [← SetOperad.map_prod (h.map Sum.inl) (rightUnitEquiv j), ← bin_prod_one h,
    comp_map_left_of _ (i := Sum.inr ()) ?h1, comp_inr_bin, one_comp', bin_map_right, map_map,
    map_map]
  · exact map_eq_self (fun c => by rcases c with w | b <;> rfl) _
  · rfl

/-- Composing into a product with one input. -/
lemma comp_prod_of_isEmpty {W : Type} [Fintype W] [DecidableEq W] (hW : Nonempty W) (j : W)
    [IsEmpty (Without W j)] (y : S B) :
    comp j (𝐏 W hW) y = map (Equiv.emptySum (Without W j) B).symm y := by
  obtain ⟨e, he⟩ : ∃ e : Unit ≃ W, e () = j :=
    ⟨{ toFun := fun _ => j
       invFun := fun _ => ()
       left_inv := fun _ => rfl
       right_inv := fun w => by
         by_contra hne
         exact IsEmpty.false (⟨w, fun h => hne h.symm⟩ : Without W j) }, rfl⟩
  rw [← SetOperad.map_prod ⟨()⟩ e, prod_unit, comp_map_left_of _ (i := ()) he, one_comp', map_map]
  exact map_congr (fun b => by rfl) _

/-! ### Absorption -/

lemma lassoc_eq' (x : S A) (y : S B) (z : S C) :
    bin D.left x (bin D.left y z) = map (Equiv.sumAssoc A B C) (bin D.left (bin D.left x y) z) :=
  (bin_assoc_of D.lassoc x y z).symm

/-- **Absorption**: `ν(X, y) = ν(X, μ_B)` for `y` a normal form on `B`. -/
theorem bin_left_psi (X : S C) (t : NonemptySubset B) (hB : Nonempty B) :
    bin D.left X (D.psi B t) = bin D.left X (𝐏 B hB) := by
  by_cases h : ∀ b, t.1 b = true
  · rw [psi_of_all D t h hB]
  · rw [psi_of_not_all D t h, bin_map_right, ← D.lmid_eq,
      bin_prod' (nonempty_true t) (nonempty_false h),
      ← bin_map_right, SetOperad.map_prod]

/-- Absorption, below a `μ`. -/
theorem bin_left_mid_psi {W : Type} [Fintype W] [DecidableEq W] (X : S C) (hW : Nonempty W)
    (t : NonemptySubset B) (hB : Nonempty B) :
    bin D.left X (bin D.mid (𝐏 W hW) (D.psi B t)) = bin D.left X (𝐏 (W ⊕ B) (hW.map Sum.inl)) := by
  rw [D.lmid_eq, lassoc_eq', bin_left_psi D _ t hB, ← lassoc_eq', ← D.lmid_eq, bin_prod']

/-! ### The composition law -/

/-- **Normal forms compose to normal forms.** -/
theorem psi_comp (i : A) (s : NonemptySubset A) (t : NonemptySubset B) :
    D.psi (Without A i ⊕ B) (comp i s t) = comp i (D.psi A s) (D.psi B t) := by
  have hB : Nonempty B := nonempty_of_tri t
  by_cases hsi : s.1 i = true
  · by_cases hs : ∀ a, s.1 a = true
    · rw [psi_of_all D s hs ⟨i⟩]
      by_cases ht : ∀ b, t.1 b = true
      · -- `A ∘ᵢ B`: both full
        rw [psi_of_all D t ht hB, comp_prod]
        exact psi_of_all D _ (by rintro (a | b) <;> simp [NonemptySubset.comp_val,
            NonemptySubset.compFun, hs, ht]) _
      · rw [psi_of_not_all D t ht]
        by_cases hA' : Nonempty (Without A i)
        · rw [comp_prod_of_nonempty D ⟨i⟩ i hA', bin_map_right, D.midl_eq, bin_prod', map_map]
          refine psi_eq D _ _ _ _ (fun p => ?_) (fun n => ?_)
          · rcases p with a | b
            · simp [NonemptySubset.comp_val, NonemptySubset.compFun, hs]
            · simpa [NonemptySubset.comp_val, NonemptySubset.compFun, binLeftEquiv, binRightEquiv,
                hsi] using b.2
          · simpa [NonemptySubset.comp_val, NonemptySubset.compFun, binLeftEquiv, binRightEquiv,
              hsi] using n.2
        · haveI : IsEmpty (Without A i) := not_nonempty_iff.mp hA'
          rw [comp_prod_of_isEmpty D ⟨i⟩ i, map_map]
          refine psi_eq D _ _ _ _ (fun p => ?_) (fun n => ?_)
          · simpa [NonemptySubset.comp_val, NonemptySubset.compFun, binLeftEquiv, binRightEquiv,
              hsi] using p.2
          · simpa [NonemptySubset.comp_val, NonemptySubset.compFun, binLeftEquiv, binRightEquiv,
              hsi] using n.2
    · rw [psi_of_not_all D s hs, comp_map_left_of (Equiv.sumCompl fun a => s.1 a = true)
        (i := Sum.inl ⟨i, hsi⟩) (i' := i) rfl, comp_inl_bin]
      · by_cases ht : ∀ b, t.1 b = true
        · rw [psi_of_all D t ht hB, comp_prod, map_map]
          refine psi_eq D _ _ _ _ (fun p => ?_) (fun n => ?_)
          · rcases p with a | b
            · simpa [NonemptySubset.comp_val, NonemptySubset.compFun, binLeftEquiv,
                binRightEquiv] using a.1.2
            · exact (by simp [hsi, ht] : (s.1 i && t.1 b) = true)
          · simpa [NonemptySubset.comp_val, NonemptySubset.compFun, binLeftEquiv,
              binRightEquiv] using n.2
        · rw [psi_of_not_all D t ht]
          by_cases hT' : Nonempty (Without {a // s.1 a = true} ⟨i, hsi⟩)
          · rw [comp_prod_of_nonempty D _ _ hT', bin_map_right, D.midl_eq, bin_prod']
            simp only [map_map, bin_map_left]
            rw [D.lassoc_eq, ← D.lmid_eq, bin_prod']
            simp only [map_map]
            refine psi_eq D _ _ _ _ (fun p => ?_) (fun n => ?_)
            · rcases p with a | b
              · simpa [NonemptySubset.comp_val, NonemptySubset.compFun, binLeftEquiv,
                  binRightEquiv] using a.1.2
              · simpa [NonemptySubset.comp_val, NonemptySubset.compFun, binLeftEquiv,
                  binRightEquiv, hsi] using b.2
            · rcases n with n | n
              · simpa [NonemptySubset.comp_val, NonemptySubset.compFun, binLeftEquiv,
                  binRightEquiv, hsi] using n.2
              · simpa [NonemptySubset.comp_val, NonemptySubset.compFun, binLeftEquiv,
                  binRightEquiv] using n.2
          · haveI : IsEmpty (Without {a // s.1 a = true} ⟨i, hsi⟩) := not_nonempty_iff.mp hT'
            rw [comp_prod_of_isEmpty D _ _]
            simp only [map_map, bin_map_left]
            rw [D.lassoc_eq, ← D.lmid_eq, bin_prod']
            simp only [map_map]
            refine psi_eq D _ _ _ _ (fun p => ?_) (fun n => ?_)
            · simpa [NonemptySubset.comp_val, NonemptySubset.compFun, binLeftEquiv, binRightEquiv,
                hsi] using p.2
            · rcases n with n | n
              · simpa [NonemptySubset.comp_val, NonemptySubset.compFun, binLeftEquiv,
                  binRightEquiv, hsi] using n.2
              · simpa [NonemptySubset.comp_val, NonemptySubset.compFun, binLeftEquiv,
                  binRightEquiv] using n.2
  · have hs : ¬ ∀ a, s.1 a = true := fun h => hsi (h i)
    rw [psi_of_not_all D s hs, comp_map_left_of (Equiv.sumCompl fun a => s.1 a = true)
      (i := Sum.inr ⟨i, hsi⟩) (i' := i) rfl, comp_inr_bin]
    · by_cases hF' : Nonempty (Without {a // ¬ s.1 a = true} ⟨i, hsi⟩)
      · rw [comp_prod_of_nonempty D _ _ hF', bin_left_mid_psi D _ _ t hB]
        simp only [map_map]
        refine psi_eq D _ _ _ _ (fun p => ?_) (fun n => ?_)
        · simpa [NonemptySubset.comp_val, NonemptySubset.compFun, binLeftEquiv,
            binRightEquiv] using p.2
        · rcases n with f | b
          · simpa [NonemptySubset.comp_val, NonemptySubset.compFun, binLeftEquiv,
              binRightEquiv] using f.1.2
          · exact (by simp [hsi] : (s.1 i && t.1 b) = false)
      · haveI : IsEmpty (Without {a // ¬ s.1 a = true} ⟨i, hsi⟩) := not_nonempty_iff.mp hF'
        rw [comp_prod_of_isEmpty D _ _, bin_map_right, bin_left_psi D _ t hB]
        simp only [map_map]
        refine psi_eq D _ _ _ _ (fun p => ?_) (fun n => ?_)
        · simpa [NonemptySubset.comp_val, NonemptySubset.compFun, binLeftEquiv,
            binRightEquiv] using p.2
        · exact (by simp [hsi] : (s.1 i && t.1 n) = false)

/-! ### The morphism -/

/-- **The morphism out of `NonemptySubset`** defined by generator values satisfying the relations:
it sends a subset to its normal form. -/
def lift : SetOperadHom NonemptySubset S where
  app A _ _ := D.psi A
  app_map e s := D.psi_map e s
  app_one := by rw [psi_of_all D _ (fun _ => rfl) ⟨()⟩, prod_unit]
  app_comp i s t := D.psi_comp i s t

/-- Transport generator values along a morphism. -/
def map {T : (A : Type) → [Fintype A] → [DecidableEq A] → Type*} [SetOperad T]
    (φ : SetOperadHom S T) : ComTriasData T where
  mid := φ.app _ D.mid
  left := φ.app _ D.left
  comm := isComm_app D.comm φ
  assoc := isAssoc_app D.assoc φ
  lassoc := by
    simpa only [SetOperadHom.app_map, SetOperadHom.app_bin, SetOperadHom.app_one]
      using congrArg (φ.app _) D.lassoc
  lperm := by
    simpa only [SetOperadHom.app_map, SetOperadHom.app_bin, SetOperadHom.app_one]
      using congrArg (φ.app _) D.lperm
  lmid := by
    simpa only [SetOperadHom.app_map, SetOperadHom.app_bin, SetOperadHom.app_one]
      using congrArg (φ.app _) D.lmid
  midl := by
    simpa only [SetOperadHom.app_map, SetOperadHom.app_bin, SetOperadHom.app_one]
      using congrArg (φ.app _) D.midl

/-- **Morphisms carry normal forms to normal forms.** -/
lemma app_psi {T : (A : Type) → [Fintype A] → [DecidableEq A] → Type*} [SetOperad T]
    (φ : SetOperadHom S T) (s : NonemptySubset A) : φ.app A (D.psi A s) = (D.map φ).psi A s := by
  by_cases h : ∀ a, s.1 a = true
  · rw [psi_of_all D s h (nonempty_of_tri s), psi_of_all _ s h (nonempty_of_tri s), app_prod]
    rfl
  · rw [psi_of_not_all D s h, psi_of_not_all _ s h, φ.app_map, φ.app_bin, app_prod, app_prod]
    rfl

lemma comp_lift {T : (A : Type) → [Fintype A] → [DecidableEq A] → Type*} [SetOperad T]
    (φ : SetOperadHom S T) : φ.comp D.lift = (D.map φ).lift := by
  ext A _ _ s
  exact D.app_psi φ s

@[ext] lemma ext' {D₁ D₂ : ComTriasData S} (hmu : D₁.mid = D₂.mid) (hnu : D₁.left = D₂.left) :
    D₁ = D₂ := by
  cases D₁
  cases D₂
  cases hmu
  cases hnu
  rfl

end ComTriasData

/-! ## The nonempty subsets -/

namespace NonemptySubset

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- `⊥`: the full subset of two inputs. -/
def mid : NonemptySubset (Fin 2) := ⟨fun _ => true, ⟨0, rfl⟩⟩

/-- `⊣`: the first of two inputs. -/
def left : NonemptySubset (Fin 2) := ⟨fun k => decide (k = 0), ⟨0, rfl⟩⟩

lemma bin_val (g : NonemptySubset (Fin 2)) (x : NonemptySubset A) (y : NonemptySubset B) :
    (bin g x y).1 = Sum.elim (fun a => g.1 0 && x.1 a) (fun b => g.1 1 && y.1 b) := by
  funext c
  rcases c with a | b <;> rfl

/-- **The generators of `NonemptySubset` satisfy the relations.** -/
def data : ComTriasData NonemptySubset where
  mid := mid
  left := left
  comm := by
    ext k
    fin_cases k <;> rfl
  assoc := by
    ext c
    rcases c with u | (u | u) <;> rfl
  lassoc := by
    ext c
    rcases c with u | (u | u) <;> rfl
  lperm := by
    ext c
    rcases c with u | (u | u) <;> rfl
  lmid := by
    ext c
    rcases c with u | (u | u) <;> rfl
  midl := by
    ext c
    rcases c with u | (u | u) <;> rfl

/-- The full subsets form a copy of `ComSet` in `NonemptySubset`. -/
def full : SetOperadHom ComSet NonemptySubset where
  app A _ _ x := ⟨fun _ => true, x.down.elim fun a => ⟨a, rfl⟩⟩
  app_map _ _ := rfl
  app_one := rfl
  app_comp i x y := by
    ext c
    rcases c with a | b <;> rfl

/-- **The products in `NonemptySubset` are the full subsets.** -/
lemma prod_val (hA : Nonempty A) (a : A) : (prod data.comm data.assoc A hA).1 a = true := by
  have h : ComSet.lift data.mid data.comm data.assoc = full :=
    ComSet.hom_ext (by rw [ComSet.lift_mu]; rfl)
  have := congrArg (fun φ : SetOperadHom ComSet NonemptySubset => (φ.app A ⟨hA⟩).1 a) h
  exact this

/-- **Every subset is its own normal form.** -/
lemma data_psi (s : NonemptySubset A) : data.psi A s = s := by
  ext a
  by_cases h : ∀ a, s.1 a = true
  · rw [ComTriasData.psi_of_all data s h (ComTriasData.nonempty_of_tri s), prod_val, h a]
  · rw [ComTriasData.psi_of_not_all data s h, map_val, Function.comp_apply, bin_val]
    by_cases ha : s.1 a = true
    · rw [Equiv.sumCompl_symm_apply_of_pos (p := fun a => s.1 a = true) ha, Sum.elim_inl,
        prod_val, ha]
      rfl
    · rw [Equiv.sumCompl_symm_apply_of_neg (p := fun a => s.1 a = true) ha, Sum.elim_inr]
      simp only [Bool.not_eq_true] at ha
      rw [ha]
      rfl

lemma data_lift : data.lift = SetOperadHom.id := by
  apply SetOperadHom.ext
  intro A _ _ s
  exact data_psi s

/-- **Morphisms out of `NonemptySubset` are determined by the two generators.** -/
theorem hom_ext {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type*} [SetOperad S]
    {φ ψ : SetOperadHom NonemptySubset S} (hmu : φ.app _ mid = ψ.app _ mid)
    (hnu : φ.app _ left = ψ.app _ left) :
    φ = ψ := by
  have hφ : φ = (data.map φ).lift := by rw [← ComTriasData.comp_lift data φ, data_lift]; rfl
  have hψ : ψ = (data.map ψ).lift := by rw [← ComTriasData.comp_lift data ψ, data_lift]; rfl
  rw [hφ, hψ, ComTriasData.ext' (D₁ := data.map φ) (D₂ := data.map ψ) hmu hnu]

end NonemptySubset

namespace ComTriasData

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type*} [SetOperad S] (D : ComTriasData S)

lemma lift_mid : D.lift.app _ NonemptySubset.mid = D.mid := by
  show D.psi _ NonemptySubset.mid = D.mid
  rw [psi_of_all D _ (fun _ => rfl) ⟨0⟩, prod_fin_two]

lemma lift_left : D.lift.app _ NonemptySubset.left = D.left := by
  show D.psi _ NonemptySubset.left = D.left
  rw [psi_eq D NonemptySubset.left ⟨()⟩ ⟨()⟩ finTwoSum.symm (fun _ => rfl) (fun _ => rfl),
      prod_unit,
    bin_one_one, map_map]
  exact map_eq_self (fun k => by fin_cases k <;> rfl) _

end ComTriasData

/-! ## The universal property and the presentation -/

namespace NonemptySubset

/-- **The universal property of `NonemptySubset`**: morphisms out of it are generator values
satisfying the relations. -/
def homEquiv {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type*} [SetOperad S] :
    SetOperadHom NonemptySubset S ≃ ComTriasData S where
  toFun φ := data.map φ
  invFun D := D.lift
  left_inv φ := by
    show (data.map φ).lift = φ
    rw [← ComTriasData.comp_lift data φ, data_lift]
    rfl
  right_inv D := ComTriasData.ext' D.lift_mid D.lift_left

/-- The generators and relations, in the presented operad. -/
def presData : ComTriasData (Pres ComTriasGen ComTriasRel) where
  mid := Pres.gen .mid
  left := Pres.gen .left
  comm := Pres.mk_eq_mk_of_rel ComTriasRel.comm
  assoc := Pres.mk_eq_mk_of_rel ComTriasRel.assoc
  lassoc := Pres.mk_eq_mk_of_rel ComTriasRel.lassoc
  lperm := Pres.mk_eq_mk_of_rel ComTriasRel.lperm
  lmid := Pres.mk_eq_mk_of_rel ComTriasRel.lmid
  midl := Pres.mk_eq_mk_of_rel ComTriasRel.midl

/-- The generator values of `NonemptySubset`. -/
def gens : ∀ n, ComTriasGen n → NonemptySubset (Fin n)
  | _, .mid => mid
  | _, .left => left

/-- The presented operad maps to `NonemptySubset`. -/
def ofPres : SetOperadHom (Pres ComTriasGen ComTriasRel) NonemptySubset :=
  Pres.lift gens ((respects_iff _).mpr
    ⟨data.comm, data.assoc, data.lassoc, data.lperm, data.lmid, data.midl⟩)

/-- **Vallette's presentation**: the set operad of nonempty subsets is presented by `⊥`, `⊣` and
the relations of commutative trialgebras. -/
def presIso : SetOperadIso (Pres ComTriasGen ComTriasRel) NonemptySubset where
  hom := ofPres
  inv := presData.lift
  hom_inv_id := Pres.hom_ext fun n g => by
    cases g
    · exact presData.lift_mid
    · exact presData.lift_left
  inv_hom_id := hom_ext
    (by
      show ofPres.app _ (presData.lift.app _ mid) = mid
      rw [presData.lift_mid]
      rfl)
    (by
      show ofPres.app _ (presData.lift.app _ left) = left
      rw [presData.lift_left]
      rfl)

end NonemptySubset


namespace ComTrias

variable (R : Type*) [CommRing R] {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]

/-- **The universal property of `ComTrias`**: a morphism of operads in `R`-modules out of it is a
pair `⊥`, `⊣` satisfying the relations of commutative trialgebras. -/
noncomputable def homEquiv : SymOperadHom R (ComTrias R) Q ≃ ComTriasData (Und R Q) :=
  (linHomEquiv R).symm.trans NonemptySubset.homEquiv

end ComTrias

end Operad
