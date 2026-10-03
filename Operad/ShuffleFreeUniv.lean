/-
# The universal property of the free shuffle operad

A morphism of shuffle operads out of the free shuffle operad on generators of any arity
(`Operad.FreeSh`) is the same as a family of operations `E k → P (Fin k)` (`Operad.FreeSh.lift`).

* **Finite sets of natural numbers as input sets** (`Operad.NS`): in an arbitrary shuffle operad,
  grafting an operation with inputs `T` at the input `a = min T` of one with inputs `S`, the
  inputs of the composite being `(S ∖ a) ∪ T` with the order of the natural numbers, is a shuffle
  composition (`Operad.canon`, `Operad.compN`). Its laws — the unit laws, sequential and parallel
  associativity, equivariance under strictly increasing relabellings — follow from the axioms,
  relabelling along order isomorphisms depending only on the input sets, order isomorphisms of
  finite linear orders being unique (`Operad.map_eq_castN`).
-/
import Operad.ShuffleFreeAny
import Operad.ShuffleIdeal

universe u v w

namespace Operad

/-! ## Finite sets of natural numbers as input sets -/

section NatSets

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [LinearOrder A] → Type w}
  [∀ (A : Type) [Fintype A] [LinearOrder A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [LinearOrder A], Module R (P A)] [ShuffleOperad R P]

/-- **A finite set of natural numbers**, as a finite linear order. -/
abbrev NS (S : Finset ℕ) : Type := {n // n ∈ S}

variable (R P) in
/-- **Transport along an equality of finite sets.** -/
def castN : {S S' : Finset ℕ} → S = S' → P (NS S) →ₗ[R] P (NS S')
  | _, _, rfl => LinearMap.id

omit [ShuffleOperad R P] in
@[simp] lemma castN_rfl {S : Finset ℕ} (x : P (NS S)) : castN R P rfl x = x := rfl

omit [ShuffleOperad R P] in
@[simp] lemma castN_castN {S S' S'' : Finset ℕ} (h : S = S') (h' : S' = S'') (x : P (NS S)) :
    castN R P h' (castN R P h x) = castN R P (h.trans h') x := by
  subst h h'
  rfl

/-- **Relabelling along an order isomorphism only depends on the two input sets**, order
isomorphisms of finite linear orders being unique. -/
lemma map_eq_map {A B : Type} [Fintype A] [LinearOrder A] [Fintype B] [LinearOrder B]
    (σ τ : A ≃o B) (x : P A) :
    ShuffleOperad.map (R := R) σ x = ShuffleOperad.map (R := R) τ x := by
  rw [Subsingleton.elim σ τ]

/-- **Relabelling between equal finite sets is transport.** -/
lemma map_eq_castN {S S' : Finset ℕ} (σ : NS S ≃o NS S') (h : S = S') (x : P (NS S)) :
    ShuffleOperad.map (R := R) σ x = castN R P h x := by
  subst h
  rw [map_eq_map σ (OrderIso.refl _), ShuffleOperad.map_refl, castN_rfl]

/-- **The order isomorphism between equal finite sets.** -/
def eqIso {S S' : Finset ℕ} (h : S = S') : NS S ≃o NS S' where
  toFun x := ⟨x.1, h ▸ x.2⟩
  invFun x := ⟨x.1, h ▸ x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

@[simp] lemma eqIso_val {S S' : Finset ℕ} (h : S = S') (x : NS S) : (eqIso h x).1 = x.1 := rfl

/-- A shuffle followed by an order isomorphism is a shuffle. -/
lemma IsShuffle.trans_orderIso {A B C C' : Type} [LinearOrder A] [LinearOrder B]
    [LinearOrder C] [LinearOrder C'] {i : A} {e : Without A i ⊕ B ≃ C} (he : IsShuffle i e)
    (ρ : C ≃o C') : IsShuffle i (e.trans ρ.toEquiv) where
  mono_left := ρ.strictMono.comp he.mono_left
  mono_right := ρ.strictMono.comp he.mono_right
  pointed a b hb := by
    rw [he.pointed a b hb]
    exact ρ.lt_iff_lt.symm

/-- **Composing along a shuffle followed by an order isomorphism** is composing and relabelling. -/
lemma comp_trans_orderIso {A B C C' : Type} [Fintype A] [LinearOrder A] [Fintype B]
    [LinearOrder B] [Fintype C] [LinearOrder C] [Fintype C'] [LinearOrder C'] (i : A)
    {e : Without A i ⊕ B ≃ C} (he : IsShuffle i e) (ρ : C ≃o C') (x : P A) (y : P B) :
    ShuffleOperad.comp (R := R) i (e.trans ρ.toEquiv) (he.trans_orderIso ρ) x y =
      ShuffleOperad.map (R := R) ρ (ShuffleOperad.comp (R := R) i e he x y) := by
  have := ShuffleOperad.map_comp (R := R) (OrderIso.refl A) (OrderIso.refl B) ρ i e he
    (e.trans ρ.toEquiv) (he.trans_orderIso ρ) (fun c => by rcases c with a | b <;> rfl) x y
  rw [this, ShuffleOperad.map_refl, ShuffleOperad.map_refl]
  rfl

/-! ### Canonical grafting -/

/-- **The conditions for grafting** inputs `T` at the input `a` of inputs `S`: `a` is the least
element of `T`, and the other inputs of `S` are not in `T`. -/
structure GraftOK (S T : Finset ℕ) (a : ℕ) : Prop where
  mem : a ∈ S
  memT : a ∈ T
  le : ∀ b ∈ T, a ≤ b
  disj : Disjoint (S.erase a) T

/-- **The canonical shuffle** of grafting `T` at `a ∈ S`: the identity on natural numbers. -/
def canon {S T : Finset ℕ} {a : ℕ} (h : GraftOK S T a) :
    Without (NS S) ⟨a, h.mem⟩ ⊕ NS T ≃ NS (S.erase a ∪ T) where
  toFun
    | Sum.inl x => ⟨x.1.1, Finset.mem_union_left _
        (Finset.mem_erase.2 ⟨fun e => x.2 (Subtype.ext e), x.1.2⟩)⟩
    | Sum.inr y => ⟨y.1, Finset.mem_union_right _ y.2⟩
  invFun z := if hz : z.1 ∈ T then Sum.inr ⟨z.1, hz⟩ else
    Sum.inl ⟨⟨z.1, Finset.mem_of_mem_erase ((Finset.mem_union.1 z.2).resolve_right hz)⟩,
      fun e => Finset.ne_of_mem_erase ((Finset.mem_union.1 z.2).resolve_right hz)
        (congrArg Subtype.val e)⟩
  left_inv := by
    rintro (x | y)
    · have hx : x.1.1 ∉ T := fun hT => Finset.disjoint_left.1 h.disj
        (Finset.mem_erase.2 ⟨fun e => x.2 (Subtype.ext e), x.1.2⟩) hT
      simp [hx]
    · simp [y.2]
  right_inv z := by
    by_cases hz : z.1 ∈ T <;> simp [hz]

@[simp] lemma canon_inl {S T : Finset ℕ} {a : ℕ} (h : GraftOK S T a)
    (x : Without (NS S) ⟨a, h.mem⟩) : (canon h (Sum.inl x)).1 = x.1.1 := rfl

@[simp] lemma canon_inr {S T : Finset ℕ} {a : ℕ} (h : GraftOK S T a) (y : NS T) :
    (canon h (Sum.inr y)).1 = y.1 := rfl

lemma isShuffle_canon {S T : Finset ℕ} {a : ℕ} (h : GraftOK S T a) :
    IsShuffle (⟨a, h.mem⟩ : NS S) (canon h) where
  mono_left _ _ hxy := hxy
  mono_right _ _ hxy := hxy
  pointed x b hb := by
    have hba : b.1 = a := le_antisymm (by simpa using hb (⟨a, h.memT⟩ : NS T)) (h.le b.1 b.2)
    show x.1.1 < a ↔ x.1.1 < b.1
    rw [hba]

variable (R P) in
open Classical in
/-- **Canonical grafting**: compose along the canonical shuffle, zero when the conditions fail. -/
noncomputable def compN (S T : Finset ℕ) (a : ℕ) :
    P (NS S) →ₗ[R] P (NS T) →ₗ[R] P (NS (S.erase a ∪ T)) :=
  if h : GraftOK S T a then ShuffleOperad.comp (⟨a, h.mem⟩ : NS S) (canon h) (isShuffle_canon h)
  else 0

lemma compN_of {S T : Finset ℕ} {a : ℕ} (h : GraftOK S T a) :
    compN R P S T a = ShuffleOperad.comp (⟨a, h.mem⟩ : NS S) (canon h) (isShuffle_canon h) :=
  dif_pos h

/-- **Equivariance transports shuffles**: a shuffle precomposed with relabellings of the two input
sets is a shuffle. -/
lemma IsShuffle.of_compEquiv {A A' B B' C : Type} [LinearOrder A] [LinearOrder A']
    [LinearOrder B] [LinearOrder B'] [LinearOrder C] (σ : A ≃o A') (τ : B ≃o B') {i : A}
    {e' : Without A' (σ i) ⊕ B' ≃ C} (he' : IsShuffle (σ i) e') :
    IsShuffle i ((Sym.compEquiv σ.toEquiv τ.toEquiv i).trans e') where
  mono_left x y hxy := he'.mono_left (show (⟨σ x.1, fun h => x.2 (σ.injective h)⟩ :
    Without A' (σ i)) < ⟨σ y.1, fun h => y.2 (σ.injective h)⟩ from σ.lt_iff_lt.2 hxy)
  mono_right x y hxy := he'.mono_right (τ.lt_iff_lt.2 hxy)
  pointed x b hb := by
    have := he'.pointed ⟨σ x.1, fun h => x.2 (σ.injective h)⟩ (τ b) fun b' => by
      obtain ⟨b'', rfl⟩ := τ.surjective b'
      exact τ.le_iff_le.2 (hb b'')
    rw [← σ.lt_iff_lt]
    exact this

/-- The order isomorphism between `Unit` and a single natural number. -/
def unitIso (a : ℕ) : Unit ≃o NS {a} :=
  orderIsoOfSubsingleton ⟨fun _ => ⟨a, Finset.mem_singleton_self a⟩, fun _ => (), fun _ => rfl,
    fun x => Subtype.ext (Finset.mem_singleton.1 x.2).symm⟩

variable (R P) in
/-- **The unit** on a single natural number. -/
noncomputable def oneN (a : ℕ) : P (NS {a}) :=
  ShuffleOperad.map (R := R) (unitIso a) (ShuffleOperad.one R)

/-- **The left unit law of canonical grafting.** -/
lemma compN_one_left {T : Finset ℕ} {a : ℕ} (ha : a ∈ T) (hle : ∀ b ∈ T, a ≤ b)
    (y : P (NS T)) :
    compN R P {a} T a (oneN R P a) y = castN R P (by simp) y := by
  have h : GraftOK {a} T a := ⟨Finset.mem_singleton_self a, ha, hle, by simp⟩
  rw [compN_of h, oneN]
  have hsh := IsShuffle.of_compEquiv (i := ()) (unitIso a) (OrderIso.refl (NS T))
    (isShuffle_canon h)
  have key := ShuffleOperad.map_comp (R := R) (unitIso a) (OrderIso.refl (NS T))
    (OrderIso.refl _) () _ hsh (canon h) (isShuffle_canon h) (fun _ => rfl)
    (ShuffleOperad.one R) y
  rw [ShuffleOperad.map_refl, ShuffleOperad.map_refl] at key
  refine key.symm.trans ?_
  rw [ShuffleOperad.one_comp _ hsh (eqIso (S := T) (S' := ({a} : Finset ℕ).erase a ∪ T)
    (by simp)) (fun b => Subtype.ext rfl), map_eq_castN]

omit [ShuffleOperad R P] in
lemma erase_union_singleton {S : Finset ℕ} {a : ℕ} (ha : a ∈ S) : S = S.erase a ∪ {a} := by
  rw [Finset.union_singleton, Finset.insert_erase ha]

/-- **The right unit law of canonical grafting.** -/
lemma compN_one_right {S : Finset ℕ} {a : ℕ} (ha : a ∈ S) (x : P (NS S)) :
    compN R P S {a} a x (oneN R P a) = castN R P (erase_union_singleton ha) x := by
  have h : GraftOK S {a} a := ⟨ha, Finset.mem_singleton_self a,
    fun b hb => (Finset.mem_singleton.1 hb).ge, by simp⟩
  rw [compN_of h, oneN]
  have hsh := IsShuffle.of_compEquiv (i := (⟨a, ha⟩ : NS S)) (OrderIso.refl (NS S)) (unitIso a)
    (isShuffle_canon h)
  have key := ShuffleOperad.map_comp (R := R) (OrderIso.refl (NS S)) (unitIso a)
    (OrderIso.refl _) (⟨a, ha⟩ : NS S) _ hsh (canon h) (isShuffle_canon h) (fun _ => rfl) x
    (ShuffleOperad.one R)
  rw [ShuffleOperad.map_refl, ShuffleOperad.map_refl] at key
  refine key.symm.trans ?_
  rw [ShuffleOperad.comp_one _ _ hsh (eqIso (erase_union_singleton ha)) fun s => ?_,
    map_eq_castN]
  apply Subtype.ext
  show s.1 = (((Sym.compEquiv (OrderIso.refl (NS S)).toEquiv (unitIso a).toEquiv
    ⟨a, ha⟩).trans (canon h)) (if h' : s = ⟨a, ha⟩ then Sum.inr () else Sum.inl ⟨s, h'⟩)).1
  by_cases hs : s = ⟨a, ha⟩
  · rw [dif_pos hs, hs]
    rfl
  · rw [dif_neg hs]
    rfl

lemma seq_eq {S T U : Finset ℕ} {a b : ℕ} (h₁ : GraftOK S T a) (h₃ : GraftOK T U b) :
    S.erase a ∪ (T.erase b ∪ U) = (S.erase a ∪ T).erase b ∪ U := by
  ext n
  simp only [Finset.mem_union, Finset.mem_erase]
  constructor
  · rintro (⟨hna, hnS⟩ | ⟨hnb, hnT⟩ | hnU)
    · refine Or.inl ⟨fun hnb => ?_, Or.inl ⟨hna, hnS⟩⟩
      exact Finset.disjoint_left.1 h₁.disj (Finset.mem_erase.2 ⟨hna, hnS⟩) (hnb ▸ h₃.mem)
    · exact Or.inl ⟨hnb, Or.inr hnT⟩
    · exact Or.inr hnU
  · rintro (⟨hnb, (⟨hna, hnS⟩ | hnT)⟩ | hnU)
    · exact Or.inl ⟨hna, hnS⟩
    · exact Or.inr (Or.inl ⟨hnb, hnT⟩)
    · exact Or.inr (Or.inr hnU)

/-- **Sequential associativity of canonical grafting.** -/
lemma compN_seq {S T U : Finset ℕ} {a b : ℕ} (h₁ : GraftOK S T a) (h₃ : GraftOK T U b)
    (hSU : Disjoint (S.erase a) U) (x : P (NS S)) (y : P (NS T)) (z : P (NS U)) :
    compN R P (S.erase a ∪ T) U b (compN R P S T a x y) z =
      castN R P (seq_eq h₁ h₃) (compN R P S (T.erase b ∪ U) a x (compN R P T U b y z)) := by
  have hbS : b ∉ S.erase a := fun hb => Finset.disjoint_left.1 h₁.disj hb h₃.mem
  have h₂ : GraftOK (S.erase a ∪ T) U b := ⟨Finset.mem_union_right _ h₃.mem, h₃.memT, h₃.le, by
    rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hbS]
    exact Finset.disjoint_union_left.2 ⟨hSU, h₃.disj⟩⟩
  have h₄ : GraftOK S (T.erase b ∪ U) a := ⟨h₁.mem, by
    by_cases hab : a = b
    · exact Finset.mem_union_right _ (hab ▸ h₃.memT)
    · exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hab, h₁.memT⟩), fun c hc => by
    rcases Finset.mem_union.1 hc with hc | hc
    · exact h₁.le c (Finset.mem_of_mem_erase hc)
    · exact (h₁.le b h₃.mem).trans (h₃.le c hc), by
    refine Finset.disjoint_union_right.2 ⟨?_, hSU⟩
    exact Finset.disjoint_of_subset_right (Finset.erase_subset _ _) h₁.disj⟩
  rw [compN_of h₁, compN_of h₂, compN_of h₃, compN_of h₄]
  have key := ShuffleOperad.comp_assoc_seq (R := R) (⟨a, h₁.mem⟩ : NS S) (⟨b, h₃.mem⟩ : NS T)
    (canon h₁) (isShuffle_canon h₁) (canon h₂) (isShuffle_canon h₂) (canon h₃)
    (isShuffle_canon h₃) ((canon h₄).trans (eqIso (seq_eq h₁ h₃)).toEquiv)
    ((isShuffle_canon h₄).trans_orderIso _) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) x y z
  refine key.trans ?_
  rw [comp_trans_orderIso, map_eq_castN]

omit [ShuffleOperad R P] in
lemma par_eq {S T U : Finset ℕ} {a b : ℕ} (hab : a ≠ b) (h₁ : GraftOK S T a)
    (h₃ : GraftOK S U b) : (S.erase b ∪ U).erase a ∪ T = (S.erase a ∪ T).erase b ∪ U := by
  have haU : a ∉ U := fun h => Finset.disjoint_left.1 h₃.disj (Finset.mem_erase.2 ⟨hab, h₁.mem⟩) h
  have hbT : b ∉ T := fun h =>
    Finset.disjoint_left.1 h₁.disj (Finset.mem_erase.2 ⟨Ne.symm hab, h₃.mem⟩) h
  ext n
  simp only [Finset.mem_union, Finset.mem_erase]
  constructor
  · rintro (⟨hna, (⟨hnb, hnS⟩ | hnU)⟩ | hnT)
    · exact Or.inl ⟨hnb, Or.inl ⟨hna, hnS⟩⟩
    · exact Or.inr hnU
    · exact Or.inl ⟨fun h => hbT (h ▸ hnT), Or.inr hnT⟩
  · rintro (⟨hnb, (⟨hna, hnS⟩ | hnT)⟩ | hnU)
    · exact Or.inl ⟨hna, Or.inl ⟨hnb, hnS⟩⟩
    · exact Or.inr hnT
    · exact Or.inl ⟨fun h => haU (h ▸ hnU), Or.inr hnU⟩

/-- **Parallel associativity of canonical grafting.** -/
lemma compN_par {S T U : Finset ℕ} {a b : ℕ} (hab : a ≠ b) (h₁ : GraftOK S T a)
    (h₃ : GraftOK S U b) (hTU : Disjoint T U) (x : P (NS S)) (y : P (NS T)) (z : P (NS U)) :
    compN R P (S.erase a ∪ T) U b (compN R P S T a x y) z =
      castN R P (par_eq hab h₁ h₃) (compN R P (S.erase b ∪ U) T a (compN R P S U b x z) y) := by
  have haU : a ∉ U := fun h => Finset.disjoint_left.1 h₃.disj (Finset.mem_erase.2 ⟨hab, h₁.mem⟩) h
  have hbT : b ∉ T := fun h =>
    Finset.disjoint_left.1 h₁.disj (Finset.mem_erase.2 ⟨Ne.symm hab, h₃.mem⟩) h
  have h₂ : GraftOK (S.erase a ∪ T) U b :=
    ⟨Finset.mem_union_left _ (Finset.mem_erase.2 ⟨Ne.symm hab, h₃.mem⟩), h₃.memT, h₃.le, by
      rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hbT]
      refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_of_subset_left (fun n hn => ?_) h₃.disj,
        hTU⟩
      exact Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hn).1,
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hn)⟩⟩
  have h₄ : GraftOK (S.erase b ∪ U) T a :=
    ⟨Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hab, h₁.mem⟩), h₁.memT, h₁.le, by
      rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem haU]
      refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_of_subset_left (fun n hn => ?_) h₁.disj,
        hTU.symm⟩
      exact Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hn).1,
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hn)⟩⟩
  rw [compN_of h₁, compN_of h₂, compN_of h₃, compN_of h₄]
  have hik : (⟨a, h₁.mem⟩ : NS S) ≠ ⟨b, h₃.mem⟩ := fun h => hab (congrArg Subtype.val h)
  have key := ShuffleOperad.comp_assoc_par (R := R) hik (canon h₁) (isShuffle_canon h₁)
    (canon h₂) (isShuffle_canon h₂) (canon h₃) (isShuffle_canon h₃)
    ((canon h₄).trans (eqIso (par_eq hab h₁ h₃)).toEquiv) ((isShuffle_canon h₄).trans_orderIso _)
    (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => rfl) x y z
  exact key.trans ((comp_trans_orderIso (⟨a, h₄.mem⟩ : NS (S.erase b ∪ U)) (isShuffle_canon h₄)
    (eqIso (par_eq hab h₁ h₃)) _ y).trans (map_eq_castN _ _ _))

/-- **The order isomorphism of a strictly increasing relabelling.** -/
noncomputable def relIso (f : ℕ → ℕ) {S : Finset ℕ} (hf : StrictMonoOn f S) :
    NS S ≃o NS (S.image f) :=
  StrictMono.orderIsoOfSurjective (fun x => ⟨f x.1, Finset.mem_image_of_mem f x.2⟩)
    (fun x y hxy => hf x.2 y.2 hxy) fun y => by
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.1 y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

@[simp] lemma relIso_val (f : ℕ → ℕ) {S : Finset ℕ} (hf : StrictMonoOn f S) (x : NS S) :
    (relIso f hf x).1 = f x.1 := rfl

omit [ShuffleOperad R P] in
lemma image_eq {S T : Finset ℕ} {a : ℕ} (h : GraftOK S T a) {f : ℕ → ℕ}
    (hf : Set.InjOn f ↑(S ∪ T)) :
    (S.image f).erase (f a) ∪ T.image f = (S.erase a ∪ T).image f := by
  ext n
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro (⟨hna, s, hs, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨s, Or.inl ⟨fun e => hna (e ▸ rfl), hs⟩, rfl⟩
    · exact ⟨t, Or.inr ht, rfl⟩
  · rintro ⟨c, (⟨hca, hcS⟩ | hcT), rfl⟩
    · refine Or.inl ⟨fun e => hca (hf ?_ ?_ e), c, hcS, rfl⟩
      · exact Finset.mem_coe.2 (Finset.mem_union_left _ hcS)
      · exact Finset.mem_coe.2 (Finset.mem_union_left _ h.mem)
    · exact Or.inr ⟨c, hcT, rfl⟩

omit [ShuffleOperad R P] in
lemma graftOK_image {S T : Finset ℕ} {a : ℕ} (h : GraftOK S T a) {f : ℕ → ℕ}
    (hf : StrictMonoOn f ↑(S ∪ T)) : GraftOK (S.image f) (T.image f) (f a) where
  mem := Finset.mem_image_of_mem f h.mem
  memT := Finset.mem_image_of_mem f h.memT
  le b hb := by
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hb
    exact hf.monotoneOn (Finset.mem_coe.2 (Finset.mem_union_left _ h.mem))
      (Finset.mem_coe.2 (Finset.mem_union_right _ ht)) (h.le t ht)
  disj := by
    refine Finset.disjoint_left.2 fun n hn hn' => ?_
    obtain ⟨hna, hn⟩ := Finset.mem_erase.1 hn
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hn
    obtain ⟨t, ht, hts⟩ := Finset.mem_image.1 hn'
    have hst : t = s := hf.injOn (Finset.mem_coe.2 (Finset.mem_union_right _ ht))
      (Finset.mem_coe.2 (Finset.mem_union_left _ hs)) hts
    subst hst
    exact Finset.disjoint_left.1 h.disj (Finset.mem_erase.2 ⟨fun e => hna (e ▸ rfl), hs⟩) ht

/-- **Canonical grafting is equivariant** under strictly increasing relabellings. -/
lemma map_relIso_compN {S T : Finset ℕ} {a : ℕ} (h : GraftOK S T a) {f : ℕ → ℕ}
    (hf : StrictMonoOn f ↑(S ∪ T)) (x : P (NS S)) (y : P (NS T)) :
    ShuffleOperad.map (R := R) (relIso f (hf.mono (fun n hn => by
        rcases Finset.mem_union.1 (Finset.mem_coe.1 hn) with hn | hn
        · exact Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_of_mem_erase hn))
        · exact Finset.mem_coe.2 (Finset.mem_union_right _ hn))))
      (compN R P S T a x y) =
    castN R P (image_eq h hf.injOn) (compN R P (S.image f) (T.image f) (f a)
      (ShuffleOperad.map (R := R) (relIso f (hf.mono (fun n hn =>
        Finset.mem_coe.2 (Finset.mem_union_left _ hn)))) x)
      (ShuffleOperad.map (R := R) (relIso f (hf.mono (fun n hn =>
        Finset.mem_coe.2 (Finset.mem_union_right _ hn)))) y)) := by
  have h' := graftOK_image h hf
  rw [compN_of h, compN_of h']
  have key := ShuffleOperad.map_comp (R := R) (relIso f (hf.mono (fun n hn =>
      Finset.mem_coe.2 (Finset.mem_union_left _ hn))))
    (relIso f (hf.mono (fun n hn => Finset.mem_coe.2 (Finset.mem_union_right _ hn))))
    (relIso f (hf.mono (fun n hn => by
        rcases Finset.mem_union.1 (Finset.mem_coe.1 hn) with hn | hn
        · exact Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_of_mem_erase hn))
        · exact Finset.mem_coe.2 (Finset.mem_union_right _ hn))))
    (⟨a, h.mem⟩ : NS S) (canon h) (isShuffle_canon h)
    ((canon h').trans (eqIso (image_eq h hf.injOn)).toEquiv) ((isShuffle_canon h').trans_orderIso _)
    (fun c => by rcases c with x | y <;> rfl) x y
  exact key.trans ((comp_trans_orderIso (⟨f a, h'.mem⟩ : NS (S.image f)) (isShuffle_canon h')
    (eqIso (image_eq h hf.injOn)) _ _).trans (map_eq_castN _ _ _))

lemma compN_slot {S T : Finset ℕ} {a a' : ℕ} (h : a = a') (x : P (NS S)) (y : P (NS T)) :
    compN R P S T a' x y = castN R P (by rw [h]) (compN R P S T a x y) := by
  subst h
  rfl

omit [ShuffleOperad R P] in
lemma castN_eq_castN_castN {S S' S'' : Finset ℕ} (h₁ : S = S') (h₂ : S'' = S') (h₃ : S = S'')
    (x : P (NS S)) : castN R P h₁ x = castN R P h₂ (castN R P h₃ x) := by
  subst h₂ h₃
  rfl

lemma compN_castN {S S' T T' : Finset ℕ} (hS : S = S') (hT : T = T') (a : ℕ) (x : P (NS S))
    (y : P (NS T)) :
    compN R P S' T' a (castN R P hS x) (castN R P hT y) =
      castN R P (by rw [hS, hT]) (compN R P S T a x y) := by
  subst hS hT
  rfl

/-! ### Total composition, one input at a time -/

/-- **The stages of a total composition**: the inputs after grafting the first `j` operations,
the operation with inputs `L j` at the input `m j`. -/
def stage (M : Finset ℕ) (m : ℕ → ℕ) (L : ℕ → Finset ℕ) : ℕ → Finset ℕ
  | 0 => M
  | j + 1 => (stage M m L j).erase (m j) ∪ L j

variable (R P) in
/-- **Total composition**, grafting the operations `y j` at the inputs `m j` one at a time. -/
noncomputable def stg (M : Finset ℕ) (m : ℕ → ℕ) (L : ℕ → Finset ℕ) (x₀ : P (NS M))
    (y : ∀ j, P (NS (L j))) : (j : ℕ) → P (NS (stage M m L j))
  | 0 => x₀
  | j + 1 => compN R P (stage M m L j) (L j) (m j) (stg M m L x₀ y j) (y j)

section Insert

variable {M : Finset ℕ} {m : ℕ → ℕ} {L L' : ℕ → Finset ℕ} {k l : ℕ} {T : Finset ℕ} {a : ℕ}

omit [ShuffleOperad R P] in
lemma stage_insert_le (hL : ∀ j, j ≠ l → L' j = L j) :
    ∀ j ≤ l, stage M m L' j = stage M m L j
  | 0, _ => rfl
  | j + 1, hj => by
    rw [stage, stage, stage_insert_le hL j (by omega), hL j (by omega)]

omit [ShuffleOperad R P] in
lemma stage_insert_gt (hL : ∀ j, j ≠ l → L' j = L j) (hLl : L' l = (L l).erase a ∪ T)
    (hOK : ∀ j < k, GraftOK (stage M m L j) (L j) (m j)) (hlk : l < k)
    (hal : GraftOK (L l) T a)
    (hpar : ∀ j, l < j → j < k → a ≠ m j ∧ GraftOK (stage M m L j) T a ∧ Disjoint T (L j)) :
    ∀ j, l < j → j ≤ k → stage M m L' j = (stage M m L j).erase a ∪ T
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | j + 1, hj, hjk => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
    · rw [stage, stage, stage_insert_gt hL hLl hOK hlk hal hpar j hj' (by omega),
        hL j (by omega)]
      obtain ⟨hab, h₁, -⟩ := hpar j hj' (by omega)
      exact (par_eq hab h₁ (hOK j (by omega))).symm
    · subst hj'
      rw [stage, stage, stage_insert_le hL l le_rfl, hLl]
      exact seq_eq (hOK l hlk) hal

variable (x₀ : P (NS M)) (y : ∀ j, P (NS (L j))) (y' : ∀ j, P (NS (L' j))) (z : P (NS T))

lemma stg_insert_le (hL : ∀ j, j ≠ l → L' j = L j)
    (hy : ∀ j (hj : j ≠ l), y' j = castN R P (hL j hj).symm (y j)) :
    ∀ j (hj : j ≤ l), stg R P M m L' x₀ y' j =
      castN R P (stage_insert_le hL j hj).symm (stg R P M m L x₀ y j)
  | 0, _ => rfl
  | j + 1, hj => by
    rw [stg, stg, stg_insert_le hL hy j (by omega), hy j (by omega), compN_castN]
    rfl

/-- **Grafting into an operation of a total composition** grafts into the total composition. -/
lemma stg_insert_gt (hL : ∀ j, j ≠ l → L' j = L j) (hLl : L' l = (L l).erase a ∪ T)
    (hOK : ∀ j < k, GraftOK (stage M m L j) (L j) (m j)) (hlk : l < k)
    (hal : GraftOK (L l) T a) (hdl : Disjoint ((stage M m L l).erase (m l)) T)
    (hpar : ∀ j, l < j → j < k → a ≠ m j ∧ GraftOK (stage M m L j) T a ∧ Disjoint T (L j))
    (hy : ∀ j (hj : j ≠ l), y' j = castN R P (hL j hj).symm (y j))
    (hyl : y' l = castN R P hLl.symm (compN R P (L l) T a (y l) z)) :
    ∀ j (hj : l < j) (hjk : j ≤ k), stg R P M m L' x₀ y' j =
      castN R P (stage_insert_gt hL hLl hOK hlk hal hpar j hj hjk).symm
        (compN R P (stage M m L j) T a (stg R P M m L x₀ y j) z)
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | j + 1, hj, hjk => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
    · obtain ⟨hab, h₁, hTU⟩ := hpar j hj' (by omega)
      rw [stg, stg, stg_insert_gt hL hLl hOK hlk hal hdl hpar hy hyl j hj' (by omega),
        hy j (by omega), compN_castN, compN_par hab h₁ (hOK j (by omega)) hTU, castN_castN]
      rfl
    · subst hj'
      rw [stg, stg, stg_insert_le x₀ y y' hL hy l le_rfl, hyl, compN_castN]
      erw [compN_seq (hOK l hlk) hal hdl, castN_castN]
      rfl

end Insert

section Image

variable {M : Finset ℕ} {m m' : ℕ → ℕ} {L L' : ℕ → Finset ℕ} {k : ℕ} {f : ℕ → ℕ}
  {Ω : Finset ℕ}

omit [ShuffleOperad R P] in
lemma stage_image (hf : StrictMonoOn f ↑Ω) (hOK : ∀ j < k, GraftOK (stage M m L j) (L j) (m j))
    (hΩ : ∀ j ≤ k, stage M m L j ⊆ Ω) (hLΩ : ∀ j, L j ⊆ Ω) (hm' : ∀ j < k, m' j = f (m j))
    (hL' : ∀ j, L' j = (L j).image f) :
    ∀ j ≤ k, stage (M.image f) m' L' j = (stage M m L j).image f
  | 0, _ => rfl
  | j + 1, hj => by
    rw [stage, stage, stage_image hf hOK hΩ hLΩ hm' hL' j (by omega), hm' j (by omega), hL' j]
    refine image_eq (hOK j (by omega)) (hf.injOn.mono ?_)
    rw [Finset.coe_union]
    exact Set.union_subset (Finset.coe_subset.2 (hΩ j (by omega))) (Finset.coe_subset.2 (hLΩ j))

/-- **Total composition is equivariant** under strictly increasing relabellings. -/
lemma stg_image (hf : StrictMonoOn f ↑Ω) (hOK : ∀ j < k, GraftOK (stage M m L j) (L j) (m j))
    (hΩ : ∀ j ≤ k, stage M m L j ⊆ Ω) (hLΩ : ∀ j, L j ⊆ Ω) (hm' : ∀ j < k, m' j = f (m j))
    (hL' : ∀ j, L' j = (L j).image f) (x₀ : P (NS M)) (y : ∀ j, P (NS (L j)))
    (y' : ∀ j, P (NS (L' j)))
    (hy' : ∀ j, y' j = castN R P (hL' j).symm (ShuffleOperad.map (R := R)
      (relIso f (hf.mono (Finset.coe_subset.2 (hLΩ j)))) (y j))) :
    ∀ j (hj : j ≤ k), stg R P (M.image f) m' L'
      (ShuffleOperad.map (R := R) (relIso f (hf.mono (Finset.coe_subset.2
        (show M ⊆ Ω from hΩ 0 (Nat.zero_le _))))) x₀) y' j =
      castN R P (stage_image hf hOK hΩ hLΩ hm' hL' j hj).symm
        (ShuffleOperad.map (R := R) (relIso f (hf.mono (Finset.coe_subset.2 (hΩ j hj))))
          (stg R P M m L x₀ y j))
  | 0, _ => rfl
  | j + 1, hj => by
    have hU : StrictMonoOn f ↑(stage M m L j ∪ L j) := hf.mono (by
      rw [Finset.coe_union]
      exact Set.union_subset (Finset.coe_subset.2 (hΩ j (by omega)))
        (Finset.coe_subset.2 (hLΩ j)))
    rw [stg, stg, stg_image hf hOK hΩ hLΩ hm' hL' x₀ y y' hy' j (by omega), hy' j,
      compN_slot (hm' j (by omega)).symm, compN_castN, castN_castN]
    have key := map_relIso_compN (R := R) (P := P) (hOK j (by omega)) hU (stg R P M m L x₀ y j)
      (y j)
    erw [key]
    exact castN_eq_castN_castN _ _ _ _

end Image

end NatSets

/-! ## Evaluating trees -/

namespace STree

variable {E : ℕ → Type v}

/-- **The set of leaves** of a tree. -/
def lset (t : STree E) : Finset ℕ := t.labels.toFinset

lemma mem_lset {t : STree E} {a : ℕ} : a ∈ lset t ↔ a ∈ t.labels := Multiset.mem_toFinset

@[simp] lemma lset_leaf (a : ℕ) : lset (leaf a : STree E) = {a} := by
  ext n
  simp [lset]

lemma mem_lset_node {k : ℕ} {e : E k} {c : Fin k → STree E} {a : ℕ} :
    a ∈ lset (node e c) ↔ ∃ i, a ∈ lset (c i) := by
  simp only [mem_lset, mem_labels_node]

/-- The least leaves of the children, as a function on the natural numbers. -/
def cm {k : ℕ} (c : Fin k → STree E) (j : ℕ) : ℕ := if h : j < k then (c ⟨j, h⟩).first else 0

/-- The leaves of the children, as a function on the natural numbers. -/
def cL {k : ℕ} (c : Fin k → STree E) (j : ℕ) : Finset ℕ :=
  if h : j < k then lset (c ⟨j, h⟩) else ∅

/-- The least leaves of the children. -/
def cM {k : ℕ} (c : Fin k → STree E) : Finset ℕ := Finset.univ.image fun j => (c j).first

lemma cm_of {k : ℕ} (c : Fin k → STree E) {j : ℕ} (hj : j < k) : cm c j = (c ⟨j, hj⟩).first :=
  dif_pos hj

lemma cL_of {k : ℕ} (c : Fin k → STree E) {j : ℕ} (hj : j < k) : cL c j = lset (c ⟨j, hj⟩) :=
  dif_pos hj

lemma cL_of_ge {k : ℕ} (c : Fin k → STree E) {j : ℕ} (hj : k ≤ j) : cL c j = ∅ :=
  dif_neg (by omega)

/-- **A valid tree**: a shuffle tree with distinct leaves. -/
structure Valid (t : STree E) : Prop where
  shuffle : t.IsShuffle
  nodup : t.labels.Nodup

section Node

variable {k : ℕ} {e : E k} {c : Fin k → STree E} (hv : Valid (node e c))
include hv

lemma Valid.child (i : Fin k) : Valid (c i) := ⟨hv.shuffle.child i, nodup_of_node hv.nodup i⟩

lemma Valid.cm_mem {j : ℕ} (hj : j < k) : cm c j ∈ cL c j := by
  rw [cm_of c hj, cL_of c hj, mem_lset]
  exact first_mem (hv.shuffle.child _)

lemma Valid.cm_le {j : ℕ} (hj : j < k) : ∀ b ∈ cL c j, cm c j ≤ b := fun b hb => by
  rw [cL_of c hj, mem_lset] at hb
  rw [cm_of c hj]
  exact first_le (hv.shuffle.child _) b hb

lemma Valid.cm_lt {i j : ℕ} (hij : i < j) (hj : j < k) : cm c i < cm c j := by
  rw [cm_of c (hij.trans hj), cm_of c hj]
  exact hv.shuffle.mono (show (⟨i, hij.trans hj⟩ : Fin k) < ⟨j, hj⟩ from hij)

lemma Valid.cm_inj {i j : ℕ} (hi : i < k) (hj : j < k) (h : cm c i = cm c j) : i = j := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact absurd h (hv.cm_lt hij hj).ne
  · rfl
  · exact absurd h (hv.cm_lt hij hi).ne'

lemma Valid.disj_cL {i j : ℕ} (hij : i ≠ j) : Disjoint (cL c i) (cL c j) := by
  by_cases hi : i < k
  · by_cases hj : j < k
    · rw [cL_of c hi, cL_of c hj]
      refine Finset.disjoint_left.2 fun n hn hn' => ?_
      rw [mem_lset] at hn hn'
      exact not_mem_of_node hv.nodup (fun h => hij (congrArg Fin.val h)) hn hn'
    · rw [cL_of_ge c (not_lt.1 hj)]
      exact Finset.disjoint_empty_right _
  · rw [cL_of_ge c (not_lt.1 hi)]
    exact Finset.disjoint_empty_left _

lemma Valid.cm_notMem {i j : ℕ} (hij : i ≠ j) (hi : i < k) : cm c i ∉ cL c j :=
  Finset.disjoint_left.1 (hv.disj_cL hij) (hv.cm_mem hi)

/-- **The stages of the evaluation of a node**: the least leaves of the children not yet grafted,
and the leaves of the grafted ones. -/
lemma Valid.stage_eq : ∀ j ≤ k, stage (cM c) (cm c) (cL c) j =
    (Finset.Ico j k).image (cm c) ∪ (Finset.range j).biUnion (cL c)
  | 0, _ => by
    ext n
    simp only [stage, cM, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_Ico, Finset.range_zero, Finset.biUnion_empty, Finset.notMem_empty, or_false]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, ⟨Nat.zero_le _, j.2⟩, cm_of c j.2⟩
    · rintro ⟨j, ⟨-, hj⟩, rfl⟩
      exact ⟨⟨j, hj⟩, (cm_of c hj).symm⟩
  | j + 1, hj => by
    rw [stage, Valid.stage_eq j (by omega)]
    ext n
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_image, Finset.mem_Ico,
      Finset.mem_biUnion, Finset.mem_range]
    constructor
    · rintro (⟨hn, (⟨i, ⟨hji, hik⟩, rfl⟩ | ⟨i, hij, hni⟩)⟩ | hn)
      · refine Or.inl ⟨i, ⟨?_, hik⟩, rfl⟩
        rcases Nat.lt_or_eq_of_le hji with h | rfl
        · exact h
        · exact absurd rfl hn
      · exact Or.inr ⟨i, by omega, hni⟩
      · exact Or.inr ⟨j, by omega, hn⟩
    · rintro (⟨i, ⟨hji, hik⟩, rfl⟩ | ⟨i, hij, hni⟩)
      · exact Or.inl ⟨fun h => absurd (hv.cm_inj hik (by omega) h) (by omega),
          Or.inl ⟨i, ⟨by omega, hik⟩, rfl⟩⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hij | rfl
        · refine Or.inl ⟨fun h => ?_, Or.inr ⟨i, hij, hni⟩⟩
          subst h
          exact hv.cm_notMem (by omega : j ≠ i) (by omega) hni
        · exact Or.inr hni

omit hv in
lemma lset_node_eq : lset (node e c) = (Finset.range k).biUnion (cL c) := by
  ext n
  simp only [mem_lset_node, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, i.2, by rwa [cL_of c i.2]⟩
  · rintro ⟨i, hi, hn⟩
    exact ⟨⟨i, hi⟩, by rwa [cL_of c hi] at hn⟩

lemma Valid.stage_k : stage (cM c) (cm c) (cL c) k = lset (node e c) := by
  rw [hv.stage_eq k le_rfl, lset_node_eq, Finset.Ico_self, Finset.image_empty, Finset.empty_union]

lemma Valid.stage_sub {j : ℕ} (hj : j ≤ k) : stage (cM c) (cm c) (cL c) j ⊆ lset (node e c) := by
  rw [hv.stage_eq j hj, lset_node_eq]
  intro n hn
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Ico, Finset.mem_biUnion,
    Finset.mem_range] at hn ⊢
  rcases hn with ⟨i, ⟨-, hik⟩, rfl⟩ | ⟨i, hij, hni⟩
  · exact ⟨i, hik, hv.cm_mem hik⟩
  · exact ⟨i, by omega, hni⟩

omit hv in
lemma cL_sub (j : ℕ) : cL c j ⊆ lset (node e c) := by
  by_cases hj : j < k
  · rw [lset_node_eq]
    intro n hn
    exact Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 hj, hn⟩
  · rw [cL_of_ge c (not_lt.1 hj)]
    exact Finset.empty_subset _

/-- **The grafting conditions at every stage** of the evaluation of a node. -/
lemma Valid.graftOK {j : ℕ} (hj : j < k) :
    GraftOK (stage (cM c) (cm c) (cL c) j) (cL c j) (cm c j) where
  mem := by
    rw [hv.stage_eq j hj.le]
    exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨j, Finset.mem_Ico.2 ⟨le_rfl, hj⟩, rfl⟩)
  memT := hv.cm_mem hj
  le := hv.cm_le hj
  disj := by
    rw [hv.stage_eq j hj.le]
    refine Finset.disjoint_left.2 fun n hn hn' => ?_
    obtain ⟨hne, hn⟩ := Finset.mem_erase.1 hn
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Ico, Finset.mem_biUnion,
      Finset.mem_range] at hn
    rcases hn with ⟨i, ⟨hji, hik⟩, rfl⟩ | ⟨i, hij, hni⟩
    · exact hv.cm_notMem (fun h => hne (congrArg (cm c) h)) hik hn'
    · exact Finset.disjoint_left.1 (hv.disj_cL (by omega : i ≠ j)) hni hn'

end Node

lemma lset_subst_update {s t : STree E} {a : ℕ} (ha : a ∈ lset s) :
    lset (s.subst (Function.update leaf a t)) = (lset s).erase a ∪ lset t := by
  ext n
  simp only [lset, Multiset.mem_toFinset, labels_subst, Multiset.mem_bind, Finset.mem_union,
    Finset.mem_erase] at ha ⊢
  constructor
  · rintro ⟨b, hb, hn⟩
    by_cases hba : b = a
    · subst hba
      rw [Function.update_self] at hn
      exact Or.inr hn
    · rw [Function.update_of_ne hba, labels_leaf, Multiset.mem_singleton] at hn
      subst hn
      exact Or.inl ⟨hba, hb⟩
  · rintro (⟨hna, hn⟩ | hn)
    · exact ⟨n, hn, by
        rw [Function.update_of_ne hna, labels_leaf]
        exact Multiset.mem_singleton_self n⟩
    · exact ⟨a, ha, by rw [Function.update_self]; exact hn⟩

/-- **Grafting valid trees** gives a valid tree. -/
lemma Valid.subst_update {s t : STree E} (hs : Valid s) (ht : Valid t) {a : ℕ} (ha : a ∈ lset s)
    (hta : t.first = a) (hd : Disjoint ((lset s).erase a) (lset t)) :
    Valid (s.subst (Function.update leaf a t)) := by
  have hfirst : ∀ b, (Function.update leaf a t b).first = b := fun b => by
    by_cases hba : b = a
    · subst hba
      rw [Function.update_self, hta]
    · rw [Function.update_of_ne hba, first_leaf]
  refine ⟨isShuffle_subst hs.shuffle (fun b _ => ?_) fun b _ b' _ h => ?_, ?_⟩
  · by_cases hba : b = a
    · subst hba
      rw [Function.update_self]
      exact ht.shuffle
    · rw [Function.update_of_ne hba]
      exact isShuffle_leaf _
  · simp only [hfirst]
    exact h
  · rw [labels_subst, Multiset.nodup_bind]
    refine ⟨fun b _ => ?_, Multiset.Nodup.pairwise (fun b hb b' hb' hbb' => ?_) hs.nodup⟩
    · by_cases hba : b = a
      · subst hba
        rw [Function.update_self]
        exact ht.nodup
      · rw [Function.update_of_ne hba, labels_leaf]
        exact Multiset.nodup_singleton _
    · have key : ∀ x, x ∈ s.labels → x ≠ a → ∀ n ∈ (Function.update leaf a t x).labels,
          n = x := fun x _ hxa n hn => by
        rw [Function.update_of_ne hxa, labels_leaf, Multiset.mem_singleton] at hn
        exact hn
      refine Multiset.disjoint_left.2 fun hn hn' => ?_
      beta_reduce at hn hn'
      by_cases hba : b = a
      · subst hba
        rw [Function.update_self] at hn
        have hb'a : b' ≠ b := Ne.symm hbb'
        have := key b' hb' hb'a _ hn'
        subst this
        exact Finset.disjoint_left.1 hd (Finset.mem_erase.2 ⟨hb'a, mem_lset.2 hb'⟩)
          (mem_lset.2 hn)
      · by_cases hb'a : b' = a
        · subst hb'a
          rw [Function.update_self] at hn'
          have := key b hb hba _ hn
          subst this
          exact Finset.disjoint_left.1 hd (Finset.mem_erase.2 ⟨hba, mem_lset.2 hb⟩)
            (mem_lset.2 hn')
        · exact hbb' ((key b hb hba _ hn).symm.trans (key b' hb' hb'a _ hn'))

end STree

open STree

section Eval

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [LinearOrder A] → Type w}
  [∀ (A : Type) [Fintype A] [LinearOrder A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [LinearOrder A], Module R (P A)] [ShuffleOperad R P]
  {E : ℕ → Type v}

variable (R P) in
/-- An operation with ordered inputs `Fin k`, on a set of `k` natural numbers. -/
noncomputable def corVal {k : ℕ} (M : Finset ℕ) (x : P (Fin k)) : P (NS M) :=
  if h : Fintype.card (NS M) = k then ShuffleOperad.map (R := R) (monoEquivOfFin (NS M) h) x
  else 0

lemma corVal_congr {k : ℕ} {M M' : Finset ℕ} (h : M = M') (x : P (Fin k)) :
    corVal R P M' x = castN R P h (corVal R P M x) := by
  subst h
  rfl

variable (R P) in
/-- **The evaluation of a tree** in a shuffle operad, given the values `φ` of the generators: a
leaf is the unit, and a node is the total composition of its generator, on the least leaves of
its children, with the evaluations of its children. -/
noncomputable def ev (φ : ∀ k, E k → P (Fin k)) : (t : STree E) → P (NS (lset t))
  | leaf a => castN R P (lset_leaf a).symm (oneN R P a)
  | @node _ k g c =>
    if h : stage (cM c) (cm c) (cL c) k = lset (node g c) then
      castN R P h (stg R P (cM c) (cm c) (cL c) (corVal R P (cM c) (φ k g))
        (fun j => if hj : j < k then castN R P (cL_of c hj).symm (ev φ (c ⟨j, hj⟩)) else 0) k)
    else 0

variable (R P) in
/-- The evaluations of the children of a node. -/
noncomputable def evc (φ : ∀ k, E k → P (Fin k)) {k : ℕ} (c : Fin k → STree E) (j : ℕ) :
    P (NS (cL c j)) :=
  if hj : j < k then castN R P (cL_of c hj).symm (ev R P φ (c ⟨j, hj⟩)) else 0

variable (φ : ∀ k, E k → P (Fin k))

lemma ev_leaf (a : ℕ) : ev R P φ (leaf a) = castN R P (lset_leaf a).symm (oneN R P a) := rfl

lemma ev_node {k : ℕ} {g : E k} {c : Fin k → STree E} (hv : Valid (node g c)) :
    ev R P φ (node g c) = castN R P hv.stage_k
      (stg R P (cM c) (cm c) (cL c) (corVal R P (cM c) (φ k g)) (evc R P φ c) k) := by
  rw [ev, dif_pos hv.stage_k]
  rfl

lemma ev_congr {t t' : STree E} (h : t = t') :
    ev R P φ t = castN R P (congrArg lset h).symm (ev R P φ t') := by
  subst h
  rfl

lemma stg_congr {M M' : Finset ℕ} {m m' : ℕ → ℕ} {L : ℕ → Finset ℕ} (hM : M = M') (hm : m = m')
    (x₀ : P (NS M)) (y : ∀ j, P (NS (L j))) (j : ℕ) :
    stg R P M' m' L (castN R P hM x₀) y j =
      castN R P (by subst hM hm; rfl) (stg R P M m L x₀ y j) := by
  subst hM hm
  rfl

/-- **Evaluation respects grafting**: the evaluation of a valid tree grafted at a leaf is the
canonical grafting of the evaluations. -/
theorem ev_subst : ∀ {s : STree E} (_hs : Valid s) {t : STree E} (_ht : Valid t) {a : ℕ}
    (ha : a ∈ lset s) (_hta : t.first = a) (_hd : Disjoint ((lset s).erase a) (lset t)),
    ev R P φ (s.subst (Function.update leaf a t)) =
      castN R P (lset_subst_update ha).symm
        (compN R P (lset s) (lset t) a (ev R P φ s) (ev R P φ t))
  | leaf b, _, t, ht, a, ha, hta, _ => by
    rw [lset_leaf, Finset.mem_singleton] at ha
    subst ha
    have hat : a ∈ lset t := mem_lset.2 (hta ▸ first_mem ht.shuffle)
    have hle : ∀ n ∈ lset t, a ≤ n := fun n hn => hta ▸ first_le ht.shuffle n (mem_lset.1 hn)
    rw [ev_congr φ (show (leaf a : STree E).subst (Function.update leaf a t) = t by simp),
      ev_leaf, ← castN_rfl (R := R) (ev R P φ t), compN_castN, compN_one_left hat hle,
      castN_castN, castN_castN, castN_castN]
  | @node _ k g c, hs, t, ht, a, ha, hta, hd => by
    obtain ⟨l, hal⟩ := mem_lset_node.1 ha
    have hsub : (node g c).subst (Function.update leaf a t) =
        node g fun j => (c j).subst (Function.update leaf a t) := rfl
    have hv' : Valid (node g fun j => (c j).subst (Function.update leaf a t)) :=
      hsub ▸ hs.subst_update ht ha hta hd
    set c' : Fin k → STree E := fun j => (c j).subst (Function.update leaf a t) with hc'
    -- the children other than `l` are unchanged, and so are the least leaves
    have hc'j : ∀ j : Fin k, j ≠ l → c' j = c j := fun j hj => by
      show (c j).subst _ = c j
      conv_rhs => rw [← subst_leaf (c j)]
      refine subst_congr _ fun b hb => Function.update_of_ne ?_ _ _
      rintro rfl
      exact not_mem_of_node hs.nodup (Ne.symm hj) (mem_lset.1 hal) hb
    have hfirst : ∀ j : Fin k, (c' j).first = (c j).first := fun j => by
      show ((c j).subst _).first = _
      rw [first_subst (hs.child j).shuffle]
      by_cases h : (c j).first = a
      · rw [h, Function.update_self, hta]
      · rw [Function.update_of_ne h, first_leaf]
    have hM : cM c = cM c' := by simp only [cM, hfirst]
    have hm : cm c = cm c' := funext fun j => by
      unfold cm
      split_ifs with hj
      · exact (hfirst ⟨j, hj⟩).symm
      · rfl
    -- the leaves
    have hat : a ∈ lset t := mem_lset.2 (hta ▸ first_mem ht.shuffle)
    have hle : ∀ n ∈ lset t, a ≤ n := fun n hn => hta ▸ first_le ht.shuffle n (mem_lset.1 hn)
    have hsubs : ∀ j, cL c j ⊆ lset (node g c) := fun j => cL_sub j
    have hL : ∀ j, j ≠ l.1 → cL c' j = cL c j := fun j hj => by
      by_cases hjk : j < k
      · rw [cL_of c' hjk, cL_of c hjk, hc'j ⟨j, hjk⟩ (fun h => hj (congrArg Fin.val h))]
      · rw [cL_of_ge c' (not_lt.1 hjk), cL_of_ge c (not_lt.1 hjk)]
    have hLl : cL c' l.1 = (cL c l.1).erase a ∪ lset t := by
      rw [cL_of c' l.2, cL_of c l.2]
      exact lset_subst_update hal
    have haL : a ∈ cL c l.1 := by rwa [cL_of c l.2]
    have hnot : ∀ j, j ≠ l.1 → a ∉ cL c j := fun j hj h =>
      Finset.disjoint_left.1 (hs.disj_cL hj) h haL
    have hsubE : ∀ j, j ≠ l.1 → cL c j ⊆ (lset (node g c)).erase a := fun j hj n hn =>
      Finset.mem_erase.2 ⟨fun h => hnot j hj (h ▸ hn), hsubs j hn⟩
    have hal' : GraftOK (cL c l.1) (lset t) a := ⟨haL, hat, hle,
      Finset.disjoint_of_subset_left (Finset.erase_subset_erase a (hsubs l.1)) hd⟩
    have hdl : Disjoint ((stage (cM c) (cm c) (cL c) l.1).erase (cm c l.1)) (lset t) := by
      refine Finset.disjoint_of_subset_left (fun n hn => ?_) hd
      obtain ⟨hn₁, hn₂⟩ := Finset.mem_erase.1 hn
      refine Finset.mem_erase.2 ⟨fun h => ?_, hs.stage_sub l.2.le hn₂⟩
      subst h
      rw [hs.stage_eq l.1 l.2.le] at hn₂
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Ico, Finset.mem_biUnion,
        Finset.mem_range] at hn₂
      rcases hn₂ with ⟨i, ⟨hli, hik⟩, hi⟩ | ⟨i, hil, hni⟩
      · rcases Nat.lt_or_eq_of_le hli with h | rfl
        · exact hnot i (by omega) (hi ▸ hs.cm_mem hik)
        · exact hn₁ hi.symm
      · exact hnot i (by omega) hni
    have hpar : ∀ j, l.1 < j → j < k → a ≠ cm c j ∧
        GraftOK (stage (cM c) (cm c) (cL c) j) (lset t) a ∧ Disjoint (lset t) (cL c j) := by
      intro j hlj hjk
      refine ⟨fun h => hnot j (by omega) (h ▸ hs.cm_mem hjk), ⟨?_, hat, hle, ?_⟩,
        Finset.disjoint_of_subset_right (hsubE j (by omega)) hd.symm⟩
      · rw [hs.stage_eq j hjk.le]
        exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨l.1, Finset.mem_range.2 hlj, haL⟩)
      · exact Finset.disjoint_of_subset_left (Finset.erase_subset_erase a (hs.stage_sub hjk.le)) hd
    have hy : ∀ j (hj : j ≠ l.1), evc R P φ c' j = castN R P (hL j hj).symm (evc R P φ c j) := by
      intro j hj
      unfold evc
      split_ifs with hjk
      · rw [ev_congr φ (hc'j ⟨j, hjk⟩ fun h => hj (congrArg Fin.val h)), castN_castN, castN_castN]
      · rw [map_zero]
    have hyl : evc R P φ c' l.1 = castN R P hLl.symm
        (compN R P (cL c l.1) (lset t) a (evc R P φ c l.1) (ev R P φ t)) := by
      unfold evc
      rw [dif_pos l.2, dif_pos l.2]
      have ih := ev_subst (hs.child l) ht hal hta
        (Finset.disjoint_of_subset_left (Finset.erase_subset_erase a (hsubs l.1)) hd |>.mono_left
          (by rw [cL_of c l.2]))
      rw [ev_congr φ (show c' ⟨l.1, l.2⟩ = (c l).subst (Function.update leaf a t) from rfl), ih,
        castN_castN, castN_castN, ← castN_rfl (R := R) (ev R P φ t), compN_castN, castN_castN]
      rfl
    rw [ev_congr φ hsub, ev_node φ hv', corVal_congr hM, stg_congr hM hm,
      stg_insert_gt _ _ _ _ hL hLl (fun j hj => hs.graftOK hj) l.2 hal' hdl hpar hy hyl k l.2
        le_rfl, ev_node φ hs, ← castN_rfl (R := R) (ev R P φ t), compN_castN]
    simp only [castN_castN]
    rfl

lemma castN_eq_map {S S' : Finset ℕ} (h : S = S') (x : P (NS S)) :
    castN R P h x = ShuffleOperad.map (R := R) (eqIso h) x := by
  subst h
  rw [map_eq_map (eqIso rfl) (OrderIso.refl _), ShuffleOperad.map_refl]
  rfl

lemma map_relIso_castN {S S' : Finset ℕ} (h : S = S') {f : ℕ → ℕ} (hf : StrictMonoOn f ↑S')
    (x : P (NS S)) :
    ShuffleOperad.map (R := R) (relIso f hf) (castN R P h x) =
      castN R P (by rw [h]) (ShuffleOperad.map (R := R) (relIso f (h ▸ hf)) x) := by
  subst h
  rfl

lemma STree.lset_relabel (f : ℕ → ℕ) (t : STree E) : lset (t.relabel f) = (lset t).image f := by
  rw [lset, lset, labels_relabel, Multiset.toFinset_map]

lemma STree.Valid.relabel {t : STree E} (ht : Valid t) {f : ℕ → ℕ}
    (hf : StrictMonoOn f ↑(lset t)) : Valid (t.relabel f) := by
  refine ⟨isShuffle_relabel ht.shuffle fun a ha b hb h => hf (mem_lset.2 ha) (mem_lset.2 hb) h, ?_⟩
  rw [labels_relabel]
  exact Multiset.Nodup.map_on (fun a ha b hb h => hf.injOn (mem_lset.2 ha) (mem_lset.2 hb) h)
    ht.nodup

lemma corVal_relabel {k : ℕ} {M : Finset ℕ} {f : ℕ → ℕ} (hf : StrictMonoOn f ↑M) (x : P (Fin k)) :
    corVal R P (M.image f) x = ShuffleOperad.map (R := R) (relIso f hf) (corVal R P M x) := by
  have hcard : Fintype.card (NS (M.image f)) = Fintype.card (NS M) := by
    simp only [Fintype.card_coe]
    exact Finset.card_image_of_injOn hf.injOn
  unfold corVal
  by_cases h : Fintype.card (NS M) = k
  · rw [dif_pos (hcard.trans h), dif_pos h, ← ShuffleOperad.map_trans]
    exact map_eq_map _ _ _
  · rw [dif_neg (fun h' => h (hcard.symm.trans h')), dif_neg h, map_zero]

/-- **Evaluation is equivariant** under strictly increasing relabellings of the leaves. -/
theorem ev_relabel : ∀ {t : STree E} (_ht : Valid t) {f : ℕ → ℕ} (hf : StrictMonoOn f ↑(lset t)),
    ev R P φ (t.relabel f) = castN R P (lset_relabel f t).symm
      (ShuffleOperad.map (R := R) (relIso f hf) (ev R P φ t))
  | leaf a, _, f, hf => by
    rw [ev_congr φ (show (leaf a : STree E).relabel f = leaf (f a) from rfl), ev_leaf, ev_leaf,
      oneN, oneN]
    simp only [castN_eq_map, ← ShuffleOperad.map_trans]
    exact map_eq_map _ _ _
  | @node _ k g c, hv, f, hf => by
    have hv'' := hv.relabel hf
    have hsub : (node g c).relabel f = node g fun j => (c j).relabel f := rfl
    rw [hsub] at hv''
    set c'' : Fin k → STree E := fun j => (c j).relabel f with hc''
    have hcf : ∀ j : Fin k, StrictMonoOn f ↑(lset (c j)) := fun j =>
      hf.mono (Finset.coe_subset.2 fun n hn => mem_lset_node.2 ⟨j, hn⟩)
    have hM : (cM c).image f = cM c'' := by
      simp only [cM, Finset.image_image]
      congr 1
      funext j
      exact (first_relabel f (hv.child j).shuffle).symm
    have hm : ∀ j < k, cm c'' j = f (cm c j) := fun j hj => by
      rw [cm_of c'' hj, cm_of c hj]
      exact first_relabel f (hv.child _).shuffle
    have hL : ∀ j, cL c'' j = (cL c j).image f := fun j => by
      by_cases hj : j < k
      · rw [cL_of c'' hj, cL_of c hj]
        exact lset_relabel f _
      · rw [cL_of_ge c'' (not_lt.1 hj), cL_of_ge c (not_lt.1 hj), Finset.image_empty]
    have hLΩ : ∀ j, cL c j ⊆ lset (node g c) := fun j => cL_sub j
    have hy : ∀ j, evc R P φ c'' j = castN R P (hL j).symm (ShuffleOperad.map (R := R)
        (relIso f (hf.mono (Finset.coe_subset.2 (hLΩ j)))) (evc R P φ c j)) := fun j => by
      unfold evc
      split_ifs with hj
      · rw [ev_congr φ (show c'' ⟨j, hj⟩ = (c ⟨j, hj⟩).relabel f from rfl),
          ev_relabel (hv.child _) (hcf _), map_relIso_castN, castN_castN, castN_castN,
          castN_castN]
      · rw [map_zero, map_zero]
    have hcM : StrictMonoOn f ↑(cM c) := hf.mono (Finset.coe_subset.2 (hv.stage_sub (j := 0)
      (Nat.zero_le _)))
    rw [ev_congr φ hsub, ev_node φ hv'', corVal_congr hM, corVal_relabel hcM, stg_congr hM rfl,
      stg_image hf (fun j hj => hv.graftOK hj) (fun j hj => hv.stage_sub hj) hLΩ hm hL _ _ _ hy k
        le_rfl, ev_node φ hv, map_relIso_castN, castN_castN, castN_castN, castN_castN]
    exact castN_eq_castN_castN _ _ _ _

end Eval

end Operad
