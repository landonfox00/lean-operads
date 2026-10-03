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

end NatSets

end Operad
