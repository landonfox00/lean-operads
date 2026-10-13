/-
# Algebras over presented operads

An algebra over a symmetric operad `P` on a module `V` is a morphism `P → EndOp R V` into the
endomorphism operad (`Sym.SymAlgebra`). For the operads with a presentation in the library, this
file identifies the algebras with the expected structures, binary multilinear operations on `V`
satisfying identities:

* `Com.algebraEquiv`: commutative associative algebras (non-unital);
* `Perm.algebraEquiv`: permutative algebras, `(xy)z = x(yz) = x(zy)`;
* `Ass.algebraEquiv`: associative algebras (non-unital);
* `Dias.algebraEquiv`: Loday's associative dialgebras;
* `Trias.algebraEquiv`: Loday and Ronco's associative trialgebras;
* `ComTrias.algebraEquiv`: Vallette's commutative trialgebras.

The computations are those of binary composites in the endomorphism operad
(`EndOp.ap_bin`, and `EndOp.leftComb_eq_rightComb_iff` for the underlying planar operad), which
turn the relations of the presentations into identities.
-/
import Operad.EndOperad
import Operad.PermPres
import Operad.AssPres
import Operad.DiasTrias
import Operad.ComTriasPres

universe u v

namespace Operad

open Sym SetOperad NSSetOperad NSSetOperad.Arr

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

namespace EndOp

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The value of an operation of the underlying set operad of `EndOp R V`. -/
def ap (x : Und R (EndOp R V) A) (w : A → V) : V := ((Und.of R (EndOp R V)).symm x) w

lemma ext_ap {x y : Und R (EndOp R V) A} (h : ∀ w, ap x w = ap y w) : x = y :=
  (Und.of R (EndOp R V)).symm.injective (MultilinearMap.ext h)

@[simp] lemma ap_map (e : A ≃ B) (x : Und R (EndOp R V) A) (w : B → V) :
    ap (map e x) w = ap x fun a => w (e a) := rfl

@[simp] lemma ap_one (w : Unit → V) : ap (one : Und R (EndOp R V) Unit) w = w () := rfl

lemma ap_comp (i : A) (x : Und R (EndOp R V) A) (y : Und R (EndOp R V) B)
    (w : Without A i ⊕ B → V) :
    ap (comp i x y) w = ap x (feed i w (ap y fun b => w (Sum.inr b))) := rfl

/-- **A binary operation filled with `x` and `y`.** -/
lemma ap_bin (g : Und R (EndOp R V) (Fin 2)) (x : Und R (EndOp R V) A)
    (y : Und R (EndOp R V) B) (w : A ⊕ B → V) :
    ap (bin g x y) w = ap g ![ap x fun a => w (Sum.inl a), ap y fun b => w (Sum.inr b)] := by
  unfold SetOperad.bin
  rw [ap_map, ap_comp, ap_comp]
  congr 1
  funext k
  fin_cases k <;> rfl

omit [AddCommGroup V] in
lemma vec_two (w : Fin 2 → V) : w = ![w 0, w 1] := by
  funext k
  fin_cases k <;> rfl

omit [AddCommGroup V] in
@[simp] lemma vec_swap (x y : V) : (fun a => ![x, y] (Equiv.swap (0 : Fin 2) 1 a)) = ![y, x] := by
  funext k
  fin_cases k <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right]

/-- **Commutativity** of a binary operation, as an identity. -/
theorem isComm_iff (g : Und R (EndOp R V) (Fin 2)) :
    IsComm g ↔ ∀ x y, ap g ![x, y] = ap g ![y, x] := by
  constructor
  · intro h x y
    conv_lhs => rw [← h]
    rw [ap_map]
    congr 1
    funext k
    fin_cases k <;> rfl
  · intro h
    refine ext_ap fun w => ?_
    rw [ap_map, vec_two w, h]
    congr 1
    funext k
    fin_cases k <;> rfl

/-- **Associativity** of a binary operation, as an identity. -/
theorem isAssoc_iff (g : Und R (EndOp R V) (Fin 2)) :
    IsAssoc g ↔ ∀ x y z, ap g ![ap g ![x, y], z] = ap g ![x, ap g ![y, z]] := by
  constructor
  · intro h x y z
    have := congrArg (fun t => ap t (Sum.elim (fun _ => x) (Sum.elim (fun _ => y) fun _ => z))) h
    simpa [ap_bin] using this
  · intro h
    refine ext_ap fun w => ?_
    simp only [ap_map, ap_bin, ap_one]
    exact h _ _ _

/-- The second permutative relation, as an identity. -/
theorem r2b_iff (g : Und R (EndOp R V) (Fin 2)) :
    bin g one (bin g one one) = bin g one (bin (map (Equiv.swap 0 1) g) one one) ↔
      ∀ x y z, ap g ![x, ap g ![y, z]] = ap g ![x, ap g ![z, y]] := by
  constructor
  · intro h x y z
    have := congrArg (fun t => ap t (Sum.elim (fun _ => x) (Sum.elim (fun _ => y) fun _ => z))) h
    simpa only [ap_bin, ap_one, ap_map, vec_swap, Sum.elim_inl, Sum.elim_inr] using this
  · intro h
    refine ext_ap fun w => ?_
    simp only [ap_bin, ap_one, ap_map, vec_swap]
    exact h _ _ _

/-- **A left comb equals a right comb**, as an identity. -/
theorem assocShape_iff (g h g' h' : Und R (EndOp R V) (Fin 2)) :
    map (Equiv.sumAssoc Unit Unit Unit) (bin g (bin h one one) one) = bin g' one (bin h' one one)
      ↔ ∀ x y z, ap g ![ap h ![x, y], z] = ap g' ![x, ap h' ![y, z]] := by
  constructor
  · intro hgh x y z
    have := congrArg (fun t => ap t (Sum.elim (fun _ => x) (Sum.elim (fun _ => y) fun _ => z)))
      hgh
    simpa [ap_bin] using this
  · intro hgh
    refine ext_ap fun w => ?_
    simp only [ap_map, ap_bin, ap_one]
    exact hgh _ _ _

/-- **Two right combs are equal**, as an identity. -/
theorem rightShape_iff (g h g' h' : Und R (EndOp R V) (Fin 2)) :
    bin g one (bin h one one) = bin g' one (bin h' one one)
      ↔ ∀ x y z, ap g ![x, ap h ![y, z]] = ap g' ![x, ap h' ![y, z]] := by
  constructor
  · intro hgh x y z
    have := congrArg (fun t => ap t (Sum.elim (fun _ => x) (Sum.elim (fun _ => y) fun _ => z)))
      hgh
    simpa [ap_bin] using this
  · intro hgh
    refine ext_ap fun w => ?_
    simp only [ap_bin, ap_one]
    exact hgh _ _ _

/-- **A planar two-fold composite**, `p (q (x, y), z)` and `p (x, q (y, z))`. -/
theorem leftComb_eq_rightComb_iff (p q p' q' : toNSSet (Und R (EndOp R V)) 2) :
    leftComb p q = rightComb p' q' ↔
      ∀ x y z, ap p ![ap q ![x, y], z] = ap p' ![x, ap q' ![y, z]] := by
  have hl : ∀ w : Fin 3 → V, ap (NSSetOperad.comp 0 1 p q : toNSSet (Und R (EndOp R V)) 3) w
      = ap p ![ap q ![w 0, w 1], w 2] := fun w => by
    show ap (map _ (comp _ p q)) w = _
    rw [ap_map, ap_comp]
    congr 1
    funext k
    fin_cases k
    · show ap q _ = ap q _
      congr 1
      funext b
      fin_cases b <;> rfl
    · rfl
  have hr : ∀ w : Fin 3 → V, ap (NSSetOperad.comp 1 0 p' q' : toNSSet (Und R (EndOp R V)) 3) w
      = ap p' ![w 0, ap q' ![w 1, w 2]] := fun w => by
    show ap (map _ (comp _ p' q')) w = _
    rw [ap_map, ap_comp]
    congr 1
    funext k
    fin_cases k
    · rfl
    · show ap q' _ = ap q' _
      congr 1
      funext b
      fin_cases b <;> rfl
  rw [leftComb_eq, rightComb_eq]
  constructor
  · intro h x y z
    have h' := mk_eq_mk_iff.1 h
    have := congrArg (fun t => ap t ![x, y, z]) h'
    simp only at this
    rw [hl, hr] at this
    exact this
  · intro h
    refine mk_eq_mk_iff.2 (ext_ap fun w => ?_)
    rw [hl, hr]
    exact h _ _ _

end EndOp

/-! ## The algebras -/

variable (R V)

/-- **A commutative associative algebra structure** on `V`, without unit. -/
structure ComAlg where
  /-- The product. -/
  mul : EndOp R V (Fin 2)
  comm : ∀ x y, mul ![x, y] = mul ![y, x]
  assoc : ∀ x y z, mul ![mul ![x, y], z] = mul ![x, mul ![y, z]]

/-- **A permutative algebra structure** on `V`: `(xy)z = x(yz) = x(zy)`. -/
structure PermAlg where
  /-- The product. -/
  mul : EndOp R V (Fin 2)
  assoc : ∀ x y z, mul ![mul ![x, y], z] = mul ![x, mul ![y, z]]
  perm : ∀ x y z, mul ![x, mul ![y, z]] = mul ![x, mul ![z, y]]

/-- **An associative algebra structure** on `V`, without unit. -/
structure AssAlg where
  /-- The product. -/
  mul : EndOp R V (Fin 2)
  assoc : ∀ x y z, mul ![mul ![x, y], z] = mul ![x, mul ![y, z]]

/-- **An associative dialgebra structure** on `V` (Loday): `⊣` and `⊢` with
`(x ⊣ y) ⊣ z = x ⊣ (y ⊣ z) = x ⊣ (y ⊢ z)`, `(x ⊢ y) ⊣ z = x ⊢ (y ⊣ z)`,
`(x ⊣ y) ⊢ z = x ⊢ (y ⊢ z) = (x ⊢ y) ⊢ z`. -/
structure DiAlg where
  /-- `x ⊣ y`. -/
  left : EndOp R V (Fin 2)
  /-- `x ⊢ y`. -/
  right : EndOp R V (Fin 2)
  d1 : ∀ x y z, left ![left ![x, y], z] = left ![x, left ![y, z]]
  d2 : ∀ x y z, left ![left ![x, y], z] = left ![x, right ![y, z]]
  d3 : ∀ x y z, left ![right ![x, y], z] = right ![x, left ![y, z]]
  d4 : ∀ x y z, right ![left ![x, y], z] = right ![x, right ![y, z]]
  d5 : ∀ x y z, right ![right ![x, y], z] = right ![x, right ![y, z]]

/-- **An associative trialgebra structure** on `V` (Loday and Ronco): `⊣`, `⊢`, `⊥` with the
eleven identities of `TriasRel`. -/
structure TriAlg where
  /-- `x ⊣ y`. -/
  left : EndOp R V (Fin 2)
  /-- `x ⊢ y`. -/
  right : EndOp R V (Fin 2)
  /-- `x ⊥ y`. -/
  middle : EndOp R V (Fin 2)
  t1 : ∀ x y z, left ![left ![x, y], z] = left ![x, left ![y, z]]
  t2 : ∀ x y z, left ![left ![x, y], z] = left ![x, right ![y, z]]
  t3 : ∀ x y z, left ![right ![x, y], z] = right ![x, left ![y, z]]
  t4 : ∀ x y z, right ![left ![x, y], z] = right ![x, right ![y, z]]
  t5 : ∀ x y z, right ![right ![x, y], z] = right ![x, right ![y, z]]
  t6 : ∀ x y z, left ![left ![x, y], z] = left ![x, middle ![y, z]]
  t7 : ∀ x y z, left ![middle ![x, y], z] = middle ![x, left ![y, z]]
  t8 : ∀ x y z, middle ![left ![x, y], z] = middle ![x, right ![y, z]]
  t9 : ∀ x y z, middle ![right ![x, y], z] = right ![x, middle ![y, z]]
  t10 : ∀ x y z, right ![middle ![x, y], z] = right ![x, right ![y, z]]
  t11 : ∀ x y z, middle ![middle ![x, y], z] = middle ![x, middle ![y, z]]

/-- **A commutative trialgebra structure** on `V` (Vallette): `⊥` commutative and associative,
and `⊣` with `(x ⊣ y) ⊣ z = x ⊣ (y ⊣ z) = x ⊣ (z ⊣ y)`, `x ⊣ (y ⊥ z) = x ⊣ (y ⊣ z)`,
`(x ⊥ y) ⊣ z = x ⊥ (y ⊣ z)`. -/
structure ComTriAlg where
  /-- `x ⊥ y`. -/
  mid : EndOp R V (Fin 2)
  /-- `x ⊣ y`. -/
  left : EndOp R V (Fin 2)
  comm : ∀ x y, mid ![x, y] = mid ![y, x]
  assoc : ∀ x y z, mid ![mid ![x, y], z] = mid ![x, mid ![y, z]]
  lassoc : ∀ x y z, left ![left ![x, y], z] = left ![x, left ![y, z]]
  lperm : ∀ x y z, left ![x, left ![y, z]] = left ![x, left ![z, y]]
  lmid : ∀ x y z, left ![x, mid ![y, z]] = left ![x, left ![y, z]]
  midl : ∀ x y z, left ![mid ![x, y], z] = mid ![x, left ![y, z]]

variable {R V}

open EndOp

/-- **Algebras over the commutative operad are commutative associative algebras.** -/
noncomputable def Com.algebraEquiv : SymAlgebra R (Lin R ComSet) V ≃ ComAlg R V :=
  (linHomEquiv R).symm.trans <| ComSet.homEquiv.trans
    { toFun := fun m => ⟨m.1, (isComm_iff m.1).1 m.2.1, (isAssoc_iff m.1).1 m.2.2⟩
      invFun := fun a => ⟨a.mul, (isComm_iff a.mul).2 a.comm, (isAssoc_iff a.mul).2 a.assoc⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- **Algebras over `Perm` are permutative algebras.** -/
noncomputable def Perm.algebraEquiv : SymAlgebra R (Sym.Perm R) V ≃ PermAlg R V :=
  (Perm.homEquiv R).trans
    { toFun := fun P => ⟨P.nu, (isAssoc_iff P.nu).1 P.r2a, (r2b_iff P.nu).1 P.r2b⟩
      invFun := fun a => ⟨a.mul, (isAssoc_iff a.mul).2 a.assoc, (r2b_iff a.mul).2 a.perm⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- **Algebras over the non-unital associative operad are associative algebras.** -/
noncomputable def Ass.algebraEquiv : SymAlgebra R (Lin R AssSet) V ≃ AssAlg R V :=
  (Ass.homEquiv R).trans
    { toFun := fun d => ⟨d.m, (leftComb_eq_rightComb_iff _ _ _ _).1 d.assoc⟩
      invFun := fun a => ⟨a.mul, (leftComb_eq_rightComb_iff _ _ _ _).2 a.assoc⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- **Algebras over `Dias` are Loday's associative dialgebras.** -/
noncomputable def Dias.algebraEquiv : SymAlgebra R (Dias R) V ≃ DiAlg R V :=
  (Dias.homEquiv R).trans
    { toFun := fun d =>
        { left := d.op .left
          right := d.op .right
          d1 := (leftComb_eq_rightComb_iff _ _ _ _).1 d.d1
          d2 := (leftComb_eq_rightComb_iff _ _ _ _).1 d.d2
          d3 := (leftComb_eq_rightComb_iff _ _ _ _).1 d.d3
          d4 := (leftComb_eq_rightComb_iff _ _ _ _).1 d.d4
          d5 := (leftComb_eq_rightComb_iff _ _ _ _).1 d.d5 }
      invFun := fun a =>
        { op := fun o => match o with | .left => a.left | .right => a.right
          d1 := (leftComb_eq_rightComb_iff _ _ _ _).2 a.d1
          d2 := (leftComb_eq_rightComb_iff _ _ _ _).2 a.d2
          d3 := (leftComb_eq_rightComb_iff _ _ _ _).2 a.d3
          d4 := (leftComb_eq_rightComb_iff _ _ _ _).2 a.d4
          d5 := (leftComb_eq_rightComb_iff _ _ _ _).2 a.d5 }
      left_inv := fun d => by
        obtain ⟨op, _, _, _, _, _⟩ := d
        simp only [DiasData.mk.injEq]
        funext o
        cases o <;> rfl
      right_inv := fun _ => rfl }

/-- **Algebras over `Trias` are Loday and Ronco's associative trialgebras.** -/
noncomputable def Trias.algebraEquiv : SymAlgebra R (Trias R) V ≃ TriAlg R V :=
  (Trias.homEquiv R).trans
    { toFun := fun d =>
        { left := d.op .left
          right := d.op .right
          middle := d.op .middle
          t1 := (leftComb_eq_rightComb_iff _ _ _ _).1 d.t1
          t2 := (leftComb_eq_rightComb_iff _ _ _ _).1 d.t2
          t3 := (leftComb_eq_rightComb_iff _ _ _ _).1 d.t3
          t4 := (leftComb_eq_rightComb_iff _ _ _ _).1 d.t4
          t5 := (leftComb_eq_rightComb_iff _ _ _ _).1 d.t5
          t6 := (leftComb_eq_rightComb_iff _ _ _ _).1 d.t6
          t7 := (leftComb_eq_rightComb_iff _ _ _ _).1 d.t7
          t8 := (leftComb_eq_rightComb_iff _ _ _ _).1 d.t8
          t9 := (leftComb_eq_rightComb_iff _ _ _ _).1 d.t9
          t10 := (leftComb_eq_rightComb_iff _ _ _ _).1 d.t10
          t11 := (leftComb_eq_rightComb_iff _ _ _ _).1 d.t11 }
      invFun := fun a =>
        { op := fun o => match o with
            | .left => a.left
            | .right => a.right
            | .middle => a.middle
          t1 := (leftComb_eq_rightComb_iff _ _ _ _).2 a.t1
          t2 := (leftComb_eq_rightComb_iff _ _ _ _).2 a.t2
          t3 := (leftComb_eq_rightComb_iff _ _ _ _).2 a.t3
          t4 := (leftComb_eq_rightComb_iff _ _ _ _).2 a.t4
          t5 := (leftComb_eq_rightComb_iff _ _ _ _).2 a.t5
          t6 := (leftComb_eq_rightComb_iff _ _ _ _).2 a.t6
          t7 := (leftComb_eq_rightComb_iff _ _ _ _).2 a.t7
          t8 := (leftComb_eq_rightComb_iff _ _ _ _).2 a.t8
          t9 := (leftComb_eq_rightComb_iff _ _ _ _).2 a.t9
          t10 := (leftComb_eq_rightComb_iff _ _ _ _).2 a.t10
          t11 := (leftComb_eq_rightComb_iff _ _ _ _).2 a.t11 }
      left_inv := fun d => by
        obtain ⟨op, _, _, _, _, _, _, _, _, _, _, _⟩ := d
        simp only [TriasData.mk.injEq]
        funext o
        cases o <;> rfl
      right_inv := fun _ => rfl }

/-- **Algebras over `ComTrias` are Vallette's commutative trialgebras.** -/
noncomputable def ComTrias.algebraEquiv : SymAlgebra R (ComTrias R) V ≃ ComTriAlg R V :=
  (ComTrias.homEquiv R).trans
    { toFun := fun D =>
        { mid := D.mid
          left := D.left
          comm := (isComm_iff _).1 D.comm
          assoc := (isAssoc_iff _).1 D.assoc
          lassoc := (isAssoc_iff _).1 D.lassoc
          lperm := (r2b_iff _).1 D.lperm
          lmid := (rightShape_iff _ _ _ _).1 D.lmid
          midl := (assocShape_iff _ _ _ _).1 D.midl }
      invFun := fun a =>
        { mid := a.mid
          left := a.left
          comm := (isComm_iff _).2 a.comm
          assoc := (isAssoc_iff _).2 a.assoc
          lassoc := (isAssoc_iff _).2 a.lassoc
          lperm := (r2b_iff _).2 a.lperm
          lmid := (rightShape_iff _ _ _ _).2 a.lmid
          midl := (assocShape_iff _ _ _ _).2 a.midl }
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Operad
