/-
# The graded endomorphism operad

A **super module** is a module with complementary idempotent parity projections (`SuperMod`).
Its **graded endomorphism operad** `EndGr R V` (`EndGr.instGrOperad`) has as operations with
inputs `A` the multilinear maps `V^A → V` *for every order of `A`*, the maps for two orders
differing by the Koszul sign of the reordering: a sign for each pair of odd inputs that the two
orders put in opposite positions (`GrEnd.rsg`, a cocycle by `GrEnd.rsg_trans`). Relabelling
transports the orders, and the parity projections act order by order (`GrEnd.parML`: the
component of parity `b` sends inputs of parities `c` to outputs of parity `b + |c|`). The
composite at a composite order `L ∘ᵢ M` is the **Koszul composite** (`GrEnd.kcomp`): the component
of parity `q` of the inner operation moves across the inputs before `i`, which costs
`σ(q · |inputs before i|)` (`GrEnd.bsg`).

The calculus is that of restricting the inputs of a multilinear map to given parities
(`GrEnd.inp`), twisting by signs depending on these parities (`GrEnd.twist`), and the
substitution rule for composites (`GrEnd.inp_compL`). The Koszul composite is natural in both
orders (`GrEnd.kcomp_twist_left`, `GrEnd.kcomp_twist_right`), so the composite of compatible
families does not depend on the orders it is computed in (`EndGr.compFam_eq`). It is sequentially
associative on the nose (`GrEnd.kcomp_assoc_seq`) and parallel associative up to the Koszul sign
of the two inserted operations (`GrEnd.kcomp_assoc_par`).

An **algebra over a graded operad** `P` is a morphism of graded operads `P → EndGr R V`
(`GrAlgebra`).
-/
import Operad.GrPresentation
import Operad.EndOperad
import Mathlib.Data.Nat.Bits

universe u v w

namespace Operad

open Sym GerBV

/-- **A super module**: a module with complementary idempotent parity projections. -/
class SuperMod (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V] [Module R V] where
  /-- The parity projections. -/
  pr : Bool → V →ₗ[R] V
  pr_add (x : V) : pr false x + pr true x = x
  pr_pr (b b' : Bool) (x : V) : pr b (pr b' x) = if b = b' then pr b' x else 0

namespace GrEnd

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V] [SuperMod R V]

/-- The parity projections of the super module. -/
local notation "𝔭" => SuperMod.pr (R := R) (V := V)

lemma pr_self (b : Bool) (x : V) : 𝔭 b (𝔭 b x) = 𝔭 b x := by
  rw [SuperMod.pr_pr, if_pos rfl]

lemma pr_ne {b b' : Bool} (h : b ≠ b') (x : V) : 𝔭 b (𝔭 b' x) = 0 := by
  rw [SuperMod.pr_pr, if_neg h]

lemma sum_pr (x : V) : ∑ b, 𝔭 b x = x := by
  rw [Fintype.sum_bool, add_comm, SuperMod.pr_add]

/-! ## Parities of inputs -/

/-- The total parity of a parity assignment. -/
def tot {X : Type} [Fintype X] (c : X → Bool) : Bool := Nat.bodd (∑ x, (c x).toNat)

lemma bodd_toNat (b : Bool) : Nat.bodd b.toNat = b := by
  cases b <;> rfl

lemma tot_sum {X Y : Type} [Fintype X] [Fintype Y] (c : X ⊕ Y → Bool) :
    tot c = xor (tot fun x => c (Sum.inl x)) (tot fun y => c (Sum.inr y)) := by
  unfold tot
  rw [Fintype.sum_sum_type, Nat.bodd_add]

lemma tot_comp_equiv {X Y : Type} [Fintype X] [Fintype Y] (e : X ≃ Y) (c : Y → Bool) :
    tot (fun x => c (e x)) = tot c := by
  unfold tot
  rw [e.sum_comp (fun y => (c y).toNat)]

lemma tot_feed {A B : Type} [Fintype A] [DecidableEq A] (i : A) (e : Without A i ⊕ B → Bool)
    (w : Bool) : tot (feed i e w) = xor w (tot fun a : Without A i => e (Sum.inl a)) := by
  unfold tot
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i, Nat.bodd_add, feed_self, bodd_toNat]
  congr 2
  exact Finset.sum_congr rfl fun a _ => by rw [feed_val]

/-! ## Restricting the inputs and projecting the output -/

variable {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype D]
  [DecidableEq D]

variable (R V) in
/-- **Restrict the inputs** of a multilinear map to the parities `c`. -/
def inp (c : A → Bool) : EndOp R V A →ₗ[R] EndOp R V A :=
  MultilinearMap.compLinearMapₗ fun a => 𝔭 (c a)

lemma inp_apply (c : A → Bool) (f : EndOp R V A) (x : A → V) :
    inp R V c f x = f fun a => 𝔭 (c a) (x a) := rfl

/-- **Every multilinear map is the sum of its restrictions.** -/
lemma sum_inp (f : EndOp R V A) : ∑ c, inp R V c f = f := by
  refine MultilinearMap.ext fun x => ?_
  rw [MultilinearMap.sum_apply]
  simp only [inp_apply]
  conv_rhs => rw [show x = fun a => ∑ b, 𝔭 b (x a) from funext fun a => (sum_pr (x a)).symm]
  rw [MultilinearMap.map_sum]

lemma inp_inp (c c' : A → Bool) (f : EndOp R V A) :
    inp R V c (inp R V c' f) = if c = c' then inp R V c f else 0 := by
  refine MultilinearMap.ext fun x => ?_
  simp only [inp_apply]
  split_ifs with h
  · subst h
    simp only [inp_apply, pr_self]
  · obtain ⟨a, ha⟩ := Function.ne_iff.1 h
    rw [MultilinearMap.zero_apply]
    exact f.map_coord_zero a (pr_ne (Ne.symm ha) _)

lemma inp_inp_self (c : A → Bool) (f : EndOp R V A) : inp R V c (inp R V c f) = inp R V c f := by
  rw [inp_inp, if_pos rfl]

/-- **Multilinear maps agree when their restrictions do.** -/
lemma ext_inp {f g : EndOp R V A} (h : ∀ c, inp R V c f = inp R V c g) : f = g := by
  rw [← sum_inp f, ← sum_inp g]
  exact Finset.sum_congr rfl fun c _ => h c

variable (R V) in
/-- **Project the output** of a multilinear map to the parity `b`. -/
def out (b : Bool) : EndOp R V A →ₗ[R] EndOp R V A where
  toFun f := (𝔭 b).compMultilinearMap f
  map_add' _ _ := MultilinearMap.ext fun _ => (𝔭 b).map_add _ _
  map_smul' _ _ := MultilinearMap.ext fun _ => (𝔭 b).map_smul _ _

lemma out_apply (b : Bool) (f : EndOp R V A) (x : A → V) : out R V b f x = 𝔭 b (f x) := rfl

lemma out_add (f : EndOp R V A) : out R V false f + out R V true f = f :=
  MultilinearMap.ext fun x => SuperMod.pr_add (f x)

lemma out_out (b b' : Bool) (f : EndOp R V A) :
    out R V b (out R V b' f) = if b = b' then out R V b' f else 0 := by
  refine MultilinearMap.ext fun x => ?_
  simp only [out_apply, SuperMod.pr_pr]
  split_ifs <;> rfl

lemma inp_out (c : A → Bool) (b : Bool) (f : EndOp R V A) :
    inp R V c (out R V b f) = out R V b (inp R V c f) := rfl

/-! ## The parity projections of multilinear maps -/

variable (R V) in
/-- **The component of parity `b`** of a multilinear map: it sends inputs of parities `c` to
outputs of parity `b + |c|`. -/
def parML (b : Bool) : EndOp R V A →ₗ[R] EndOp R V A :=
  ∑ c, out R V (xor b (tot c)) ∘ₗ inp R V c

lemma inp_parML (c : A → Bool) (b : Bool) (f : EndOp R V A) :
    inp R V c (parML R V b f) = out R V (xor b (tot c)) (inp R V c f) := by
  unfold parML
  rw [LinearMap.sum_apply, map_sum, Finset.sum_eq_single c]
  · rw [LinearMap.comp_apply, inp_out, inp_inp_self]
  · intro c' _ hc'
    rw [LinearMap.comp_apply, inp_out, inp_inp, if_neg (Ne.symm hc'), map_zero]
  · intro h
    exact absurd (Finset.mem_univ c) h

lemma parML_add (f : EndOp R V A) : parML R V false f + parML R V true f = f := by
  refine ext_inp fun c => ?_
  rw [map_add, inp_parML, inp_parML]
  cases tot c
  · exact out_add _
  · exact (add_comm _ _).trans (out_add _)

lemma parML_parML (b b' : Bool) (f : EndOp R V A) :
    parML R V b (parML R V b' f) = if b = b' then parML R V b' f else 0 := by
  refine ext_inp fun c => ?_
  rw [inp_parML, inp_parML, out_out]
  split_ifs with h1 h2 h2
  · rw [inp_parML]
  · exact absurd (by cases b <;> cases b' <;> cases tot c <;> simp_all) h2
  · exact absurd (by subst h2; rfl) h1
  · rw [map_zero]

lemma parML_out (b : Bool) (c : A → Bool) (f : EndOp R V A) :
    out R V (xor b (tot c)) (inp R V c (parML R V b f)) = inp R V c (parML R V b f) := by
  rw [inp_parML, out_out, if_pos rfl]

/-! ## Twisting by signs depending on the parities of the inputs -/

variable (R V) in
/-- **Twist a multilinear map by signs** depending on the parities of its inputs. -/
def twist (φ : (A → Bool) → R) : EndOp R V A →ₗ[R] EndOp R V A :=
  ∑ c, φ c • inp R V c

lemma inp_twist (φ : (A → Bool) → R) (c : A → Bool) (f : EndOp R V A) :
    inp R V c (twist R V φ f) = φ c • inp R V c f := by
  unfold twist
  rw [LinearMap.sum_apply, map_sum, Finset.sum_eq_single c]
  · rw [LinearMap.smul_apply, map_smul, inp_inp_self]
  · intro c' _ hc'
    rw [LinearMap.smul_apply, map_smul, inp_inp, if_neg (Ne.symm hc'), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ c) h

lemma twist_twist (φ ψ : (A → Bool) → R) (f : EndOp R V A) :
    twist R V φ (twist R V ψ f) = twist R V (fun c => φ c * ψ c) f :=
  ext_inp fun c => by rw [inp_twist, inp_twist, inp_twist, smul_smul]

lemma twist_congr {φ ψ : (A → Bool) → R} (h : ∀ c, φ c = ψ c) (f : EndOp R V A) :
    twist R V φ f = twist R V ψ f :=
  ext_inp fun c => by rw [inp_twist, inp_twist, h]

lemma twist_one (f : EndOp R V A) : twist R V (fun _ => 1) f = f :=
  ext_inp fun c => by rw [inp_twist, one_smul]

lemma parML_twist (b : Bool) (φ : (A → Bool) → R) (f : EndOp R V A) :
    parML R V b (twist R V φ f) = twist R V φ (parML R V b f) :=
  ext_inp fun c => by rw [inp_parML, inp_twist, inp_twist, inp_parML, map_smul]

lemma out_twist (b : Bool) (φ : (A → Bool) → R) (f : EndOp R V A) :
    out R V b (twist R V φ f) = twist R V φ (out R V b f) :=
  ext_inp fun c => by rw [inp_out, inp_twist, inp_twist, inp_out, map_smul]

/-! ## Relabelling -/

lemma inp_mapL (e : A ≃ B) (c : B → Bool) (f : EndOp R V A) :
    inp R V c (EndOp.mapL R V e f) = EndOp.mapL R V e (inp R V (fun a => c (e a)) f) :=
  MultilinearMap.ext fun _ => rfl

lemma out_mapL (e : A ≃ B) (b : Bool) (f : EndOp R V A) :
    out R V b (EndOp.mapL R V e f) = EndOp.mapL R V e (out R V b f) :=
  MultilinearMap.ext fun _ => rfl

lemma parML_mapL (e : A ≃ B) (b : Bool) (f : EndOp R V A) :
    parML R V b (EndOp.mapL R V e f) = EndOp.mapL R V e (parML R V b f) :=
  ext_inp fun c => by
    rw [inp_parML, inp_mapL, inp_mapL, inp_parML, out_mapL, tot_comp_equiv e c]

lemma twist_mapL (e : A ≃ B) (φ : (B → Bool) → R) (f : EndOp R V A) :
    twist R V φ (EndOp.mapL R V e f)
      = EndOp.mapL R V e (twist R V (fun c => φ fun b => c (e.symm b)) f) :=
  ext_inp fun c => by
    rw [inp_twist, inp_mapL, inp_mapL, inp_twist, map_smul]
    simp only [Equiv.apply_symm_apply]

/-! ## Composition -/

omit [SuperMod R V] in
lemma compL_apply (i : A) (f : EndOp R V A) (g : EndOp R V B) (x : Without A i ⊕ B → V) :
    EndOp.compL R V i f g x = f (feed i x (g fun b => x (Sum.inr b))) := rfl

lemma out_compL (i : A) (b : Bool) (f : EndOp R V A) (g : EndOp R V B) :
    out R V b (EndOp.compL R V i f g) = EndOp.compL R V i (out R V b f) g := rfl

/-- **The parities of the inputs of `f` in `f ∘ᵢ g`**, for inputs of parities `e` and `g` of
parity `q`: the input `i` receives the parity `q + |e_B|`. -/
def slot (i : A) (q : Bool) (e : Without A i ⊕ B → Bool) : A → Bool :=
  feed i e (xor q (tot fun b => e (Sum.inr b)))

/-- **Restricting the inputs of a composite** with an operation of parity `q` restricts the inputs
of both factors. -/
lemma inp_compL (i : A) (q : Bool) (e : Without A i ⊕ B → Bool) (f : EndOp R V A)
    (g : EndOp R V B) :
    inp R V e (EndOp.compL R V i f (parML R V q g))
      = EndOp.compL R V i (inp R V (slot i q e) f)
          (inp R V (fun b => e (Sum.inr b)) (parML R V q g)) := by
  refine MultilinearMap.ext fun x => ?_
  simp only [inp_apply, compL_apply]
  congr 1
  funext a
  by_cases h : a = i
  · subst h
    simp only [feed_self, slot]
    exact (congrArg (fun F : EndOp R V B => F fun b => x (Sum.inr b))
      (parML_out q (fun b => e (Sum.inr b)) g)).symm
  · simp only [feed_of_ne h, slot]

/-- **Twisting a composite through the parities of the outer inputs.** -/
lemma twist_compL_slot (i : A) (q : Bool) (α : (A → Bool) → R) (f : EndOp R V A)
    (g : EndOp R V B) :
    twist R V (fun e => α (slot i q e)) (EndOp.compL R V i f (parML R V q g))
      = EndOp.compL R V i (twist R V α f) (parML R V q g) :=
  ext_inp fun e => by
    rw [inp_twist, inp_compL, inp_compL, inp_twist, map_smul, LinearMap.smul_apply]

/-- **Twisting a composite through the parities of the inner inputs.** -/
lemma twist_compL_inr (i : A) (β : (B → Bool) → R) (f : EndOp R V A) (g : EndOp R V B) :
    twist R V (fun e => β fun b => e (Sum.inr b)) (EndOp.compL R V i f g)
      = EndOp.compL R V i f (twist R V β g) := by
  have key : ∀ q, twist R V (fun e => β fun b => e (Sum.inr b))
      (EndOp.compL R V i f (parML R V q g))
      = EndOp.compL R V i f (twist R V β (parML R V q g)) := fun q => ext_inp fun e => by
    rw [inp_twist, ← parML_twist, inp_compL, inp_compL, parML_twist, inp_twist, map_smul]
  conv_lhs => rw [← parML_add g, map_add, map_add, key, key]
  conv_rhs => rw [← parML_add g, map_add, map_add]

omit [DecidableEq B] in
lemma tot_slot (i : A) (q : Bool) (e : Without A i ⊕ B → Bool) :
    tot (slot i q e) = xor q (tot e) := by
  rw [slot, tot_feed, tot_sum e]
  cases q <;> cases tot (fun b => e (Sum.inr b)) <;> cases tot (fun a => e (Sum.inl a)) <;> rfl

/-- **A composite of homogeneous operations is homogeneous**, the parities adding. -/
lemma parML_compL (i : A) (p q : Bool) (f : EndOp R V A) (g : EndOp R V B) :
    parML R V (xor p q) (EndOp.compL R V i (parML R V p f) (parML R V q g))
      = EndOp.compL R V i (parML R V p f) (parML R V q g) :=
  ext_inp fun e => by
    rw [inp_parML, inp_compL, out_compL, inp_parML, out_out, tot_slot, if_pos (by
      cases p <;> cases q <;> cases tot e <;> rfl)]

/-- The component of parity `b` of a composite with a homogeneous inner operation. -/
lemma parML_compL_right (i : A) (b q : Bool) (f : EndOp R V A) (g : EndOp R V B) :
    parML R V b (EndOp.compL R V i f (parML R V q g))
      = EndOp.compL R V i (parML R V (xor b q) f) (parML R V q g) := by
  conv_lhs => rw [← parML_add f, map_add, LinearMap.add_apply, map_add]
  have h : ∀ p, parML R V b (EndOp.compL R V i (parML R V p f) (parML R V q g))
      = if p = xor b q then EndOp.compL R V i (parML R V p f) (parML R V q g) else 0 := by
    intro p
    rw [← parML_compL i p q f g, parML_parML]
    by_cases hp : p = xor b q
    · rw [if_pos (by subst hp; cases b <;> cases q <;> rfl), if_pos hp, parML_compL]
    · rw [if_neg (fun h => hp (by subst h; cases p <;> cases q <;> rfl)), if_neg hp]
  rw [h, h]
  cases hb : xor b q <;> simp

/-! ## Koszul signs -/

omit [SuperMod R V] in
lemma σ_and_xor (x a b : Bool) : σ R (x && xor a b) = σ R (x && a) * σ R (x && b) := by
  cases x <;> cases a <;> cases b <;> simp

omit [SuperMod R V] in
lemma σ_xor_and (x a b : Bool) : σ R (xor a b && x) = σ R (a && x) * σ R (b && x) := by
  cases x <;> cases a <;> cases b <;> simp

omit [SuperMod R V] in
lemma prod_σ_finset {X : Type} (x : Bool) (d : X → Bool) (s : Finset X) :
    ∏ y ∈ s, σ R (x && d y) = σ R (x && Nat.bodd (∑ y ∈ s, (d y).toNat)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, Nat.bodd_add, bodd_toNat,
      σ_and_xor]

omit [SuperMod R V] in
lemma prod_σ_tot {X : Type} [Fintype X] (x : Bool) (d : X → Bool) :
    ∏ y, σ R (x && d y) = σ R (x && tot d) :=
  prod_σ_finset x d Finset.univ

omit [SuperMod R V] in
lemma prod_ite_σ_tot {X : Type} [Fintype X] (P : Prop) [Decidable P] (x : Bool) (d : X → Bool) :
    ∏ y, (if P then σ R (x && d y) else 1) = if P then σ R (x && tot d) else 1 := by
  split_ifs
  · exact prod_σ_tot x d
  · exact Finset.prod_const_one

omit [SuperMod R V] in
lemma σ_mul_self' (a : Bool) : σ R a * σ R a = 1 := by
  cases a <;> simp

omit [SuperMod R V] [Fintype A] [DecidableEq A] in
lemma lt_asymm (L : LinOrd A) {a b : A} (h : L.lt a b) : ¬ L.lt b a :=
  fun h' => L.irrefl a (L.trans _ _ _ h h')

variable (R) in
open Classical in
/-- **The Koszul sign of moving an operation of parity `q` across the inputs before `i`** in the
order `L`, for inputs of parities `c`. -/
noncomputable def bsg (L : LinOrd A) (i : A) (q : Bool) (c : A → Bool) : R :=
  ∏ a, if L.lt a i then σ R (q && c a) else 1

omit [SuperMod R V] [DecidableEq A] in
lemma bsg_mul (L : LinOrd A) (i : A) (q r : Bool) (c : A → Bool) :
    bsg R L i q c * bsg R L i r c = bsg R L i (xor q r) c := by
  unfold bsg
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  split_ifs
  · rw [σ_xor_and]
  · rw [mul_one]

omit [SuperMod R V] [DecidableEq A] in
lemma bsg_false (L : LinOrd A) (i : A) (c : A → Bool) : bsg R L i false c = 1 := by
  unfold bsg
  exact Finset.prod_eq_one fun a _ => by split_ifs <;> simp

omit [SuperMod R V] [DecidableEq A] in
lemma bsg_congr (L : LinOrd A) (i : A) (q : Bool) {c c' : A → Bool} (h : ∀ a, a ≠ i → c a = c' a) :
    bsg R L i q c = bsg R L i q c' := by
  unfold bsg
  refine Finset.prod_congr rfl fun a _ => ?_
  split_ifs with ha
  · rw [h a fun e => L.irrefl a (e ▸ ha)]
  · rfl

omit [SuperMod R V] [DecidableEq A] in
lemma bsg_map {A' : Type} [Fintype A'] [DecidableEq A'] (e : A ≃ A') (L : LinOrd A) (i : A)
    (q : Bool) (c : A' → Bool) :
    bsg R (LinOrd.map e L) (e i) q c = bsg R L i q fun a => c (e a) := by
  classical
  unfold bsg
  rw [← e.prod_comp]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp only [LinOrd.map_lt, Equiv.symm_apply_apply]

omit [SuperMod R V] in
lemma bsg_one (q : Bool) (c : Unit → Bool) : bsg R LinOrd.one () q c = 1 := by
  unfold bsg
  exact Finset.prod_eq_one fun a _ => if_neg id

omit [SuperMod R V] [DecidableEq B] in
/-- The sign before an inserted input, in a composite order. -/
lemma bsg_comp_inr (i : A) (j : B) (L : LinOrd A) (M : LinOrd B) (q r : Bool)
    (e : Without A i ⊕ B → Bool) :
    bsg R (LinOrd.comp i L M) (Sum.inr j) r e
      = bsg R L i r (slot i q e) * bsg R M j r fun b => e (Sum.inr b) := by
  classical
  unfold bsg
  rw [Fintype.prod_sum_type, Fintype.prod_eq_mul_prod_subtype_ne _ i, if_neg (L.irrefl i),
    one_mul]
  congr 1
  refine Finset.prod_congr rfl fun a _ => ?_
  show (if L.lt a.1 i then _ else _) = _
  rw [show slot i q e a.1 = e (Sum.inl a) from feed_val _ _ _ _]

omit [SuperMod R V] [DecidableEq B] in
open Classical in
/-- The sign before an outer input, in a composite order. -/
lemma bsg_comp_inl {i k : A} (hik : i ≠ k) (L : LinOrd A) (M : LinOrd B) (q r : Bool)
    (e : Without A i ⊕ B → Bool) :
    bsg R (LinOrd.comp i L M) (Sum.inl ⟨k, Ne.symm hik⟩) r e
      = bsg R L k r (slot i q e) * if L.lt i k then σ R (r && q) else 1 := by
  unfold bsg
  rw [Fintype.prod_sum_type, Fintype.prod_eq_mul_prod_subtype_ne (fun a => if L.lt a k then
    σ R (r && slot i q e a) else 1) i]
  have h1 : ∏ b : B, (if (LinOrd.comp i L M).lt (Sum.inr b) (Sum.inl ⟨k, Ne.symm hik⟩) then
      σ R (r && e (Sum.inr b)) else 1) = if L.lt i k then σ R (r && tot fun b => e (Sum.inr b))
        else 1 :=
    prod_ite_σ_tot (L.lt i k) r _
  have h2 : ∏ a : Without A i, (if (LinOrd.comp i L M).lt (Sum.inl a)
      (Sum.inl ⟨k, Ne.symm hik⟩) then σ R (r && e (Sum.inl a)) else 1)
      = ∏ a : Without A i, if L.lt a.1 k then σ R (r && slot i q e a.1) else 1 :=
    Finset.prod_congr rfl fun a _ => by
      rw [show slot i q e a.1 = e (Sum.inl a) from feed_val _ _ _ _]
      rfl
  rw [h1, h2, slot, feed_self]
  by_cases h : L.lt i k
  · simp only [if_pos h]
    rw [σ_and_xor]
    linear_combination (-((∏ a : Without A i, if L.lt a.1 k then σ R (r && feed i e (xor q
      (tot fun b => e (Sum.inr b))) a.1) else 1) * σ R (r && tot fun b => e (Sum.inr b))))
      * σ_mul_self' (R := R) (r && q)
  · simp only [if_neg h, mul_one, one_mul]

omit [SuperMod R V] in
lemma prod_ite_σ_tot' {X : Type} [Fintype X] (P : Prop) [Decidable P] (x : Bool)
    (d : X → Bool) :
    ∏ y, (if P then σ R (d y && x) else 1) = if P then σ R (tot d && x) else 1 := by
  simp_rw [Bool.and_comm _ x]
  exact prod_ite_σ_tot P x d

omit [SuperMod R V] [Fintype A] [DecidableEq A] in
lemma lt_and_lt (L : LinOrd A) (a b : A) : (L.lt a b ∧ L.lt b a) ↔ False :=
  ⟨fun h => lt_asymm L h.1 h.2, False.elim⟩

variable (R) in
open Classical in
/-- **The Koszul sign of reordering** inputs of parities `c` from the order `L` to the order `L'`:
a sign for each pair of odd inputs in opposite orders. -/
noncomputable def rsg (L L' : LinOrd A) (c : A → Bool) : R :=
  ∏ a, ∏ b, if L.lt a b ∧ L'.lt b a then σ R (c a && c b) else 1

omit [SuperMod R V] [DecidableEq A] in
lemma rsg_self (L : LinOrd A) (c : A → Bool) : rsg R L L c = 1 := by
  unfold rsg
  exact Finset.prod_eq_one fun a _ => Finset.prod_eq_one fun b _ =>
    if_neg fun h => lt_asymm L h.1 h.2

omit [SuperMod R V] in
open Classical in
/-- A product over pairs, oriented by an order. -/
lemma prod_orient (L : LinOrd A) (F : A → A → R) (hF : ∀ a, F a a = 1) :
    ∏ a, ∏ b, F a b = ∏ a, ∏ b, if L.lt a b then F a b * F b a else 1 := by
  classical
  have h1 : ∀ a b, F a b = (if L.lt a b then F a b else 1) * (if L.lt b a then F a b else 1) := by
    intro a b
    by_cases hab : a = b
    · subst hab
      rw [if_neg (L.irrefl a), hF, one_mul]
    · rcases L.total a b hab with h | h
      · rw [if_pos h, if_neg (lt_asymm L h), mul_one]
      · rw [if_neg (lt_asymm L h), if_pos h, one_mul]
  calc ∏ a, ∏ b, F a b
      = ∏ a, ∏ b, (if L.lt a b then F a b else 1) * (if L.lt b a then F a b else 1) :=
        Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => h1 a b
    _ = (∏ a, ∏ b, if L.lt a b then F a b else 1) * ∏ a, ∏ b, if L.lt b a then F a b else 1 := by
        simp only [Finset.prod_mul_distrib]
    _ = (∏ a, ∏ b, if L.lt a b then F a b else 1) * ∏ a, ∏ b, if L.lt a b then F b a else 1 := by
        rw [Finset.prod_comm (f := fun a b => if L.lt b a then F a b else 1)]
    _ = ∏ a, ∏ b, if L.lt a b then F a b * F b a else 1 := by
        simp only [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
        split_ifs <;> simp

omit [SuperMod R V] in
/-- **The reordering signs form a cocycle.** -/
lemma rsg_trans (L L' L'' : LinOrd A) (c : A → Bool) :
    rsg R L L' c * rsg R L' L'' c = rsg R L L'' c := by
  classical
  unfold rsg
  rw [prod_orient L (fun a b => if L.lt a b ∧ L'.lt b a then σ R (c a && c b) else 1)
      (fun a => if_neg fun h => L.irrefl a h.1),
    prod_orient L (fun a b => if L'.lt a b ∧ L''.lt b a then σ R (c a && c b) else 1)
      (fun a => if_neg fun h => L'.irrefl a h.1),
    prod_orient L (fun a b => if L.lt a b ∧ L''.lt b a then σ R (c a && c b) else 1)
      (fun a => if_neg fun h => L.irrefl a h.1)]
  simp only [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
  by_cases hab : L.lt a b
  · have hne : a ≠ b := fun h => L.irrefl a (h ▸ hab)
    have hs : σ R (c b && c a) = σ R (c a && c b) := by rw [Bool.and_comm]
    rcases L'.total a b hne with h1 | h1 <;> rcases L''.total a b hne with h2 | h2 <;>
      simp only [hab, h1, h2, lt_asymm _ hab, lt_asymm _ h1, lt_asymm _ h2, and_true, and_false,
        if_true, if_false, mul_one, one_mul, hs]
    exact σ_mul_self' _
  · simp only [hab, if_false, mul_one]

omit [SuperMod R V] [DecidableEq A] in
/-- **Relabelling the orders relabels the parities.** -/
lemma rsg_map {A' : Type} [Fintype A'] [DecidableEq A'] (e : A ≃ A') (L L' : LinOrd A)
    (c : A' → Bool) :
    rsg R (LinOrd.map e L) (LinOrd.map e L') c = rsg R L L' fun a => c (e a) := by
  classical
  unfold rsg
  rw [← e.prod_comp]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← e.prod_comp]
  refine Finset.prod_congr rfl fun b _ => ?_
  simp only [LinOrd.map_lt, Equiv.symm_apply_apply]

omit [SuperMod R V] [DecidableEq B] in
/-- Changing the order of the inserted inputs of a composite order. -/
lemma rsg_comp_right (i : A) (L : LinOrd A) (M₀ M : LinOrd B) (e : Without A i ⊕ B → Bool) :
    rsg R (LinOrd.comp i L M₀) (LinOrd.comp i L M) e = rsg R M₀ M fun b => e (Sum.inr b) := by
  classical
  unfold rsg
  simp only [Fintype.prod_sum_type, LinOrd.comp_lt, LinOrd.compLt_inl_inl,
    LinOrd.compLt_inl_inr, LinOrd.compLt_inr_inl, LinOrd.compLt_inr_inr, lt_and_lt, if_false,
    Finset.prod_const_one, one_mul]
  congr

omit [SuperMod R V] [DecidableEq B] in
/-- **Changing the order of the outer inputs of a composite order**: the reordering sign of the
composite and the Koszul signs of the inserted operation, before and after. -/
lemma rsg_comp_left (i : A) (L₀ L : LinOrd A) (M : LinOrd B) (q : Bool)
    (e : Without A i ⊕ B → Bool) :
    bsg R L i q (slot i q e) * rsg R L₀ L (slot i q e)
      = rsg R (LinOrd.comp i L₀ M) (LinOrd.comp i L M) e * bsg R L₀ i q (slot i q e) := by
  classical
  set t := tot fun b => e (Sum.inr b) with ht
  have hci : slot i q e i = xor q t := feed_self _ _ _
  have hca : ∀ a : Without A i, slot i q e a.1 = e (Sum.inl a) := fun a => feed_val _ _ _ _
  -- the Koszul signs, as products over the outer inputs other than `i`
  have hb : ∀ L' : LinOrd A, bsg R L' i q (slot i q e)
      = ∏ a : Without A i, if L'.lt a.1 i then σ R (q && e (Sum.inl a)) else 1 := by
    intro L'
    unfold bsg
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i, if_neg (L'.irrefl i), one_mul]
    exact Finset.prod_congr rfl fun a _ => by rw [hca]
  -- the common part: pairs of outer inputs other than `i`
  set X : Without A i → R := fun a => ∏ a' : Without A i,
    if L₀.lt a.1 a'.1 ∧ L.lt a'.1 a.1 then σ R (e (Sum.inl a) && e (Sum.inl a')) else 1 with hX
  have hr1 : rsg R L₀ L (slot i q e) = ∏ a : Without A i,
      (if L₀.lt i a.1 ∧ L.lt a.1 i then σ R (xor q t && e (Sum.inl a)) else 1)
        * ((if L₀.lt a.1 i ∧ L.lt i a.1 then σ R (e (Sum.inl a) && xor q t) else 1) * X a) := by
    unfold rsg
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i, Fintype.prod_eq_mul_prod_subtype_ne _ i,
      if_neg (fun h => L₀.irrefl i h.1), one_mul, Finset.prod_mul_distrib]
    congr 1
    · exact Finset.prod_congr rfl fun a _ => by rw [hci, hca]
    · refine Finset.prod_congr rfl fun a _ => ?_
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ i, hci, hca]
      congr 1
      exact Finset.prod_congr rfl fun a' _ => by simp only [hca]
  -- the composite orders
  have hr2 : rsg R (LinOrd.comp i L₀ M) (LinOrd.comp i L M) e = ∏ a : Without A i,
      (if L₀.lt i a.1 ∧ L.lt a.1 i then σ R (t && e (Sum.inl a)) else 1)
        * ((if L₀.lt a.1 i ∧ L.lt i a.1 then σ R (e (Sum.inl a) && t) else 1) * X a) := by
    have h1 : ∀ a : Without A i, (∏ b : B, if (LinOrd.comp i L₀ M).lt (Sum.inl a) (Sum.inr b) ∧
        (LinOrd.comp i L M).lt (Sum.inr b) (Sum.inl a) then σ R (e (Sum.inl a) && e (Sum.inr b))
          else 1) = if L₀.lt a.1 i ∧ L.lt i a.1 then σ R (e (Sum.inl a) && t) else 1 :=
      fun a => prod_ite_σ_tot (L₀.lt a.1 i ∧ L.lt i a.1) (e (Sum.inl a)) _
    have h2 : ∀ a : Without A i, (∏ b : B, if (LinOrd.comp i L₀ M).lt (Sum.inr b) (Sum.inl a) ∧
        (LinOrd.comp i L M).lt (Sum.inl a) (Sum.inr b) then σ R (e (Sum.inr b) && e (Sum.inl a))
          else 1) = if L₀.lt i a.1 ∧ L.lt a.1 i then σ R (t && e (Sum.inl a)) else 1 :=
      fun a => prod_ite_σ_tot' (L₀.lt i a.1 ∧ L.lt a.1 i) (e (Sum.inl a)) _
    have h3 : ∀ b : B, (∏ b' : B, if (LinOrd.comp i L₀ M).lt (Sum.inr b) (Sum.inr b') ∧
        (LinOrd.comp i L M).lt (Sum.inr b') (Sum.inr b) then σ R (e (Sum.inr b) && e (Sum.inr b'))
          else 1) = 1 :=
      fun b => Finset.prod_eq_one fun b' _ => if_neg fun h => lt_asymm M h.1 h.2
    have h4 : ∀ a : Without A i, (∏ a' : Without A i, if (LinOrd.comp i L₀ M).lt (Sum.inl a)
        (Sum.inl a') ∧ (LinOrd.comp i L M).lt (Sum.inl a') (Sum.inl a) then
          σ R (e (Sum.inl a) && e (Sum.inl a')) else 1) = X a := fun a => rfl
    unfold rsg
    rw [Fintype.prod_sum_type]
    simp only [Fintype.prod_sum_type, h1, h3, h4, mul_one]
    rw [Finset.prod_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun (b : B) (a : Without A i) => if (LinOrd.comp i L₀ M).lt (Sum.inr b) (Sum.inl a) ∧
        (LinOrd.comp i L M).lt (Sum.inl a) (Sum.inr b) then σ R (e (Sum.inr b) && e (Sum.inl a))
          else 1)]
    simp only [h2, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun a _ => by ring1
  rw [hb L, hb L₀, hr1, hr2, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  have ha : a.1 ≠ i := a.2
  have hs : ∀ x y : Bool, σ R (x && y) = σ R (y && x) := fun x y => by rw [Bool.and_comm]
  rcases L₀.total a.1 i ha with h0 | h0 <;> rcases L.total a.1 i ha with h1 | h1 <;>
    simp only [h0, h1, lt_asymm _ h0, lt_asymm _ h1, and_true, and_false, if_true, if_false,
      mul_one, one_mul, σ_and_xor, σ_xor_and] <;>
    first
    | ring1
    | (rw [hs (e (Sum.inl a)) q]; ring1)
    | linear_combination (σ R (t && e (Sum.inl a)) * X a)
        * σ_mul_self' (R := R) (q && e (Sum.inl a))

/-! ## The Koszul composition -/

lemma twist_mul_const (φ : (A → Bool) → R) (a : R) (f : EndOp R V A) :
    twist R V (fun c => φ c * a) f = a • twist R V φ f :=
  ext_inp fun c => by rw [inp_twist, map_smul, inp_twist, smul_smul, mul_comm]

lemma parML_one (b : Bool) :
    parML R V b (EndOp.one R V) = if b = false then EndOp.one R V else 0 := by
  refine ext_inp fun c => ?_
  have hc : tot c = c () := by
    unfold tot
    rw [Fintype.sum_unique, bodd_toNat]
  rw [inp_parML, hc]
  have h1 : out R V (c ()) (inp R V c (EndOp.one R V)) = inp R V c (EndOp.one R V) :=
    MultilinearMap.ext fun x => pr_self _ _
  have h2 : out R V (!c ()) (inp R V c (EndOp.one R V)) = 0 :=
    MultilinearMap.ext fun x => pr_ne (by cases c () <;> simp) _
  split_ifs with hb
  · subst hb
    rw [Bool.false_xor, h1]
  · rw [show b = true by simpa using hb, Bool.true_xor, h2, map_zero]

variable (R V) in
/-- **The Koszul composition** relative to an order `L` of the outer inputs: the component of
parity `q` of `g` is moved across the inputs of `f` before `i`. -/
noncomputable def kcomp (L : LinOrd A) (i : A) :
    EndOp R V A →ₗ[R] EndOp R V B →ₗ[R] EndOp R V (Without A i ⊕ B) :=
  ∑ q, ((EndOp.compL R V i).comp (twist R V (bsg R L i q))).compl₂ (parML R V q)

lemma kcomp_apply (L : LinOrd A) (i : A) (f : EndOp R V A) (g : EndOp R V B) :
    kcomp R V L i f g = ∑ q, EndOp.compL R V i (twist R V (bsg R L i q) f) (parML R V q g) := by
  simp only [kcomp, LinearMap.sum_apply, LinearMap.compl₂_apply, LinearMap.comp_apply]

/-- The Koszul composition with a homogeneous operation. -/
lemma kcomp_parML (L : LinOrd A) (i : A) (f : EndOp R V A) (q : Bool) (g : EndOp R V B) :
    kcomp R V L i f (parML R V q g)
      = EndOp.compL R V i (twist R V (bsg R L i q) f) (parML R V q g) := by
  rw [kcomp_apply, Finset.sum_eq_single q]
  · rw [parML_parML, if_pos rfl]
  · intro r _ hr
    rw [parML_parML, if_neg hr, map_zero]
  · intro h
    exact absurd (Finset.mem_univ q) h

/-- **The Koszul composite of homogeneous operations is homogeneous.** -/
lemma parML_kcomp (L : LinOrd A) (i : A) (p q : Bool) (f : EndOp R V A) (g : EndOp R V B) :
    parML R V (xor p q) (kcomp R V L i (parML R V p f) (parML R V q g))
      = kcomp R V L i (parML R V p f) (parML R V q g) := by
  rw [kcomp_parML, ← parML_twist]
  exact parML_compL i p q _ g

/-- **The Koszul composition is equivariant.** -/
lemma mapL_kcomp {A' B' : Type} [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']
    (σ' : A ≃ A') (τ : B ≃ B') (L : LinOrd A) (i : A) (f : EndOp R V A) (g : EndOp R V B) :
    EndOp.mapL R V (compEquiv σ' τ i) (kcomp R V L i f g)
      = kcomp R V (LinOrd.map σ' L) (σ' i) (EndOp.mapL R V σ' f) (EndOp.mapL R V τ g) := by
  rw [kcomp_apply, kcomp_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h := SymOperad.map_comp (R := R) (P := EndOp R V) σ' τ i
    (twist R V (bsg R L i q) f) (parML R V q g)
  refine h.trans ?_
  show EndOp.compL R V (σ' i) (EndOp.mapL R V σ' (twist R V (bsg R L i q) f))
    (EndOp.mapL R V τ (parML R V q g)) = _
  have hb : (fun c => bsg R (LinOrd.map σ' L) (σ' i) q fun b => c (σ'.symm b)) = bsg R L i q :=
    funext fun c => by rw [bsg_map]; simp only [Equiv.symm_apply_apply]
  rw [twist_mapL, ← parML_mapL, hb]

/-- The Koszul composition with the unit. -/
lemma kcomp_one (L : LinOrd A) (i : A) (f : EndOp R V A) :
    EndOp.mapL R V (rightUnitEquiv i) (kcomp R V L i f (EndOp.one R V)) = f := by
  have h1 : EndOp.one R V = parML R V false (EndOp.one R V) := by
    rw [parML_one, if_pos rfl]
  rw [h1, kcomp_parML, ← h1]
  rw [twist_congr (fun c => bsg_false L i c), twist_one]
  exact SymOperad.comp_one (R := R) (P := EndOp R V) i f

/-- The Koszul composition into the unit. -/
lemma one_kcomp (g : EndOp R V B) :
    EndOp.mapL R V (leftUnitEquiv B) (kcomp R V LinOrd.one () (EndOp.one R V) g) = g := by
  rw [kcomp_apply]
  simp only [twist_congr (fun c => bsg_one _ c), twist_one]
  rw [← map_sum, Fintype.sum_bool, add_comm, parML_add]
  exact SymOperad.one_comp (R := R) (P := EndOp R V) g

/-- **Naturality in the order of the inserted inputs.** -/
lemma kcomp_twist_right (L : LinOrd A) (M₀ M : LinOrd B) (i : A) (f : EndOp R V A)
    (g : EndOp R V B) :
    kcomp R V L i f (twist R V (rsg R M₀ M) g)
      = twist R V (rsg R (LinOrd.comp i L M₀) (LinOrd.comp i L M)) (kcomp R V L i f g) := by
  rw [kcomp_apply, kcomp_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [twist_congr (fun e => rsg_comp_right i L M₀ M e), twist_compL_inr, parML_twist]

/-- **Naturality in the order of the outer inputs.** -/
lemma kcomp_twist_left (L₀ L : LinOrd A) (M : LinOrd B) (i : A) (f : EndOp R V A)
    (g : EndOp R V B) :
    kcomp R V L i (twist R V (rsg R L₀ L) f) g
      = twist R V (rsg R (LinOrd.comp i L₀ M) (LinOrd.comp i L M)) (kcomp R V L₀ i f g) := by
  rw [kcomp_apply, kcomp_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [twist_twist, ← twist_compL_slot, ← twist_compL_slot, twist_twist]
  exact twist_congr (fun e => rsg_comp_left i L₀ L M q e) _

lemma twist_comm (φ ψ : (A → Bool) → R) (f : EndOp R V A) :
    twist R V φ (twist R V ψ f) = twist R V ψ (twist R V φ f) := by
  rw [twist_twist, twist_twist]
  exact twist_congr (fun c => mul_comm _ _) f

/-- **Sequential associativity of the Koszul composition**, on the nose. -/
lemma kcomp_assoc_seq (L : LinOrd A) (M : LinOrd B) (i : A) (j : B) (f : EndOp R V A)
    (g : EndOp R V B) (h : EndOp R V D) :
    EndOp.mapL R V (seqEquiv i j D)
        (kcomp R V (LinOrd.comp i L M) (Sum.inr j) (kcomp R V L i f g) h)
      = kcomp R V L i f (kcomp R V M j g h) := by
  have key : ∀ q r : Bool, twist R V (bsg R (LinOrd.comp i L M) (Sum.inr j) r)
      (EndOp.compL R V i (twist R V (bsg R L i q) f) (parML R V q g))
      = EndOp.compL R V i (twist R V (bsg R L i (xor r q)) f)
          (parML R V q (twist R V (bsg R M j r) g)) := by
    intro q r
    rw [twist_congr (fun e => bsg_comp_inr i j L M q r e), ← twist_twist, twist_compL_inr,
      ← parML_twist, twist_compL_slot, twist_twist]
    congr 2
    exact twist_congr (fun c => bsg_mul L i r q c) f
  rw [kcomp_apply, kcomp_apply, kcomp_apply]
  simp only [map_sum, LinearMap.sum_apply, key]
  have hseq : ∀ (x : EndOp R V A) (y : EndOp R V B) (z : EndOp R V D),
      EndOp.mapL R V (seqEquiv i j D) (EndOp.compL R V (Sum.inr j) (EndOp.compL R V i x y) z)
        = EndOp.compL R V i x (EndOp.compL R V j y z) :=
    fun x y z => SymOperad.comp_assoc_seq (R := R) (P := EndOp R V) i j x y z
  simp only [hseq, kcomp_apply, map_sum, parML_compL_right]
  simp only [Fintype.sum_bool, Bool.not_true, Bool.not_false, Bool.xor_true, Bool.xor_false]
  abel

/-- **Parallel associativity of the Koszul composition**, up to the Koszul sign of exchanging the
two inserted operations. -/
lemma kcomp_assoc_par {i k : A} (hik : i ≠ k) (L : LinOrd A) (M : LinOrd B) (N : LinOrd D)
    (f : EndOp R V A) (q r : Bool) (g : EndOp R V B) (h : EndOp R V D) :
    EndOp.mapL R V (parEquiv hik B D)
        (kcomp R V (LinOrd.comp i L M) (Sum.inl ⟨k, Ne.symm hik⟩)
          (kcomp R V L i f (parML R V q g)) (parML R V r h))
      = σ R (q && r) • kcomp R V (LinOrd.comp k L N) (Sum.inl ⟨i, hik⟩)
          (kcomp R V L k f (parML R V r h)) (parML R V q g) := by
  classical
  rw [kcomp_parML, kcomp_parML, kcomp_parML, kcomp_parML,
    twist_congr (fun e => bsg_comp_inl hik L M q r e), twist_mul_const, twist_compL_slot,
    twist_congr (fun e => bsg_comp_inl (Ne.symm hik) L N r q e), twist_mul_const,
    twist_compL_slot, twist_comm (bsg R L i q)]
  have hpar : ∀ (x : EndOp R V A) (y : EndOp R V B) (z : EndOp R V D),
      EndOp.mapL R V (parEquiv hik B D)
        (EndOp.compL R V (Sum.inl ⟨k, Ne.symm hik⟩) (EndOp.compL R V i x y) z)
        = EndOp.compL R V (Sum.inl ⟨i, hik⟩) (EndOp.compL R V k x z) y :=
    fun x y z => SymOperad.comp_assoc_par (R := R) (P := EndOp R V) hik x y z
  simp only [map_smul, LinearMap.smul_apply, smul_smul]
  rw [hpar]
  congr 1
  by_cases hl : L.lt i k
  · rw [if_pos hl, if_neg (lt_asymm L hl), mul_one, Bool.and_comm]
  · rw [if_neg hl, if_pos ((L.total i k hik).resolve_left hl)]
    exact (σ_mul_self' _).symm

/-! ## The graded endomorphism operad -/

variable (R V) in
/-- **Compatible families**: a multilinear map for every order of the inputs, those for two orders
differing by the Koszul sign of the reordering. -/
def compat (A : Type) [Fintype A] [DecidableEq A] : Submodule R (LinOrd A → EndOp R V A) where
  carrier := {F | ∀ L L', F L' = twist R V (rsg R L L') (F L)}
  add_mem' {F G} hF hG L L' := by
    simp only [Set.mem_setOf_eq] at hF hG ⊢
    rw [Pi.add_apply, Pi.add_apply, hF L L', hG L L', map_add]
  zero_mem' L L' := by
    simp only [Pi.zero_apply, map_zero]
  smul_mem' c F hF L L' := by
    simp only [Set.mem_setOf_eq] at hF ⊢
    rw [Pi.smul_apply, Pi.smul_apply, hF L L', map_smul]

end GrEnd

variable (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V] [Module R V] [SuperMod R V]

/-- **The graded endomorphism operad** of a super module: an operation with inputs `A` is a
multilinear map `V^A → V` for every order of `A`, those for two orders differing by the Koszul
sign of the reordering (`GrEnd.compat`). -/
def EndGr (A : Type) [Fintype A] [DecidableEq A] : Type v := GrEnd.compat R V A

namespace EndGr

open GrEnd

instance (A : Type) [Fintype A] [DecidableEq A] : AddCommGroup (EndGr R V A) :=
  inferInstanceAs (AddCommGroup (compat R V A))

instance (A : Type) [Fintype A] [DecidableEq A] : Module R (EndGr R V A) :=
  inferInstanceAs (Module R (compat R V A))

variable {R V}
variable {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype D]
  [DecidableEq D]

/-- The multilinear map of a compatible family at an order of the inputs. -/
def fam (F : EndGr R V A) (L : LinOrd A) : EndOp R V A := (F : compat R V A).1 L

/-- A compatible family. -/
def mk (Φ : LinOrd A → EndOp R V A) (h : ∀ L L', Φ L' = twist R V (rsg R L L') (Φ L)) :
    EndGr R V A := ⟨Φ, h⟩

@[simp] lemma mk_fam (Φ : LinOrd A → EndOp R V A) (h : ∀ L L', Φ L' = twist R V (rsg R L L') (Φ L))
    (L : LinOrd A) : (mk Φ h).fam L = Φ L := rfl

lemma fam_compat (F : EndGr R V A) (L L' : LinOrd A) :
    F.fam L' = twist R V (rsg R L L') (F.fam L) :=
  (F : compat R V A).2 L L'

@[simp] lemma add_fam (F G : EndGr R V A) (L : LinOrd A) : (F + G).fam L = F.fam L + G.fam L :=
  rfl

@[simp] lemma smul_fam (c : R) (F : EndGr R V A) (L : LinOrd A) : (c • F).fam L = c • F.fam L :=
  rfl

@[simp] lemma zero_fam (L : LinOrd A) : (0 : EndGr R V A).fam L = 0 := rfl

/-- **A compatible family is determined by its value at one order.** -/
lemma ext {F G : EndGr R V A} (L : LinOrd A) (h : F.fam L = G.fam L) : F = G :=
  Subtype.ext (funext fun L' => by
    show F.fam L' = G.fam L'
    rw [fam_compat F L L', fam_compat G L L', h])

/-- A default order of a finite type. -/
noncomputable def dord (A : Type) [Fintype A] : LinOrd A := LinOrd.ofRank (Fintype.equivFin A)

/-- The parity projections, order by order. -/
noncomputable def parE (b : Bool) : EndGr R V A →ₗ[R] EndGr R V A where
  toFun F := mk (fun L => parML R V b (F.fam L)) fun L L' => by
    dsimp only
    rw [fam_compat F L L', parML_twist]
  map_add' F G := ext (dord A) (map_add (parML R V b) (F.fam _) (G.fam _))
  map_smul' c F := ext (dord A) (map_smul (parML R V b) c (F.fam _))

@[simp] lemma parE_fam (b : Bool) (F : EndGr R V A) (L : LinOrd A) :
    (parE b F).fam L = parML R V b (F.fam L) := rfl

/-- Relabelling, the orders transported. -/
noncomputable def mapE (e : A ≃ B) : EndGr R V A →ₗ[R] EndGr R V B where
  toFun F := mk (fun L => EndOp.mapL R V e (F.fam (LinOrd.map e.symm L))) fun L L' => by
    dsimp only
    rw [fam_compat F (LinOrd.map e.symm L) (LinOrd.map e.symm L'), twist_mapL]
    congr 1
    exact twist_congr (fun c => rsg_map e.symm L L' c) _
  map_add' F G := ext (dord B) (map_add (EndOp.mapL R V e) (F.fam _) (G.fam _))
  map_smul' c F := ext (dord B) (map_smul (EndOp.mapL R V e) c (F.fam _))

@[simp] lemma mapE_fam (e : A ≃ B) (F : EndGr R V A) (L : LinOrd B) :
    (mapE e F).fam L = EndOp.mapL R V e (F.fam (LinOrd.map e.symm L)) := rfl

/-- The identity of `V`. -/
noncomputable def oneE : EndGr R V Unit :=
  mk (fun _ => EndOp.one R V) fun L L' => by
    dsimp only
    rw [LinOrd.eq_of_subsingleton L L', twist_congr (fun c => rsg_self L' c), twist_one]

@[simp] lemma oneE_fam (L : LinOrd Unit) : (oneE : EndGr R V Unit).fam L = EndOp.one R V := rfl

/-- The composite family, through the default orders. -/
noncomputable def compFam (i : A) (F : EndGr R V A) (G : EndGr R V B)
    (L : LinOrd (Without A i ⊕ B)) : EndOp R V (Without A i ⊕ B) :=
  twist R V (rsg R (LinOrd.comp i (dord A) (dord B)) L)
    (kcomp R V (dord A) i (F.fam (dord A)) (G.fam (dord B)))

lemma compFam_compat (i : A) (F : EndGr R V A) (G : EndGr R V B)
    (L L' : LinOrd (Without A i ⊕ B)) :
    compFam i F G L' = twist R V (rsg R L L') (compFam i F G L) := by
  unfold compFam
  rw [twist_twist]
  exact twist_congr (fun c => by rw [mul_comm, rsg_trans]) _

/-- **The composite, through any orders of the factors.** -/
lemma compFam_eq (i : A) (F : EndGr R V A) (G : EndGr R V B) (L : LinOrd A) (M : LinOrd B)
    (L'' : LinOrd (Without A i ⊕ B)) :
    compFam i F G L''
      = twist R V (rsg R (LinOrd.comp i L M) L'') (kcomp R V L i (F.fam L) (G.fam M)) := by
  rw [fam_compat F (dord A) L, fam_compat G (dord B) M, kcomp_twist_right,
    kcomp_twist_left (dord A) L (dord B), twist_twist, twist_twist]
  unfold compFam
  refine twist_congr (fun c => ?_) _
  have h1 := rsg_trans (R := R) (LinOrd.comp i (dord A) (dord B)) (LinOrd.comp i L (dord B))
    (LinOrd.comp i L M) c
  have h2 := rsg_trans (R := R) (LinOrd.comp i (dord A) (dord B)) (LinOrd.comp i L M) L'' c
  linear_combination -h2 - rsg R (LinOrd.comp i L M) L'' c * h1

/-- **The composite at a composite order** is the Koszul composite. -/
lemma compFam_comp (i : A) (F : EndGr R V A) (G : EndGr R V B) (L : LinOrd A) (M : LinOrd B) :
    compFam i F G (LinOrd.comp i L M) = kcomp R V L i (F.fam L) (G.fam M) := by
  rw [compFam_eq i F G L M, twist_congr (fun c => rsg_self _ c), twist_one]

/-- Composition. -/
noncomputable def compE (i : A) :
    EndGr R V A →ₗ[R] EndGr R V B →ₗ[R] EndGr R V (Without A i ⊕ B) :=
  LinearMap.mk₂ R (fun F G => mk (compFam i F G) (compFam_compat i F G))
    (fun F F' G => ext (dord _) (by
      simp only [mk_fam, add_fam, compFam, map_add, LinearMap.add_apply]))
    (fun c F G => ext (dord _) (by
      simp only [mk_fam, smul_fam, compFam, map_smul, LinearMap.smul_apply]))
    (fun F G G' => ext (dord _) (by
      simp only [mk_fam, add_fam, compFam, map_add]))
    (fun c F G => ext (dord _) (by
      simp only [mk_fam, smul_fam, compFam, map_smul]))

@[simp] lemma compE_fam (i : A) (F : EndGr R V A) (G : EndGr R V B)
    (L : LinOrd (Without A i ⊕ B)) : (compE i F G).fam L = compFam i F G L := rfl

/-! ### The operad laws of linear orders, stated with `LinOrd.map` and `LinOrd.comp` -/

section LinOrdLaws

variable {A' B' : Type} [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']

lemma lo_map_refl (L : LinOrd A) : LinOrd.map (Equiv.refl A) L = L :=
  SetOperad.map_refl (S := fun A _ _ => LinOrd A) L

lemma lo_map_trans (e : A ≃ B) (f : B ≃ D) (L : LinOrd A) :
    LinOrd.map (e.trans f) L = LinOrd.map f (LinOrd.map e L) :=
  SetOperad.map_trans (S := fun A _ _ => LinOrd A) e f L

lemma lo_map_symm_map (e : A ≃ B) (L : LinOrd A) : LinOrd.map e.symm (LinOrd.map e L) = L :=
  SetOperad.map_symm_map (S := fun A _ _ => LinOrd A) e L

lemma lo_map_comp (σ' : A ≃ A') (τ : B ≃ B') (i : A) (L : LinOrd A) (M : LinOrd B) :
    LinOrd.map (compEquiv σ' τ i) (LinOrd.comp i L M)
      = LinOrd.comp (σ' i) (LinOrd.map σ' L) (LinOrd.map τ M) :=
  SetOperad.map_comp (S := fun A _ _ => LinOrd A) σ' τ i L M

lemma lo_comp_one (i : A) (L : LinOrd A) :
    LinOrd.map (rightUnitEquiv i) (LinOrd.comp i L LinOrd.one) = L :=
  SetOperad.comp_one (S := fun A _ _ => LinOrd A) i L

lemma lo_one_comp (M : LinOrd B) :
    LinOrd.map (leftUnitEquiv B) (LinOrd.comp () LinOrd.one M) = M :=
  SetOperad.one_comp (S := fun A _ _ => LinOrd A) M

lemma lo_comp_assoc_seq (i : A) (j : B) (L : LinOrd A) (M : LinOrd B) (N : LinOrd D) :
    LinOrd.map (seqEquiv i j D) (LinOrd.comp (Sum.inr j) (LinOrd.comp i L M) N)
      = LinOrd.comp i L (LinOrd.comp j M N) :=
  SetOperad.comp_assoc_seq (S := fun A _ _ => LinOrd A) i j L M N

lemma lo_comp_assoc_par {i k : A} (hik : i ≠ k) (L : LinOrd A) (M : LinOrd B) (N : LinOrd D) :
    LinOrd.map (parEquiv hik B D) (LinOrd.comp (Sum.inl ⟨k, Ne.symm hik⟩) (LinOrd.comp i L M) N)
      = LinOrd.comp (Sum.inl ⟨i, hik⟩) (LinOrd.comp k L N) M :=
  SetOperad.comp_assoc_par (S := fun A _ _ => LinOrd A) hik L M N

end LinOrdLaws

variable (R V) in
/-- **The graded endomorphism operad of a super module is a graded operad.** -/
noncomputable instance instGrOperad : GrOperad R (EndGr R V) where
  par b := parE b
  par_add {A} _ _ F := ext (dord A) (parML_add (F.fam _))
  par_par {A} _ _ b b' F := ext (dord A) (by
    rw [parE_fam, parE_fam, parML_parML]
    split_ifs <;> rfl)
  map e := mapE e
  map_refl {A} _ _ F := ext (dord A) (by
    rw [mapE_fam, Equiv.refl_symm, lo_map_refl]
    rfl)
  map_trans {A B C} _ _ _ _ _ _ e f F := ext (dord C) (by
    have h : (e.trans f).symm = f.symm.trans e.symm := rfl
    rw [mapE_fam, mapE_fam, mapE_fam, h, lo_map_trans]
    rfl)
  map_par {A B} _ _ _ _ e b F := ext (dord B) (by
    rw [mapE_fam, parE_fam, parE_fam, mapE_fam, parML_mapL])
  one := oneE
  par_one := ext (dord Unit) (by rw [parE_fam, oneE_fam, parML_one, if_pos rfl])
  comp i := compE i
  comp_par {A B} _ _ _ _ i p q F G := ext (dord _) (by
    simp only [parE_fam, compE_fam, compFam, parML_twist, parML_kcomp])
  map_comp {A A' B B'} _ _ _ _ _ _ _ _ σ' τ i F G :=
    ext (LinOrd.map (compEquiv σ' τ i) (LinOrd.comp i (dord A) (dord B))) (by
      rw [mapE_fam, compE_fam, lo_map_symm_map, compFam_comp, mapL_kcomp, compE_fam,
        lo_map_comp, compFam_comp, mapE_fam, mapE_fam, lo_map_symm_map, lo_map_symm_map])
  comp_one {A} _ _ i F :=
    ext (LinOrd.map (rightUnitEquiv i) (LinOrd.comp i (dord A) LinOrd.one)) (by
      rw [mapE_fam, compE_fam, lo_map_symm_map, compFam_comp, oneE_fam, kcomp_one,
        lo_comp_one])
  one_comp {B} _ _ G :=
    ext (LinOrd.map (leftUnitEquiv B) (LinOrd.comp () LinOrd.one (dord B))) (by
      rw [mapE_fam, compE_fam, lo_map_symm_map, compFam_comp, oneE_fam, one_kcomp,
        lo_one_comp])
  comp_assoc_seq {A B D} _ _ _ _ _ _ i j F G H :=
    ext (LinOrd.map (seqEquiv i j D)
      (LinOrd.comp (Sum.inr j) (LinOrd.comp i (dord A) (dord B)) (dord D))) (by
      rw [mapE_fam, compE_fam, lo_map_symm_map, compFam_comp, compE_fam, compFam_comp,
        kcomp_assoc_seq, compE_fam, lo_comp_assoc_seq, compFam_comp, compE_fam, compFam_comp])
  comp_assoc_par {A B D} _ _ _ _ _ _ i k hik F q r G H hG hH :=
    ext (LinOrd.map (parEquiv hik B D) (LinOrd.comp (Sum.inl ⟨k, Ne.symm hik⟩)
      (LinOrd.comp i (dord A) (dord B)) (dord D))) (by
      have hG' : parML R V q (G.fam (dord B)) = G.fam (dord B) :=
        congrArg (fun X : EndGr R V B => X.fam (dord B)) hG
      have hH' : parML R V r (H.fam (dord D)) = H.fam (dord D) :=
        congrArg (fun X : EndGr R V D => X.fam (dord D)) hH
      rw [mapE_fam, compE_fam, lo_map_symm_map, compFam_comp, compE_fam, compFam_comp, ← hG',
        ← hH', kcomp_assoc_par, smul_fam, compE_fam, lo_comp_assoc_par, compFam_comp, compE_fam,
        compFam_comp, hG', hH'])

/-- **The compatible family of a multilinear map at an order.** -/
noncomputable def ofFam (L : LinOrd A) (f : EndOp R V A) : EndGr R V A :=
  mk (fun L' => twist R V (rsg R L L') f) fun L' L'' => by
    dsimp only
    rw [twist_twist]
    exact twist_congr (fun c => by rw [mul_comm, rsg_trans]) _

@[simp] lemma ofFam_fam (L : LinOrd A) (f : EndOp R V A) : (ofFam L f).fam L = f := by
  rw [ofFam, mk_fam, twist_congr (fun c => rsg_self L c), twist_one]

lemma ofFam_eq (F : EndGr R V A) (L : LinOrd A) : ofFam L (F.fam L) = F :=
  ext L (ofFam_fam L _)

lemma parE_ofFam (b : Bool) (L : LinOrd A) (f : EndOp R V A) :
    parE b (ofFam L f) = ofFam L (parML R V b f) :=
  ext L (by rw [parE_fam, ofFam_fam, ofFam_fam])

end EndGr

variable {R} in
/-- **An algebra over a graded operad** `P` on a super module `V`: a morphism of graded operads
into the graded endomorphism operad. -/
abbrev GrAlgebra (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P] :=
  GrOperadHom R P (EndGr R V)

end Operad
