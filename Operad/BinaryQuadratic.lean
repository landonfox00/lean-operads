/-
# Binary quadratic operads and their algebras

An operad is **binary quadratic** when it is presented by binary generators and by relators which
are linear combinations of the generators (in arity two) and of their two-fold composites (in arity
three). In the symmetric setting:

* `BinGen G` are binary generators indexed by `G`, and `FreeBin R G` is the free operad on them in
  `R`-modules, the linearization of the free set operad;
* the monomials, with their inputs relabelled by a permutation `σ`, are
  `bin2 g σ = g (x_{σ0}, x_{σ1})`, `binL g h σ = g (h (x_{σ0}, x_{σ1}), x_{σ2})` and
  `binR g h σ = g (x_{σ0}, h (x_{σ1}, x_{σ2}))`;
* `BinPres R r₂ r₃` is the operad presented by relators `r₂` of arity two and `r₃` of arity three;
* binary operations `μ g` on a module `V` define an algebra `binHom μ` over the free operad, whose
  values on the monomials are the expected composites (`binHom_bin2`, `binHom_binL`,
  `binHom_binR`): **an algebra over `BinPres R r₂ r₃` is a family of binary operations under which
  the relators vanish** (`BinPres.algebraEquiv`).

The classical binary quadratic operads follow, each with its algebras:

* `Lie`: antisymmetric brackets with the Jacobi identity (`Lie.algebraEquiv`);
* `PreLie`: right pre-Lie algebras, `(xy)z - x(yz) = (xz)y - x(zy)`;
* `Leib`: right Leibniz algebras, `[[x,y],z] = [[x,z],y] + [x,[y,z]]`;
* `Zinb`: Zinbiel algebras, `(xy)z = x(yz) + x(zy)`;
* `Dend`: Loday's dendriform algebras;
* `Pois`: Poisson algebras;
* `BinAss`, `BinPerm`, `BinDias`: associative, permutative (`(xy)z = x(yz) = x(zy)`) and Loday's
  diassociative algebras, the Koszul duals of `BinAss`, `PreLie` and `Dend`
  (`Operad.BinaryKoszul`).

Over a ring in which `2` is not invertible, antisymmetry `[x,y] = -[y,x]` is weaker than
`[x,x] = 0`: the operad `Lie` is the one presented by the antisymmetry relator.
-/
import Operad.SymPresentation
import Operad.Algebras

universe u v w

namespace Operad

open Sym SetOperad

/-- **Binary generators** indexed by `G`. -/
inductive BinGen (G : Type w) : ℕ → Type w
  | op (g : G) : BinGen G 2

variable (R : Type u) [CommRing R] (G : Type w)

/-- **The free operad on binary generators** `G`, in `R`-modules. -/
abbrev FreeBin := Lin R (FreeSet (BinGen G))

namespace FreeBin

variable {R G}

/-- The expression of a generator. -/
def gen (g : G) : Syn (BinGen G) (Fin 2) := .gen (.op g)

/-- **The monomial `g (x_{σ 0}, x_{σ 1})`.** -/
noncomputable def bin2 (g : G) (σ : Equiv.Perm (Fin 2)) : FreeBin R G (Fin 2) :=
  Finsupp.single (Pres.mk (.map σ (gen g))) 1

/-- **The monomial `g (h (x_{σ 0}, x_{σ 1}), x_{σ 2})`.** -/
noncomputable def binL (g h : G) (σ : Equiv.Perm (Fin 3)) : FreeBin R G (Fin 3) :=
  Finsupp.single
    (Pres.mk (.map (fin3Left.symm.trans σ) (Syn.bin (gen g) (Syn.bin (gen h) .one .one) .one))) 1

/-- **The monomial `g (x_{σ 0}, h (x_{σ 1}, x_{σ 2}))`.** -/
noncomputable def binR (g h : G) (σ : Equiv.Perm (Fin 3)) : FreeBin R G (Fin 3) :=
  Finsupp.single
    (Pres.mk (.map (fin3Right.symm.trans σ) (Syn.bin (gen g) .one (Syn.bin (gen h) .one .one)))) 1

end FreeBin

/-- **The permutation `0 ↦ a, 1 ↦ b, 2 ↦ c`** of `Fin 3`, to relabel monomials. -/
noncomputable def perm3 (a b c : Fin 3) (h : Function.Bijective ![a, b, c] := by decide) :
    Equiv.Perm (Fin 3) :=
  Equiv.ofBijective _ h

@[simp] lemma perm3_apply (a b c : Fin 3) (h : Function.Bijective ![a, b, c]) (i : Fin 3) :
    perm3 a b c h i = ![a, b, c] i := rfl

variable {R G}

/-- **Relators of arity two and three**, as a family of relators. -/
def rel23 (r₂ : Set (FreeBin R G (Fin 2))) (r₃ : Set (FreeBin R G (Fin 3))) :
    ∀ n, Set (FreeBin R G (Fin n))
  | 2 => r₂
  | 3 => r₃
  | _ => ∅

lemma forall_rel23 {r₂ : Set (FreeBin R G (Fin 2))} {r₃ : Set (FreeBin R G (Fin 3))}
    {p : ∀ n, FreeBin R G (Fin n) → Prop} :
    (∀ n, ∀ x ∈ rel23 r₂ r₃ n, p n x) ↔ (∀ x ∈ r₂, p 2 x) ∧ ∀ x ∈ r₃, p 3 x := by
  refine ⟨fun h => ⟨h 2, h 3⟩, fun h n x hx => ?_⟩
  rcases n with _ | _ | _ | _ | n
  · simp [rel23] at hx
  · simp [rel23] at hx
  · exact h.1 x hx
  · exact h.2 x hx
  · simp [rel23] at hx

variable (R) in
/-- **The operad presented by binary generators `G` and relators** `r₂` of arity two and `r₃` of
arity three. -/
abbrev BinPres (r₂ : Set (FreeBin R G (Fin 2))) (r₃ : Set (FreeBin R G (Fin 3))) :=
  (SymOperadIdeal.span R (rel23 r₂ r₃)).Quot

/-! ## Algebras -/

section Algebra

variable {V : Type v} [AddCommGroup V] [Module R V]

/-- The generator values given by binary operations. -/
def binVal (μ : G → EndOp R V (Fin 2)) : ∀ n, BinGen G n → Und R (EndOp R V) (Fin n)
  | _, .op g => Und.of R (EndOp R V) (μ g)

/-- **The algebra over the free operad given by binary operations** `μ g` on `V`. -/
noncomputable def binHom (μ : G → EndOp R V (Fin 2)) : SymAlgebra R (FreeBin R G) V :=
  linHomEquiv R (FreeSet.homEquiv.symm (binVal μ))

/-- Generator values in arity two are binary operations. -/
def binValEquiv :
    (∀ n, BinGen G n → Und R (EndOp R V) (Fin n)) ≃ (G → EndOp R V (Fin 2)) where
  toFun f g := (Und.of R (EndOp R V)).symm (f 2 (.op g))
  invFun := binVal
  left_inv f := by
    funext n x
    cases x
    rfl
  right_inv _ := rfl

/-- **Algebras over the free operad on binary generators** are families of binary operations. -/
noncomputable def freeBinEquiv : SymAlgebra R (FreeBin R G) V ≃ (G → EndOp R V (Fin 2)) :=
  (linHomEquiv R).symm.trans (FreeSet.homEquiv.trans binValEquiv)

lemma freeBinEquiv_symm (μ : G → EndOp R V (Fin 2)) : freeBinEquiv.symm μ = binHom μ := rfl

/-- The value of the algebra given by binary operations on a basis element. -/
lemma binHom_single (μ : G → EndOp R V (Fin 2)) {A : Type} [Fintype A] [DecidableEq A]
    (x : Syn (BinGen G) A) :
    (binHom μ).app A (Finsupp.single (Pres.mk x) 1)
      = (Und.of R (EndOp R V)).symm (Syn.eval (binVal μ) x) := by
  show Finsupp.lift (EndOp R V A) R (FreeSet (BinGen G) A) _ (Finsupp.single (Pres.mk x) 1) = _
  simp
  rfl

/-- **The value of a binary monomial**: `g (x_{σ 0}, x_{σ 1})`. -/
lemma binHom_bin2 (μ : G → EndOp R V (Fin 2)) (g : G) (σ : Equiv.Perm (Fin 2)) (w : Fin 2 → V) :
    (binHom μ).app (Fin 2) (FreeBin.bin2 g σ) w = μ g ![w (σ 0), w (σ 1)] := by
  rw [FreeBin.bin2, binHom_single]
  show EndOp.ap (map σ (Und.of R (EndOp R V) (μ g))) w = _
  rw [EndOp.ap_map]
  show μ g _ = _
  congr 1
  funext k
  fin_cases k <;> rfl

/-- **The value of a left two-fold monomial**: `g (h (x_{σ 0}, x_{σ 1}), x_{σ 2})`. -/
lemma binHom_binL (μ : G → EndOp R V (Fin 2)) (g h : G) (σ : Equiv.Perm (Fin 3))
    (w : Fin 3 → V) :
    (binHom μ).app (Fin 3) (FreeBin.binL g h σ) w = μ g ![μ h ![w (σ 0), w (σ 1)], w (σ 2)] := by
  rw [FreeBin.binL, binHom_single]
  show EndOp.ap _ w = _
  simp only [Syn.eval_map, Syn.eval_bin, Syn.eval_one, EndOp.ap_map, EndOp.ap_bin, EndOp.ap_one]
  rfl

/-- **The value of a right two-fold monomial**: `g (x_{σ 0}, h (x_{σ 1}, x_{σ 2}))`. -/
lemma binHom_binR (μ : G → EndOp R V (Fin 2)) (g h : G) (σ : Equiv.Perm (Fin 3))
    (w : Fin 3 → V) :
    (binHom μ).app (Fin 3) (FreeBin.binR g h σ) w = μ g ![w (σ 0), μ h ![w (σ 1), w (σ 2)]] := by
  rw [FreeBin.binR, binHom_single]
  show EndOp.ap _ w = _
  simp only [Syn.eval_map, Syn.eval_bin, Syn.eval_one, EndOp.ap_map, EndOp.ap_bin, EndOp.ap_one]
  rfl

omit [AddCommGroup V] in
lemma vec_three (w : Fin 3 → V) : w = ![w 0, w 1, w 2] := by
  funext k
  fin_cases k <;> rfl

/-- A bilinear operation vanishes when it does on all pairs. -/
lemma endOp_eq_zero_iff₂ (F : EndOp R V (Fin 2)) : F = 0 ↔ ∀ x y, F ![x, y] = 0 := by
  refine ⟨fun h x y => by rw [h]; rfl, fun h => MultilinearMap.ext fun w => ?_⟩
  rw [EndOp.vec_two w]
  exact h _ _

/-- A trilinear operation vanishes when it does on all triples. -/
lemma endOp_eq_zero_iff₃ (F : EndOp R V (Fin 3)) : F = 0 ↔ ∀ x y z, F ![x, y, z] = 0 := by
  refine ⟨fun h x y z => by rw [h]; rfl, fun h => MultilinearMap.ext fun w => ?_⟩
  rw [vec_three w]
  exact h _ _ _

/-- **Algebras over a binary quadratic operad** are the families of binary operations under which
the relators vanish. -/
noncomputable def BinPres.algebraEquiv (r₂ : Set (FreeBin R G (Fin 2)))
    (r₃ : Set (FreeBin R G (Fin 3))) :
    SymAlgebra R (BinPres R r₂ r₃) V ≃
      {μ : G → EndOp R V (Fin 2) //
        (∀ x ∈ r₂, (binHom μ).app _ x = 0) ∧ ∀ x ∈ r₃, (binHom μ).app _ x = 0} :=
  SymOperadIdeal.presHomEquiv.trans <| freeBinEquiv.subtypeEquiv fun φ => by
    rw [← freeBinEquiv_symm, Equiv.symm_apply_apply]
    exact forall_rel23

@[simp] lemma BinPres.algebraEquiv_apply (r₂ : Set (FreeBin R G (Fin 2)))
    (r₃ : Set (FreeBin R G (Fin 3))) (α : SymAlgebra R (BinPres R r₂ r₃) V) (g : G) :
    (BinPres.algebraEquiv r₂ r₃ α).1 g
      = α.app (Fin 2) ((SymOperadIdeal.span R (rel23 r₂ r₃)).proj _
          (Finsupp.single (Pres.mk (FreeBin.gen g)) 1)) := rfl

end Algebra


/-! ## Relators -/

open FreeBin

section Relators

variable (R)

/-- The commutativity relator `g (x₀, x₁) - g (x₁, x₀)`. -/
noncomputable def BinRel.comm (g : G) : FreeBin R G (Fin 2) :=
  bin2 g 1 - bin2 g (Equiv.swap 0 1)

/-- The antisymmetry relator `g (x₀, x₁) + g (x₁, x₀)`. -/
noncomputable def BinRel.antisymm (g : G) : FreeBin R G (Fin 2) :=
  bin2 g 1 + bin2 g (Equiv.swap 0 1)

/-- The associativity relator `g (g (x₀, x₁), x₂) - g (x₀, g (x₁, x₂))`. -/
noncomputable def BinRel.assoc (g : G) : FreeBin R G (Fin 3) := binL g g 1 - binR g g 1

/-- The Jacobi relator `[[x₀, x₁], x₂] + [[x₁, x₂], x₀] + [[x₂, x₀], x₁]`, for `[-,-] = g`. -/
noncomputable def BinRel.jacobi (g : G) : FreeBin R G (Fin 3) :=
  binL g g 1 + binL g g (perm3 1 2 0) + binL g g (perm3 2 0 1)

/-- The right pre-Lie relator `(x₀x₁)x₂ - x₀(x₁x₂) - ((x₀x₂)x₁ - x₀(x₂x₁))`, for the product
`g`. -/
noncomputable def BinRel.preLie (g : G) : FreeBin R G (Fin 3) :=
  binL g g 1 - binR g g 1 - (binL g g (perm3 0 2 1) - binR g g (perm3 0 2 1))

/-- The right Leibniz relator `[[x₀, x₁], x₂] - ([[x₀, x₂], x₁] + [x₀, [x₁, x₂]])`, for
`[-,-] = g`. -/
noncomputable def BinRel.leib (g : G) : FreeBin R G (Fin 3) :=
  binL g g 1 - (binL g g (perm3 0 2 1) + binR g g 1)

/-- The Zinbiel relator `(x₀x₁)x₂ - (x₀(x₁x₂) + x₀(x₂x₁))`, for the product `g`. -/
noncomputable def BinRel.zinb (g : G) : FreeBin R G (Fin 3) :=
  binL g g 1 - (binR g g 1 + binR g g (perm3 0 2 1))

/-- The Leibniz rule relator `[x₀, x₁x₂] - ([x₀, x₁]x₂ + x₁[x₀, x₂])`, for the product `m` and
the bracket `b`. -/
noncomputable def BinRel.leibnizRule (m b : G) : FreeBin R G (Fin 3) :=
  binR b m 1 - (binL m b 1 + binR m b (perm3 1 0 2))

/-- The first dendriform relator `(x₀ ≺ x₁) ≺ x₂ - (x₀ ≺ (x₁ ≺ x₂) + x₀ ≺ (x₁ ≻ x₂))`. -/
noncomputable def BinRel.dend₁ : FreeBin R DiOp (Fin 3) :=
  binL .left .left 1 - (binR .left .left 1 + binR .left .right 1)

/-- The second dendriform relator `(x₀ ≻ x₁) ≺ x₂ - x₀ ≻ (x₁ ≺ x₂)`. -/
noncomputable def BinRel.dend₂ : FreeBin R DiOp (Fin 3) :=
  binL .left .right 1 - binR .right .left 1

/-- The third dendriform relator `x₀ ≻ (x₁ ≻ x₂) - ((x₀ ≺ x₁) ≻ x₂ + (x₀ ≻ x₁) ≻ x₂)`. -/
noncomputable def BinRel.dend₃ : FreeBin R DiOp (Fin 3) :=
  binR .right .right 1 - (binL .right .left 1 + binL .right .right 1)

/-- The right permutativity relator `x₀(x₁x₂) - x₀(x₂x₁)`, for the product `g`. -/
noncomputable def BinRel.perm (g : G) : FreeBin R G (Fin 3) :=
  binR g g 1 - binR g g (perm3 0 2 1)

/-- The first diassociative relator `(x₀ ⊣ x₁) ⊣ x₂ - x₀ ⊣ (x₁ ⊣ x₂)`. -/
noncomputable def BinRel.dias₁ : FreeBin R DiOp (Fin 3) := binL .left .left 1 - binR .left .left 1

/-- The second diassociative relator `(x₀ ⊣ x₁) ⊣ x₂ - x₀ ⊣ (x₁ ⊢ x₂)`. -/
noncomputable def BinRel.dias₂ : FreeBin R DiOp (Fin 3) :=
  binL .left .left 1 - binR .left .right 1

/-- The third diassociative relator `(x₀ ⊢ x₁) ⊣ x₂ - x₀ ⊢ (x₁ ⊣ x₂)`. -/
noncomputable def BinRel.dias₃ : FreeBin R DiOp (Fin 3) :=
  binL .left .right 1 - binR .right .left 1

/-- The fourth diassociative relator `(x₀ ⊣ x₁) ⊢ x₂ - x₀ ⊢ (x₁ ⊢ x₂)`. -/
noncomputable def BinRel.dias₄ : FreeBin R DiOp (Fin 3) :=
  binL .right .left 1 - binR .right .right 1

/-- The fifth diassociative relator `(x₀ ⊢ x₁) ⊢ x₂ - x₀ ⊢ (x₁ ⊢ x₂)`. -/
noncomputable def BinRel.dias₅ : FreeBin R DiOp (Fin 3) :=
  binL .right .right 1 - binR .right .right 1

end Relators

section Identities

variable {V : Type v} [AddCommGroup V] [Module R V] (μ : G → EndOp R V (Fin 2))

lemma BinRel.comm_iff (g : G) : (binHom μ).app _ (BinRel.comm R g) = 0 ↔
    ∀ x y, μ g ![x, y] = μ g ![y, x] := by
  rw [endOp_eq_zero_iff₂]
  simp only [BinRel.comm, map_sub, MultilinearMap.sub_apply, binHom_bin2, sub_eq_zero]
  rfl

lemma BinRel.antisymm_iff (g : G) : (binHom μ).app _ (BinRel.antisymm R g) = 0 ↔
    ∀ x y, μ g ![x, y] = -μ g ![y, x] := by
  rw [endOp_eq_zero_iff₂]
  simp only [BinRel.antisymm, map_add, MultilinearMap.add_apply, binHom_bin2,
    ← eq_neg_iff_add_eq_zero]
  rfl

lemma BinRel.assoc_iff (g : G) : (binHom μ).app _ (BinRel.assoc R g) = 0 ↔
    ∀ x y z, μ g ![μ g ![x, y], z] = μ g ![x, μ g ![y, z]] := by
  rw [endOp_eq_zero_iff₃]
  simp only [BinRel.assoc, map_sub, MultilinearMap.sub_apply, binHom_binL, binHom_binR,
    sub_eq_zero]
  rfl

lemma BinRel.jacobi_iff (g : G) : (binHom μ).app _ (BinRel.jacobi R g) = 0 ↔
    ∀ x y z, μ g ![μ g ![x, y], z] + μ g ![μ g ![y, z], x] + μ g ![μ g ![z, x], y] = 0 := by
  rw [endOp_eq_zero_iff₃]
  simp only [BinRel.jacobi, map_add, MultilinearMap.add_apply, binHom_binL]
  rfl

lemma BinRel.preLie_iff (g : G) : (binHom μ).app _ (BinRel.preLie R g) = 0 ↔
    ∀ x y z, μ g ![μ g ![x, y], z] - μ g ![x, μ g ![y, z]]
      = μ g ![μ g ![x, z], y] - μ g ![x, μ g ![z, y]] := by
  rw [endOp_eq_zero_iff₃]
  simp only [BinRel.preLie, map_sub, MultilinearMap.sub_apply, binHom_binL, binHom_binR,
    sub_eq_zero]
  rfl

lemma BinRel.leib_iff (g : G) : (binHom μ).app _ (BinRel.leib R g) = 0 ↔
    ∀ x y z, μ g ![μ g ![x, y], z] = μ g ![μ g ![x, z], y] + μ g ![x, μ g ![y, z]] := by
  rw [endOp_eq_zero_iff₃]
  simp only [BinRel.leib, map_add, map_sub, MultilinearMap.add_apply, MultilinearMap.sub_apply,
    binHom_binL, binHom_binR, sub_eq_zero]
  rfl

lemma BinRel.zinb_iff (g : G) : (binHom μ).app _ (BinRel.zinb R g) = 0 ↔
    ∀ x y z, μ g ![μ g ![x, y], z] = μ g ![x, μ g ![y, z]] + μ g ![x, μ g ![z, y]] := by
  rw [endOp_eq_zero_iff₃]
  simp only [BinRel.zinb, map_add, map_sub, MultilinearMap.add_apply, MultilinearMap.sub_apply,
    binHom_binL, binHom_binR, sub_eq_zero]
  rfl

lemma BinRel.perm_iff (g : G) : (binHom μ).app _ (BinRel.perm R g) = 0 ↔
    ∀ x y z, μ g ![x, μ g ![y, z]] = μ g ![x, μ g ![z, y]] := by
  rw [endOp_eq_zero_iff₃]
  simp only [BinRel.perm, map_sub, MultilinearMap.sub_apply, binHom_binR, sub_eq_zero]
  rfl

lemma BinRel.leibnizRule_iff (m b : G) : (binHom μ).app _ (BinRel.leibnizRule R m b) = 0 ↔
    ∀ x y z, μ b ![x, μ m ![y, z]] = μ m ![μ b ![x, y], z] + μ m ![y, μ b ![x, z]] := by
  rw [endOp_eq_zero_iff₃]
  simp only [BinRel.leibnizRule, map_add, map_sub, MultilinearMap.add_apply,
    MultilinearMap.sub_apply, binHom_binL, binHom_binR, sub_eq_zero]
  rfl

section Dend

variable {V : Type v} [AddCommGroup V] [Module R V] (μ : DiOp → EndOp R V (Fin 2))

lemma BinRel.dend₁_iff : (binHom μ).app _ (BinRel.dend₁ R) = 0 ↔ ∀ x y z,
    μ .left ![μ .left ![x, y], z]
      = μ .left ![x, μ .left ![y, z]] + μ .left ![x, μ .right ![y, z]] := by
  rw [endOp_eq_zero_iff₃]
  simp only [BinRel.dend₁, map_add, map_sub, MultilinearMap.add_apply, MultilinearMap.sub_apply,
    binHom_binL, binHom_binR, sub_eq_zero]
  rfl

lemma BinRel.dend₂_iff : (binHom μ).app _ (BinRel.dend₂ R) = 0 ↔
    ∀ x y z, μ .left ![μ .right ![x, y], z] = μ .right ![x, μ .left ![y, z]] := by
  rw [endOp_eq_zero_iff₃]
  simp only [BinRel.dend₂, map_sub, MultilinearMap.sub_apply, binHom_binL, binHom_binR,
    sub_eq_zero]
  rfl

lemma BinRel.dend₃_iff : (binHom μ).app _ (BinRel.dend₃ R) = 0 ↔ ∀ x y z,
    μ .right ![x, μ .right ![y, z]]
      = μ .right ![μ .left ![x, y], z] + μ .right ![μ .right ![x, y], z] := by
  rw [endOp_eq_zero_iff₃]
  simp only [BinRel.dend₃, map_add, map_sub, MultilinearMap.add_apply, MultilinearMap.sub_apply,
    binHom_binL, binHom_binR, sub_eq_zero]
  rfl

lemma BinRel.dias₁_iff : (binHom μ).app _ (BinRel.dias₁ R) = 0 ↔
    ∀ x y z, μ .left ![μ .left ![x, y], z] = μ .left ![x, μ .left ![y, z]] := by
  rw [endOp_eq_zero_iff₃]
  simp only [BinRel.dias₁, map_sub, MultilinearMap.sub_apply, binHom_binL, binHom_binR,
    sub_eq_zero]
  rfl

lemma BinRel.dias₂_iff : (binHom μ).app _ (BinRel.dias₂ R) = 0 ↔
    ∀ x y z, μ .left ![μ .left ![x, y], z] = μ .left ![x, μ .right ![y, z]] := by
  rw [endOp_eq_zero_iff₃]
  simp only [BinRel.dias₂, map_sub, MultilinearMap.sub_apply, binHom_binL, binHom_binR,
    sub_eq_zero]
  rfl

lemma BinRel.dias₃_iff : (binHom μ).app _ (BinRel.dias₃ R) = 0 ↔
    ∀ x y z, μ .left ![μ .right ![x, y], z] = μ .right ![x, μ .left ![y, z]] := by
  rw [endOp_eq_zero_iff₃]
  simp only [BinRel.dias₃, map_sub, MultilinearMap.sub_apply, binHom_binL, binHom_binR,
    sub_eq_zero]
  rfl

lemma BinRel.dias₄_iff : (binHom μ).app _ (BinRel.dias₄ R) = 0 ↔
    ∀ x y z, μ .right ![μ .left ![x, y], z] = μ .right ![x, μ .right ![y, z]] := by
  rw [endOp_eq_zero_iff₃]
  simp only [BinRel.dias₄, map_sub, MultilinearMap.sub_apply, binHom_binL, binHom_binR,
    sub_eq_zero]
  rfl

lemma BinRel.dias₅_iff : (binHom μ).app _ (BinRel.dias₅ R) = 0 ↔
    ∀ x y z, μ .right ![μ .right ![x, y], z] = μ .right ![x, μ .right ![y, z]] := by
  rw [endOp_eq_zero_iff₃]
  simp only [BinRel.dias₅, map_sub, MultilinearMap.sub_apply, binHom_binL, binHom_binR,
    sub_eq_zero]
  rfl

end Dend

end Identities

/-! ## The operads -/

/-- The two generators of a Poisson algebra. -/
inductive PoisOp
  /-- The commutative product. -/
  | mul
  /-- The Lie bracket. -/
  | bracket
  deriving DecidableEq

variable (R)

/-- **The Lie operad**: an antisymmetric bracket satisfying the Jacobi identity. -/
abbrev Lie := BinPres R {BinRel.antisymm R ()} {BinRel.jacobi R ()}

/-- **The right pre-Lie operad.** -/
abbrev PreLie := BinPres R (∅ : Set (FreeBin R Unit (Fin 2))) {BinRel.preLie R ()}

/-- **The right Leibniz operad.** -/
abbrev Leib := BinPres R (∅ : Set (FreeBin R Unit (Fin 2))) {BinRel.leib R ()}

/-- **The Zinbiel operad.** -/
abbrev Zinb := BinPres R (∅ : Set (FreeBin R Unit (Fin 2))) {BinRel.zinb R ()}

/-- **Loday's dendriform operad**, generated by `≺` (`DiOp.left`) and `≻` (`DiOp.right`). -/
abbrev Dend :=
  BinPres R (∅ : Set (FreeBin R DiOp (Fin 2))) {BinRel.dend₁ R, BinRel.dend₂ R, BinRel.dend₃ R}

/-- **The Poisson operad**: a commutative associative product and a Lie bracket, related by the
Leibniz rule. -/
abbrev Pois := BinPres R {BinRel.comm R PoisOp.mul, BinRel.antisymm R PoisOp.bracket}
  {BinRel.assoc R PoisOp.mul, BinRel.jacobi R PoisOp.bracket,
    BinRel.leibnizRule R PoisOp.mul PoisOp.bracket}

/-- **The associative operad**, as a binary quadratic operad. -/
abbrev BinAss := BinPres R (∅ : Set (FreeBin R Unit (Fin 2))) {BinRel.assoc R ()}

/-- **The permutative operad**, as a binary quadratic operad: an associative product with
`x(yz) = x(zy)`. -/
abbrev BinPerm :=
  BinPres R (∅ : Set (FreeBin R Unit (Fin 2))) {BinRel.assoc R (), BinRel.perm R ()}

/-- **Loday's diassociative operad**, generated by `⊣` (`DiOp.left`) and `⊢` (`DiOp.right`). -/
abbrev BinDias := BinPres R (∅ : Set (FreeBin R DiOp (Fin 2)))
  {BinRel.dias₁ R, BinRel.dias₂ R, BinRel.dias₃ R, BinRel.dias₄ R, BinRel.dias₅ R}

/-! ## Their algebras -/

variable (V : Type v) [AddCommGroup V] [Module R V]

/-- **A Lie algebra structure** on `V`: an antisymmetric bracket with the Jacobi identity. -/
structure LieAlg where
  /-- The bracket. -/
  bracket : EndOp R V (Fin 2)
  antisymm : ∀ x y, bracket ![x, y] = -bracket ![y, x]
  jacobi : ∀ x y z, bracket ![bracket ![x, y], z] + bracket ![bracket ![y, z], x]
    + bracket ![bracket ![z, x], y] = 0

/-- **A right pre-Lie algebra structure** on `V`: `(xy)z - x(yz) = (xz)y - x(zy)`. -/
structure PreLieAlg where
  /-- The product. -/
  mul : EndOp R V (Fin 2)
  preLie : ∀ x y z, mul ![mul ![x, y], z] - mul ![x, mul ![y, z]]
    = mul ![mul ![x, z], y] - mul ![x, mul ![z, y]]

/-- **A right Leibniz algebra structure** on `V`: `[[x,y],z] = [[x,z],y] + [x,[y,z]]`. -/
structure LeibAlg where
  /-- The bracket. -/
  bracket : EndOp R V (Fin 2)
  leibniz : ∀ x y z, bracket ![bracket ![x, y], z]
    = bracket ![bracket ![x, z], y] + bracket ![x, bracket ![y, z]]

/-- **A Zinbiel algebra structure** on `V`: `(xy)z = x(yz) + x(zy)`. -/
structure ZinbAlg where
  /-- The product. -/
  mul : EndOp R V (Fin 2)
  zinbiel : ∀ x y z, mul ![mul ![x, y], z] = mul ![x, mul ![y, z]] + mul ![x, mul ![z, y]]

/-- **A dendriform algebra structure** on `V` (Loday): `≺` and `≻` with
`(x ≺ y) ≺ z = x ≺ (y ≺ z) + x ≺ (y ≻ z)`, `(x ≻ y) ≺ z = x ≻ (y ≺ z)` and
`x ≻ (y ≻ z) = (x ≺ y) ≻ z + (x ≻ y) ≻ z`. -/
structure DendAlg where
  /-- `x ≺ y`. -/
  left : EndOp R V (Fin 2)
  /-- `x ≻ y`. -/
  right : EndOp R V (Fin 2)
  d1 : ∀ x y z, left ![left ![x, y], z] = left ![x, left ![y, z]] + left ![x, right ![y, z]]
  d2 : ∀ x y z, left ![right ![x, y], z] = right ![x, left ![y, z]]
  d3 : ∀ x y z, right ![x, right ![y, z]] = right ![left ![x, y], z] + right ![right ![x, y], z]

/-- **A Poisson algebra structure** on `V`: a commutative associative product, a Lie bracket, and
the Leibniz rule `[x, yz] = [x, y]z + y[x, z]`. -/
structure PoisAlg where
  /-- The product. -/
  mul : EndOp R V (Fin 2)
  /-- The bracket. -/
  bracket : EndOp R V (Fin 2)
  comm : ∀ x y, mul ![x, y] = mul ![y, x]
  assoc : ∀ x y z, mul ![mul ![x, y], z] = mul ![x, mul ![y, z]]
  antisymm : ∀ x y, bracket ![x, y] = -bracket ![y, x]
  jacobi : ∀ x y z, bracket ![bracket ![x, y], z] + bracket ![bracket ![y, z], x]
    + bracket ![bracket ![z, x], y] = 0
  leibniz : ∀ x y z, bracket ![x, mul ![y, z]]
    = mul ![bracket ![x, y], z] + mul ![y, bracket ![x, z]]

variable {R V}

/-- **Algebras over the Lie operad are Lie algebras** (with an antisymmetric bracket). -/
noncomputable def Lie.algebraEquiv : SymAlgebra R (Lie R) V ≃ LieAlg R V :=
  (BinPres.algebraEquiv _ _).trans
    { toFun := fun μ =>
        { bracket := μ.1 ()
          antisymm := (BinRel.antisymm_iff μ.1 ()).1 (μ.2.1 _ rfl)
          jacobi := (BinRel.jacobi_iff μ.1 ()).1 (μ.2.2 _ rfl) }
      invFun := fun a => ⟨fun _ => a.bracket,
        fun _ h => h ▸ (BinRel.antisymm_iff _ ()).2 a.antisymm,
        fun _ h => h ▸ (BinRel.jacobi_iff _ ()).2 a.jacobi⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- **Algebras over the pre-Lie operad are right pre-Lie algebras.** -/
noncomputable def PreLie.algebraEquiv : SymAlgebra R (PreLie R) V ≃ PreLieAlg R V :=
  (BinPres.algebraEquiv _ _).trans
    { toFun := fun μ => ⟨μ.1 (), (BinRel.preLie_iff μ.1 ()).1 (μ.2.2 _ rfl)⟩
      invFun := fun a => ⟨fun _ => a.mul, fun _ h => h.elim,
        fun _ h => h ▸ (BinRel.preLie_iff _ ()).2 a.preLie⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- **Algebras over the Leibniz operad are right Leibniz algebras.** -/
noncomputable def Leib.algebraEquiv : SymAlgebra R (Leib R) V ≃ LeibAlg R V :=
  (BinPres.algebraEquiv _ _).trans
    { toFun := fun μ => ⟨μ.1 (), (BinRel.leib_iff μ.1 ()).1 (μ.2.2 _ rfl)⟩
      invFun := fun a => ⟨fun _ => a.bracket, fun _ h => h.elim,
        fun _ h => h ▸ (BinRel.leib_iff _ ()).2 a.leibniz⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- **Algebras over the Zinbiel operad are Zinbiel algebras.** -/
noncomputable def Zinb.algebraEquiv : SymAlgebra R (Zinb R) V ≃ ZinbAlg R V :=
  (BinPres.algebraEquiv _ _).trans
    { toFun := fun μ => ⟨μ.1 (), (BinRel.zinb_iff μ.1 ()).1 (μ.2.2 _ rfl)⟩
      invFun := fun a => ⟨fun _ => a.mul, fun _ h => h.elim,
        fun _ h => h ▸ (BinRel.zinb_iff _ ()).2 a.zinbiel⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- **Algebras over the dendriform operad are dendriform algebras.** -/
noncomputable def Dend.algebraEquiv : SymAlgebra R (Dend R) V ≃ DendAlg R V :=
  (BinPres.algebraEquiv _ _).trans
    { toFun := fun μ =>
        { left := μ.1 .left
          right := μ.1 .right
          d1 := (BinRel.dend₁_iff μ.1).1 (μ.2.2 _ (Or.inl rfl))
          d2 := (BinRel.dend₂_iff μ.1).1 (μ.2.2 _ (Or.inr (Or.inl rfl)))
          d3 := (BinRel.dend₃_iff μ.1).1 (μ.2.2 _ (Or.inr (Or.inr rfl))) }
      invFun := fun a => ⟨fun o => match o with | .left => a.left | .right => a.right,
        fun _ h => h.elim, fun _ h => by
          rcases h with rfl | rfl | rfl
          · exact (BinRel.dend₁_iff _).2 a.d1
          · exact (BinRel.dend₂_iff _).2 a.d2
          · exact (BinRel.dend₃_iff _).2 a.d3⟩
      left_inv := fun μ => Subtype.ext (funext fun o => by cases o <;> rfl)
      right_inv := fun _ => rfl }

/-- **Algebras over the Poisson operad are Poisson algebras.** -/
noncomputable def Pois.algebraEquiv : SymAlgebra R (Pois R) V ≃ PoisAlg R V :=
  (BinPres.algebraEquiv _ _).trans
    { toFun := fun μ =>
        { mul := μ.1 .mul
          bracket := μ.1 .bracket
          comm := (BinRel.comm_iff μ.1 _).1 (μ.2.1 _ (Or.inl rfl))
          assoc := (BinRel.assoc_iff μ.1 _).1 (μ.2.2 _ (Or.inl rfl))
          antisymm := (BinRel.antisymm_iff μ.1 _).1 (μ.2.1 _ (Or.inr rfl))
          jacobi := (BinRel.jacobi_iff μ.1 _).1 (μ.2.2 _ (Or.inr (Or.inl rfl)))
          leibniz := (BinRel.leibnizRule_iff μ.1 _ _).1 (μ.2.2 _ (Or.inr (Or.inr rfl))) }
      invFun := fun a => ⟨fun o => match o with | .mul => a.mul | .bracket => a.bracket,
        fun _ h => by
          rcases h with rfl | rfl
          · exact (BinRel.comm_iff _ _).2 a.comm
          · exact (BinRel.antisymm_iff _ _).2 a.antisymm,
        fun _ h => by
          rcases h with rfl | rfl | rfl
          · exact (BinRel.assoc_iff _ _).2 a.assoc
          · exact (BinRel.jacobi_iff _ _).2 a.jacobi
          · exact (BinRel.leibnizRule_iff _ _ _).2 a.leibniz⟩
      left_inv := fun μ => Subtype.ext (funext fun o => by cases o <;> rfl)
      right_inv := fun _ => rfl }

/-- **Algebras over the binary quadratic associative operad are associative algebras.** -/
noncomputable def BinAss.algebraEquiv : SymAlgebra R (BinAss R) V ≃ AssAlg R V :=
  (BinPres.algebraEquiv _ _).trans
    { toFun := fun μ => ⟨μ.1 (), (BinRel.assoc_iff μ.1 ()).1 (μ.2.2 _ rfl)⟩
      invFun := fun a => ⟨fun _ => a.mul, fun _ h => h.elim,
        fun _ h => h ▸ (BinRel.assoc_iff _ ()).2 a.assoc⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- **Algebras over the permutative operad are permutative algebras.** -/
noncomputable def BinPerm.algebraEquiv : SymAlgebra R (BinPerm R) V ≃ PermAlg R V :=
  (BinPres.algebraEquiv _ _).trans
    { toFun := fun μ => ⟨μ.1 (), (BinRel.assoc_iff μ.1 ()).1 (μ.2.2 _ (Or.inl rfl)),
        (BinRel.perm_iff μ.1 ()).1 (μ.2.2 _ (Or.inr rfl))⟩
      invFun := fun a => ⟨fun _ => a.mul, fun _ h => h.elim, fun _ h => by
          rcases h with rfl | rfl
          · exact (BinRel.assoc_iff _ ()).2 a.assoc
          · exact (BinRel.perm_iff _ ()).2 a.perm⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- **Algebras over the diassociative operad are associative dialgebras.** -/
noncomputable def BinDias.algebraEquiv : SymAlgebra R (BinDias R) V ≃ DiAlg R V :=
  (BinPres.algebraEquiv _ _).trans
    { toFun := fun μ =>
        { left := μ.1 .left
          right := μ.1 .right
          d1 := (BinRel.dias₁_iff μ.1).1 (μ.2.2 _ (Or.inl rfl))
          d2 := (BinRel.dias₂_iff μ.1).1 (μ.2.2 _ (Or.inr (Or.inl rfl)))
          d3 := (BinRel.dias₃_iff μ.1).1 (μ.2.2 _ (Or.inr (Or.inr (Or.inl rfl))))
          d4 := (BinRel.dias₄_iff μ.1).1 (μ.2.2 _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
          d5 := (BinRel.dias₅_iff μ.1).1 (μ.2.2 _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) }
      invFun := fun a => ⟨fun o => match o with | .left => a.left | .right => a.right,
        fun _ h => h.elim, fun _ h => by
          rcases h with rfl | rfl | rfl | rfl | rfl
          · exact (BinRel.dias₁_iff _).2 a.d1
          · exact (BinRel.dias₂_iff _).2 a.d2
          · exact (BinRel.dias₃_iff _).2 a.d3
          · exact (BinRel.dias₄_iff _).2 a.d4
          · exact (BinRel.dias₅_iff _).2 a.d5⟩
      left_inv := fun μ => Subtype.ext (funext fun o => by cases o <;> rfl)
      right_inv := fun _ => rfl }

end Operad
