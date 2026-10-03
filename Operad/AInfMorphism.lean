/-
# ∞-morphisms of A∞-algebras

**Multilinear series** `V ⇝ W` are families of multilinear maps `V^n → W`, one in each arity
(`MSer`). They compose along compositions of the arity, `(q ∘ p)ₙ = ∑_c q_ℓ(p_{c₁}, …, p_{c_ℓ})`
(`MSer.comp`), associatively (`MSer.comp_assoc`) and with the identity series as unit
(`MSer.comp_id`, `MSer.id_comp`): this is the algebraic counterpart of the composition of formal
multilinear series, and the proofs follow mathlib's.

For a super module `(V, ε)`, write `V̂ = V × V` for `V ⊕ θV`, the extension by an odd parameter `θ`
with `θ² = 0`. An even series `f` extends to the series `f̂ : V̂ ⇝ Ŵ`,
`f̂((x₁, y₁), …) = (f(x), ∑ₛ f(εx₁, …, εx_{s-1}, y_s, x_{s+1}, …))` (`MSer.hat`): `θ` passes the
inputs before it, which costs `ε` on each. **Extension is functorial on even series**
(`MSer.hat_comp`), and the identity extends to the identity (`MSer.hat_id`).

An A∞-structure `b` in the bar convention (`Operad.AInf`) is encoded by the series
`β_b : V ⇝ V̂`, `x ↦ (x, b₀ x)` in arity one and `x ↦ (0, bₙ₋₁ x)` in arity `n ≥ 2`
(`AInf.bser`): the codifferential `1 + θ D_b`. An **∞-morphism** `f : (V, b) ⇝ (W, b')` is an even
series with `f̂ ∘ β_b = β_{b'} ∘ f` (`AInf.IsInfMorph`). Its first component says
`f ∘ (insertions of b) = b' ∘ (f, …, f)` summed over compositions; in arity one, `f₁` is a chain
map (`IsInfMorph.chain`), and in arity two, `f₁` is multiplicative up to the homotopy `f₂`
(`IsInfMorph.mul`).

**∞-morphisms compose** (`IsInfMorph.comp`): `(g ∘ f)^ ∘ β_b = ĝ ∘ f̂ ∘ β_b = ĝ ∘ β_{b'} ∘ f =
β_{b''} ∘ g ∘ f`, by functoriality of the extension and associativity; the identity is an
∞-morphism (`IsInfMorph.id`); and a linear map `φ` is an ∞-morphism, concentrated in arity one,
exactly when it is a strict morphism, `φ ∘ bₙ = b'ₙ ∘ φ^⊗(n+1)` (`isInfMorph_lin_iff`).
-/
import Operad.AInfinity
import Mathlib.Analysis.Analytic.Composition

universe u

namespace Operad

open Finset

/-! ## Multilinear series and their composition -/

variable (R : Type u) [CommRing R]

/-- **A multilinear series** from `V` to `W`: a multilinear map `V^n → W` in every arity. -/
abbrev MSer (V W : Type*) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] :=
  ∀ n : ℕ, MultilinearMap R (fun _ : Fin n => V) W

namespace MSer

variable {R} {V W X Y : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]

/-- Components of equal arities agree on corresponding inputs. -/
lemma congr (p : MSer R V W) {m n : ℕ} (h : m = n) {v : Fin m → V} {w : Fin n → V}
    (hv : ∀ (i : ℕ) (him : i < m) (hin : i < n), v ⟨i, him⟩ = w ⟨i, hin⟩) : p m v = p n w := by
  subst h
  congr 1
  funext i
  exact hv i i.2 i.2

/-- The values of the components of `p` on the blocks of a composition. -/
def applyComp (p : MSer R V W) {n : ℕ} (c : Composition n) (v : Fin n → V) :
    Fin c.length → W :=
  fun i => p (c.blocksFun i) (v ∘ c.embedding i)

lemma applyComp_update (p : MSer R V W) {n : ℕ} (c : Composition n) (j : Fin n) (v : Fin n → V)
    (z : V) :
    applyComp p c (Function.update v j z) =
      Function.update (applyComp p c v) (c.index j)
        (p (c.blocksFun (c.index j))
          (Function.update (v ∘ c.embedding (c.index j)) (c.invEmbedding j) z)) := by
  ext k
  by_cases h : k = c.index j
  · rw [h]
    let r : Fin (c.blocksFun (c.index j)) → Fin n := c.embedding (c.index j)
    simp only [Function.update_self]
    change p (c.blocksFun (c.index j)) (Function.update v j z ∘ r) = _
    let j' := c.invEmbedding j
    suffices B : Function.update v j z ∘ r = Function.update (v ∘ r) j' z by rw [B]
    suffices C : Function.update v (r j') z ∘ r = Function.update (v ∘ r) j' z by
      convert C using 3
      exact (c.embedding_comp_inv j).symm
    exact Function.update_comp_eq_of_injective _ (c.embedding _).injective _ _
  · simp only [h, Function.update_of_ne, Ne, not_false_iff]
    let r : Fin (c.blocksFun k) → Fin n := c.embedding k
    change p (c.blocksFun k) (Function.update v j z ∘ r) = p (c.blocksFun k) (v ∘ r)
    suffices B : Function.update v j z ∘ r = v ∘ r by rw [B]
    apply Function.update_comp_eq_of_notMem_range
    rwa [c.mem_range_embedding_iff']

lemma applyComp_ones (p : MSer R V W) (n : ℕ) :
    applyComp p (Composition.ones n) =
      fun v i => p 1 fun _ => v (Fin.castLE (Composition.length_le _) i) := by
  funext v i
  apply p.congr (Composition.ones_blocksFun _ _)
  intro j hjn hj1
  obtain rfl : j = 0 := by omega
  refine congr_arg v ?_
  rw [Fin.ext_iff, Fin.val_castLE, Composition.ones_embedding, Fin.val_mk]

/-- **The composite along a composition**: `q_ℓ` applied to the values of `p` on the blocks. -/
def compAlong (q : MSer R W X) (p : MSer R V W) {n : ℕ} (c : Composition n) :
    MultilinearMap R (fun _ : Fin n => V) X :=
  MultilinearMap.mk' (fun v => q c.length (applyComp p c v))
    (fun v i x y => by simp only [applyComp_update, MultilinearMap.map_update_add])
    (fun v i r x => by simp only [applyComp_update, MultilinearMap.map_update_smul])

@[simp] lemma compAlong_apply (q : MSer R W X) (p : MSer R V W) {n : ℕ} (c : Composition n)
    (v : Fin n → V) : compAlong q p c v = q c.length (applyComp p c v) :=
  rfl

/-- **The composite of two multilinear series**: `(q ∘ p)ₙ = ∑_c q_ℓ(p_{c₁}, …, p_{c_ℓ})`, the sum
running over the compositions `c` of `n`. -/
def comp (q : MSer R W X) (p : MSer R V W) : MSer R V X :=
  fun n => ∑ c : Composition n, compAlong q p c

lemma comp_apply (q : MSer R W X) (p : MSer R V W) (n : ℕ) (v : Fin n → V) :
    comp q p n v = ∑ c : Composition n, q c.length (applyComp p c v) := by
  simp [comp, MultilinearMap.sum_apply]

/-- **Composition of multilinear series is associative.** -/
theorem comp_assoc (r : MSer R X Y) (q : MSer R W X) (p : MSer R V W) :
    comp (comp r q) p = comp r (comp q p) := by
  funext n
  ext v
  let f : (Σ a : Composition n, Composition a.length) → Y := fun c =>
    r c.2.length (applyComp q c.2 (applyComp p c.1 v))
  let g : (Σ c : Composition n, ∀ i : Fin c.length, Composition (c.blocksFun i)) → Y := fun c =>
    r c.1.length fun i : Fin c.1.length =>
      q (c.2 i).length (applyComp p (c.2 i) (v ∘ c.1.embedding i))
  suffices ∑ c, f c = ∑ c, g c by
    simpa +unfoldPartialApp only [comp, MultilinearMap.sum_apply, compAlong_apply,
      Finset.sum_sigma', applyComp, MultilinearMap.map_sum]
  rw [← Equiv.sum_comp (Composition.sigmaEquivSigmaPi n) g]
  apply Finset.sum_congr rfl
  rintro ⟨a, b⟩ _
  dsimp [Composition.sigmaEquivSigmaPi]
  apply r.congr (Composition.length_gather a b).symm
  intro i hi1 hi2
  apply q.congr (Composition.length_sigmaCompositionAux a b _).symm
  intro j hj1 hj2
  apply p.congr (Composition.blocksFun_sigmaCompositionAux a b _ _).symm
  intro k hk1 hk2
  refine congr_arg v (Fin.ext ?_)
  dsimp [Composition.embedding]
  rw [← add_assoc, ← Composition.sizeUpTo_sizeUpTo_add _ _ hi1 hj1]
  rfl

variable (R V) in
/-- **The identity series**: the identity in arity one, zero elsewhere. -/
def id : MSer R V V
  | 1 => MultilinearMap.ofSubsingleton R V V 0 LinearMap.id
  | _ => 0

@[simp] lemma id_apply_one (v : Fin 1 → V) : id R V 1 v = v 0 :=
  rfl

lemma id_apply_one' {n : ℕ} (h : n = 1) (v : Fin n → V) :
    id R V n v = v ⟨0, h.symm ▸ zero_lt_one⟩ := by
  subst h
  rfl

lemma id_of_ne_one {n : ℕ} (h : n ≠ 1) : id R V n = 0 := by
  match n, h with
  | 0, _ => rfl
  | n + 2, _ => rfl

/-- **The identity is a right unit.** -/
@[simp] theorem comp_id (p : MSer R V W) : comp p (id R V) = p := by
  funext n
  rw [comp, Finset.sum_eq_single (Composition.ones n)]
  · ext v
    rw [compAlong_apply]
    apply p.congr (Composition.ones_length n)
    intros
    rw [applyComp_ones]
    refine congr_arg v ?_
    rw [Fin.ext_iff, Fin.val_castLE, Fin.val_mk]
  · intro b _ hb
    obtain ⟨k, hk, lt_k⟩ : ∃ (k : ℕ), k ∈ Composition.blocks b ∧ 1 < k :=
      Composition.ne_ones_iff.1 hb
    obtain ⟨i, hi⟩ : ∃ (i : Fin b.blocks.length), b.blocks[i] = k :=
      List.get_of_mem hk
    let j : Fin b.length := ⟨i.val, b.blocks_length ▸ i.prop⟩
    have A : b.blocksFun j ≠ 1 := by
      have : b.blocksFun j = k := hi
      omega
    ext v
    rw [compAlong_apply, MultilinearMap.zero_apply]
    apply MultilinearMap.map_coord_zero _ j
    dsimp [applyComp]
    rw [id_of_ne_one A, MultilinearMap.zero_apply]
  · simp

/-- **The identity is a left unit**, on series vanishing in arity zero. -/
theorem id_comp (p : MSer R V W) (h : p 0 = 0) : comp (id R W) p = p := by
  funext n
  obtain rfl | n_pos := n.eq_zero_or_pos
  · ext v
    rw [comp_apply, h, MultilinearMap.zero_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    have : c.length = 0 := Nat.le_zero.mp c.length_le
    rw [id_of_ne_one (by omega), MultilinearMap.zero_apply]
  · rw [comp, Finset.sum_eq_single (Composition.single n n_pos)]
    · ext v
      rw [compAlong_apply, id_apply_one' (Composition.single_length n_pos)]
      dsimp [applyComp]
      refine p.congr rfl fun i him hin => congr_arg v (Fin.ext ?_)
      simp
    · intro b _ hb
      have A : b.length ≠ 1 := by simpa [Composition.eq_single_iff_length] using hb
      ext v
      rw [compAlong_apply, id_of_ne_one A, MultilinearMap.zero_apply,
        MultilinearMap.zero_apply]
    · simp

/-! ## The extension by an odd parameter -/

section Hat

/-- Inputs of earlier blocks of a composition come before those of later blocks. -/
lemma embedding_lt_embedding {n : ℕ} (c : Composition n) {i r : Fin c.length} (h : i < r)
    (j : Fin (c.blocksFun i)) (s : Fin (c.blocksFun r)) : c.embedding i j < c.embedding r s := by
  rw [Fin.lt_def, Composition.coe_embedding, Composition.coe_embedding]
  have h1 := c.sizeUpTo_succ' i
  have h2 : c.sizeUpTo ((i : ℕ) + 1) ≤ c.sizeUpTo r := c.monotone_sizeUpTo (Nat.succ_le_of_lt h)
  have := j.isLt
  omega

variable (εV : V →ₗ[R] V)

/-- The inputs of the `θ`-term at `s`: `ε ∘ fst` before `s`, `snd` at `s`, `fst` after. -/
def hatFn {n : ℕ} (s t : Fin n) : V × V →ₗ[R] V :=
  if t < s then εV ∘ₗ LinearMap.fst R V V
  else if t = s then LinearMap.snd R V V else LinearMap.fst R V V

/-- **The extension of a series by an odd parameter** `θ`:
`f̂((x₁, y₁), …) = (f(x), ∑ₛ f(εx₁, …, εx_{s-1}, y_s, x_{s+1}, …))`. -/
def hat (f : MSer R V W) : MSer R (V × V) (W × W) := fun n =>
  MultilinearMap.prod ((f n).compLinearMap fun _ => LinearMap.fst R V V)
    (∑ s : Fin n, (f n).compLinearMap (hatFn εV s))

lemma hatFn_of_lt {n : ℕ} {s t : Fin n} (h : t < s) :
    hatFn εV s t = εV ∘ₗ LinearMap.fst R V V := if_pos h

lemma hatFn_self {n : ℕ} (s : Fin n) : hatFn εV s s = LinearMap.snd R V V := by
  rw [hatFn, if_neg (lt_irrefl s), if_pos rfl]

lemma hatFn_of_gt {n : ℕ} {s t : Fin n} (h : s < t) : hatFn εV s t = LinearMap.fst R V V := by
  rw [hatFn, if_neg (not_lt.mpr h.le), if_neg (ne_of_gt h)]

lemma hat_apply (f : MSer R V W) (n : ℕ) (v : Fin n → V × V) :
    hat εV f n v = (f n fun t => (v t).1, ∑ s : Fin n, f n fun t => hatFn εV s t (v t)) := by
  simp [hat, MultilinearMap.sum_apply]

variable (εW : W →ₗ[R] W)

/-- **An even series** commutes with the parity involutions. -/
def IsEven (f : MSer R V W) : Prop :=
  ∀ n (v : Fin n → V), f n (fun t => εV (v t)) = εW (f n v)

variable {εV εW}

/-- **Extension by an odd parameter is functorial on even series.** -/
theorem hat_comp {f : MSer R V W} (hf : IsEven εV εW f) (g : MSer R W X) :
    hat εV (comp g f) = comp (hat εW g) (hat εV f) := by
  funext n
  ext v
  · simp only [hat_apply, comp_apply, applyComp, Prod.fst_sum]
    rfl
  · rw [comp_apply (hat εW g) (hat εV f), Prod.snd_sum, hat_apply]
    dsimp only
    simp only [comp_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hat_apply, ← c.blocksFinEquiv.sum_comp, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun r _ => ?_
    have key : (fun i => hatFn εW r i (applyComp (hat εV f) c v i)) =
        Function.update (fun i => if i < r
            then εW (f (c.blocksFun i) fun j => (v (c.embedding i j)).1)
            else f (c.blocksFun i) fun j => (v (c.embedding i j)).1) r
          (∑ s' : Fin (c.blocksFun r),
            f (c.blocksFun r) fun j => hatFn εV s' j (v (c.embedding r j))) := by
      funext i
      simp only [applyComp, hat_apply]
      rcases lt_trichotomy i r with h | rfl | h
      · rw [Function.update_of_ne (ne_of_lt h), if_pos h, hatFn_of_lt εW h]
        rfl
      · rw [Function.update_self, hatFn_self εW]
        rfl
      · rw [Function.update_of_ne (ne_of_gt h), if_neg (not_lt.mpr h.le), hatFn_of_gt εW h]
        rfl
    rw [key, MultilinearMap.map_update_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [show c.blocksFinEquiv ⟨r, s'⟩ = c.embedding r s' from rfl]
    congr 1
    funext i
    simp only [applyComp]
    rcases lt_trichotomy i r with h | rfl | h
    · rw [Function.update_of_ne (ne_of_lt h), if_pos h, ← hf]
      congr 1
      funext j
      rw [Function.comp_apply, hatFn_of_lt εV (embedding_lt_embedding c h j s')]
      rfl
    · rw [Function.update_self]
      congr 1
      funext j
      rw [Function.comp_apply]
      rcases lt_trichotomy j s' with h | rfl | h
      · rw [hatFn_of_lt εV h, hatFn_of_lt εV ((c.embedding i).strictMono h)]
      · rw [hatFn_self εV, hatFn_self εV]
      · rw [hatFn_of_gt εV h, hatFn_of_gt εV ((c.embedding i).strictMono h)]
    · rw [Function.update_of_ne (ne_of_gt h), if_neg (not_lt.mpr h.le)]
      congr 1
      funext j
      rw [Function.comp_apply, hatFn_of_gt εV (embedding_lt_embedding c h s' j)]
      rfl

variable (εV) in
/-- **The extension of the identity is the identity.** -/
@[simp] theorem hat_id : hat εV (id R V) = id R (V × V) := by
  funext n
  by_cases hn : n = 1
  · subst hn
    ext v
    · simp [hat_apply]
    · simp [hat_apply, hatFn_self]
  · have h1 : hat εV (id R V) n = 0 := by
      ext v
      · simp [hat_apply, id_of_ne_one (V := V) hn]
      · simp [hat_apply, id_of_ne_one (V := V) hn]
    rw [h1, id_of_ne_one hn]

variable (εV) in
lemma id_even : IsEven εV εV (id R V) := fun n v => by
  by_cases hn : n = 1
  · subst hn
    rfl
  · simp [id_of_ne_one hn]

/-- **A composite of even series is even.** -/
lemma comp_even {εX : X →ₗ[R] X} {f : MSer R V W} {g : MSer R W X} (hf : IsEven εV εW f)
    (hg : IsEven εW εX g) : IsEven εV εX (comp g f) := fun n v => by
  rw [comp_apply, comp_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← hg]
  congr 1
  funext i
  exact hf _ _

end Hat

/-! ## Low arities -/

lemma composition_one (c : Composition 1) : c = Composition.ones 1 :=
  Composition.eq_ones_iff_le_length.2 ((Composition.length_pos_iff c).2 one_pos)

lemma composition_two (c : Composition 2) :
    c = Composition.ones 2 ∨ c = Composition.single 2 two_pos := by
  have h1 := c.length_le
  have h2 := (Composition.length_pos_iff c).2 (two_pos : 0 < 2)
  rcases (show c.length = 1 ∨ c.length = 2 by omega) with h | h
  · exact Or.inr ((Composition.eq_single_iff_length two_pos).2 h)
  · exact Or.inl (Composition.eq_ones_iff_length.2 h)

/-- **A composite in arity one.** -/
lemma comp_apply_one (q : MSer R W X) (p : MSer R V W) (v : Fin 1 → V) :
    comp q p 1 v = q 1 ![p 1 v] := by
  rw [comp_apply, Fintype.sum_eq_single (Composition.ones 1)
    (fun c hc => absurd (composition_one c) hc)]
  apply q.congr (Composition.ones_length 1)
  intro i hi1 hi2
  obtain rfl : i = 0 := by omega
  rw [applyComp_ones]
  show p 1 _ = p 1 _
  congr 1
  funext t
  fin_cases t
  exact congr_arg v (Fin.ext rfl)

/-- **A composite in arity two**: `q₂(p₁, p₁) + q₁(p₂)`. -/
lemma comp_apply_two (q : MSer R W X) (p : MSer R V W) (v : Fin 2 → V) :
    comp q p 2 v = q 2 ![p 1 ![v 0], p 1 ![v 1]] + q 1 ![p 2 v] := by
  have hne : Composition.ones 2 ≠ Composition.single 2 two_pos := fun h => by
    have := congrArg Composition.length h
    simp at this
  rw [comp_apply, Fintype.sum_eq_add (Composition.ones 2) (Composition.single 2 two_pos) hne
    (fun c ⟨h1, h2⟩ => by rcases composition_two c with h | h <;> contradiction)]
  congr 1
  · apply q.congr (Composition.ones_length 2)
    intro i hi1 hi2
    rw [applyComp_ones]
    show p 1 _ = _
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · show p 1 _ = p 1 _
      congr 1
      funext t
      fin_cases t
      exact congr_arg v (Fin.ext (by simp))
    · show p 1 _ = p 1 _
      congr 1
      funext t
      fin_cases t
      exact congr_arg v (Fin.ext (by simp))
  · apply q.congr (Composition.single_length two_pos)
    intro i hi1 hi2
    obtain rfl : i = 0 := by omega
    show p _ _ = p 2 v
    apply p.congr (Composition.single_blocksFun two_pos _)
    intro j hj1 hj2
    exact congr_arg v (Fin.ext (by rw [Composition.coe_embedding]; simp))

lemma hat_apply_one_snd (εV : V →ₗ[R] V) (f : MSer R V W) (w : Fin 1 → V × V) :
    (hat εV f 1 w).2 = f 1 ![(w 0).2] := by
  rw [hat_apply, Fin.sum_univ_one]
  dsimp only
  congr 1
  funext t
  fin_cases t
  simp [hatFn_self]

lemma hat_apply_two_snd (εV : V →ₗ[R] V) (f : MSer R V W) (w : Fin 2 → V × V) :
    (hat εV f 2 w).2 = f 2 ![(w 0).2, (w 1).1] + f 2 ![εV (w 0).1, (w 1).2] := by
  rw [hat_apply, Fin.sum_univ_two]
  dsimp only
  congr 1
  · congr 1
    funext t
    fin_cases t
    · simp [hatFn_self]
    · simp [hatFn_of_gt εV (show (0 : Fin 2) < 1 by decide)]
  · congr 1
    funext t
    fin_cases t
    · simp [hatFn_of_lt εV (show (0 : Fin 2) < 1 by decide)]
    · simp [hatFn_self]

/-! ## Linear maps as series -/

/-- **A linear map as a series**, concentrated in arity one. -/
def lin (φ : V →ₗ[R] W) : MSer R V W
  | 1 => MultilinearMap.ofSubsingleton R V W 0 φ
  | _ => 0

@[simp] lemma lin_apply_one (φ : V →ₗ[R] W) (v : Fin 1 → V) : lin φ 1 v = φ (v 0) :=
  rfl

lemma lin_apply_one' (φ : V →ₗ[R] W) {n : ℕ} (h : n = 1) (v : Fin n → V) :
    lin φ n v = φ (v ⟨0, h.symm ▸ zero_lt_one⟩) := by
  subst h
  rfl

lemma lin_of_ne_one (φ : V →ₗ[R] W) {n : ℕ} (h : n ≠ 1) : lin φ n = 0 := by
  match n, h with
  | 0, _ => rfl
  | n + 2, _ => rfl

/-- **Composing with a linear map on the right** applies it to every input. -/
theorem comp_lin_right (p : MSer R W X) (φ : V →ₗ[R] W) :
    comp p (lin φ) = fun n => (p n).compLinearMap fun _ => φ := by
  funext n
  rw [comp, Finset.sum_eq_single (Composition.ones n)]
  · ext v
    rw [compAlong_apply, MultilinearMap.compLinearMap_apply]
    apply p.congr (Composition.ones_length n)
    intros
    rw [applyComp_ones]
    refine congr_arg φ (congr_arg v ?_)
    rw [Fin.ext_iff, Fin.val_castLE, Fin.val_mk]
  · intro b _ hb
    obtain ⟨k, hk, lt_k⟩ : ∃ (k : ℕ), k ∈ Composition.blocks b ∧ 1 < k :=
      Composition.ne_ones_iff.1 hb
    obtain ⟨i, hi⟩ : ∃ (i : Fin b.blocks.length), b.blocks[i] = k :=
      List.get_of_mem hk
    let j : Fin b.length := ⟨i.val, b.blocks_length ▸ i.prop⟩
    have A : b.blocksFun j ≠ 1 := by
      have : b.blocksFun j = k := hi
      omega
    ext v
    rw [compAlong_apply, MultilinearMap.zero_apply]
    apply MultilinearMap.map_coord_zero _ j
    dsimp [applyComp]
    rw [lin_of_ne_one φ A, MultilinearMap.zero_apply]
  · simp

/-- **Composing with a linear map on the left** applies it to the value, on series vanishing in
arity zero. -/
theorem comp_lin_left (ψ : W →ₗ[R] X) (p : MSer R V W) (h : p 0 = 0) :
    comp (lin ψ) p = fun n => ψ.compMultilinearMap (p n) := by
  funext n
  obtain rfl | n_pos := n.eq_zero_or_pos
  · ext v
    rw [comp_apply, LinearMap.compMultilinearMap_apply, h, MultilinearMap.zero_apply, map_zero]
    refine Finset.sum_eq_zero fun c _ => ?_
    have : c.length = 0 := Nat.le_zero.mp c.length_le
    rw [lin_of_ne_one ψ (by omega), MultilinearMap.zero_apply]
  · rw [comp, Finset.sum_eq_single (Composition.single n n_pos)]
    · ext v
      rw [compAlong_apply, lin_apply_one' ψ (Composition.single_length n_pos),
        LinearMap.compMultilinearMap_apply]
      dsimp [applyComp]
      refine congr_arg ψ (p.congr rfl fun i him hin => congr_arg v (Fin.ext ?_))
      simp
    · intro b _ hb
      have A : b.length ≠ 1 := by simpa [Composition.eq_single_iff_length] using hb
      ext v
      rw [compAlong_apply, lin_of_ne_one ψ A, MultilinearMap.zero_apply,
        MultilinearMap.zero_apply]
    · simp

/-- **The extension of a linear map** is the linear map on both components. -/
theorem hat_lin (εV : V →ₗ[R] V) (φ : V →ₗ[R] W) : hat εV (lin φ) = lin (φ.prodMap φ) := by
  funext n
  by_cases hn : n = 1
  · subst hn
    ext v
    · simp [hat_apply]
    · simp [hat_apply, hatFn_self]
  · have h1 : hat εV (lin φ) n = 0 := by
      ext v
      · simp [hat_apply, lin_of_ne_one φ hn]
      · simp [hat_apply, lin_of_ne_one φ hn]
    rw [h1, lin_of_ne_one _ hn]

end MSer

/-! ## ∞-morphisms -/

namespace AInf

open MSer

variable {R} {V W X : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [AddCommGroup X] [Module R X]

/-- **The codifferential of a family `b` as a series** `V ⇝ V × V`: `1 + θ b`, that is
`x ↦ (x, b₀ x)` in arity one and `x ↦ (0, bₙ x)` in arity `n + 1 ≥ 2`. -/
def bser (b : Fam R V) : MSer R V (V × V)
  | 0 => 0
  | n + 1 => MultilinearMap.prod (MSer.id R V (n + 1)) (b n)

@[simp] lemma bser_zero (b : Fam R V) : bser b 0 = 0 :=
  rfl

lemma bser_succ_apply (b : Fam R V) (n : ℕ) (v : Fin (n + 1) → V) :
    bser b (n + 1) v = (MSer.id R V (n + 1) v, b n v) :=
  rfl

/-- **An ∞-morphism of A∞-algebras** `(V, b) ⇝ (W, b')`, in the bar convention: an even series
`f` whose extension intertwines the codifferentials, `f̂ ∘ β_b = β_{b'} ∘ f`. -/
structure IsInfMorph (εV : V →ₗ[R] V) (εW : W →ₗ[R] W) (b : Fam R V) (b' : Fam R W)
    (f : MSer R V W) : Prop where
  /-- The components are even. -/
  even : IsEven εV εW f
  /-- The extension intertwines the codifferentials. -/
  eq : comp (hat εV f) (bser b) = comp (bser b') f

namespace IsInfMorph

variable {εV : V →ₗ[R] V} {εW : W →ₗ[R] W} {εX : X →ₗ[R] X}

variable (εV) in
/-- **The identity is an ∞-morphism.** -/
theorem id (b : Fam R V) : IsInfMorph εV εV b b (MSer.id R V) where
  even := id_even εV
  eq := by rw [hat_id, id_comp _ (bser_zero b), comp_id]

/-- **∞-morphisms compose**: `(g ∘ f)^ ∘ β_b = ĝ ∘ f̂ ∘ β_b = ĝ ∘ β_{b'} ∘ f = β_{b''} ∘ g ∘ f`. -/
theorem comp {b : Fam R V} {b' : Fam R W} {b'' : Fam R X} {f : MSer R V W} {g : MSer R W X}
    (hf : IsInfMorph εV εW b b' f) (hg : IsInfMorph εW εX b' b'' g) :
    IsInfMorph εV εX b b'' (MSer.comp g f) where
  even := comp_even hf.even hg.even
  eq := by
    rw [hat_comp hf.even, comp_assoc, hf.eq, ← comp_assoc, hg.eq, comp_assoc]

/-- **In arity one, `f₁` is a chain map**: `f₁ (b₀ x) = b'₀ (f₁ x)`. -/
theorem chain {b : Fam R V} {b' : Fam R W} {f : MSer R V W} (hf : IsInfMorph εV εW b b' f)
    (x : V) : f 1 ![b 0 ![x]] = b' 0 ![f 1 ![x]] := by
  have h := congrArg (fun F : MSer R V (W × W) => (F 1 ![x]).2) hf.eq
  simp only [comp_apply_one, hat_apply_one_snd, Matrix.cons_val_zero, bser_succ_apply] at h
  exact h

/-- **In arity two, `f₁` is multiplicative up to the homotopy `f₂`**:
`f₁ (b₁(x, y)) + f₂(b₀ x, y) + f₂(ε x, b₀ y) = b'₁(f₁ x, f₁ y) + b'₀ (f₂(x, y))`. -/
theorem mul {b : Fam R V} {b' : Fam R W} {f : MSer R V W} (hf : IsInfMorph εV εW b b' f)
    (x y : V) :
    f 1 ![b 1 ![x, y]] + f 2 ![b 0 ![x], y] + f 2 ![εV x, b 0 ![y]] =
      b' 1 ![f 1 ![x], f 1 ![y]] + b' 0 ![f 2 ![x, y]] := by
  have h := congrArg (fun F : MSer R V (W × W) => (F 2 ![x, y]).2) hf.eq
  simp only [comp_apply_two, Prod.snd_add, hat_apply_one_snd, hat_apply_two_snd,
    Matrix.cons_val_zero, Matrix.cons_val_one, bser_succ_apply] at h
  rw [← h]
  abel

end IsInfMorph

/-- **Strict morphisms are ∞-morphisms**: a linear map, as a series concentrated in arity one, is
an ∞-morphism exactly when it is even and commutes with all the operations,
`φ (bₙ(x₀, …, xₙ)) = b'ₙ(φ x₀, …, φ xₙ)`. -/
theorem isInfMorph_lin_iff {εV : V →ₗ[R] V} {εW : W →ₗ[R] W} {b : Fam R V} {b' : Fam R W}
    (φ : V →ₗ[R] W) :
    IsInfMorph εV εW b b' (lin φ) ↔ (∀ x, φ (εV x) = εW (φ x)) ∧
      ∀ n (v : Fin (n + 1) → V), φ (b n v) = b' n fun t => φ (v t) := by
  rw [show (IsInfMorph εV εW b b' (lin φ)) ↔ (IsEven εV εW (lin φ) ∧
      comp (hat εV (lin φ)) (bser b) = comp (bser b') (lin φ)) from
    ⟨fun h => ⟨h.even, h.eq⟩, fun h => ⟨h.1, h.2⟩⟩, hat_lin, comp_lin_left _ _ (bser_zero b),
    comp_lin_right]
  refine and_congr ⟨fun h x => h 1 ![x], fun h n v => ?_⟩ ⟨fun h n v => ?_, fun h => ?_⟩
  · by_cases hn : n = 1
    · subst hn
      exact h (v 0)
    · simp [lin_of_ne_one φ hn]
  · have := congrArg (fun F : MultilinearMap R (fun _ : Fin (n + 1) => V) (W × W) => (F v).2)
      (congrFun h (n + 1))
    simpa [bser_succ_apply] using this
  · funext n
    ext v
    · cases n with
      | zero => simp
      | succ n =>
        simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
          bser_succ_apply, LinearMap.prodMap_apply]
        by_cases hn : n + 1 = 1
        · rw [MSer.id_apply_one' hn, MSer.id_apply_one' hn]
        · simp [MSer.id_of_ne_one hn]
    · cases n with
      | zero => simp
      | succ n =>
        simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
          bser_succ_apply, LinearMap.prodMap_apply]
        exact h n v

end AInf

end Operad
