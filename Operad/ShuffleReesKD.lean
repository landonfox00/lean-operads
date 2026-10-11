/-
# The Rees family of a Koszul dual cooperad

Let `w` weigh the generators of a shuffle operad. **Rescaling the generators by `c^{-w}`**
(`c ≠ 0`) multiplies a monomial by `c^{-wdeg}` (`LTree.wt_pow`), and the Koszul dual cooperad of
the rescaled relators, on the monomials, is that of `R` rescaled the same way
(`ShuffleBar.KDmono_rescale`, `ShuffleBar.KDmono_rescale_pow`). So for relators `R` whose
leading forms `R₀` satisfy `KD(R₀) = gr KD(R)` (`ShuffleBar.KDmono_eq_grF`), the Rees module of
the Koszul dual cooperad of `R` on the monomials (`Graded.rees`), a free `K[X]`-module, is the
family of the Koszul dual cooperads of the relators `R_c`, where `R_0 = R₀` and `R_c` is `R`
rescaled by `c^{-w}` for `c ≠ 0`:

* **its fiber at `c ≠ 0` is the Koszul dual cooperad of `R_c`, at `c = 0` that of `R₀`**
  (`ShuffleBar.fiber_rees_KDmono_of_ne_zero`, `ShuffleBar.fiber_rees_KDmono_zero`), and its rank
  is their common dimension (`ShuffleBar.finrank_rees_KDmono`);
* over an infinite field **it is the module of polynomial sections of the family**
  (`ShuffleBar.sections_KDmono_eq_rees`).
-/
import Operad.ReesModule

universe u v

namespace Operad

open Polynomial Module

namespace LTree

variable {E : Type v} {K : Type u} [CommRing K]

/-- **The weight of a tree for the scalars `a^w` is `a^wdeg`.** -/
lemma wt_pow (w : E → ℕ) (a : K) : ∀ t : LTree E, wt (fun e => a ^ w e) t = a ^ wdeg w t
  | leaf _ => by simp
  | node e l r => by
    rw [wt_node, wdeg_node, wt_pow w a l, wt_pow w a r, pow_add, pow_add]

end LTree

namespace ShuffleBar

open LTree Graded

variable {E : Type v} [Fintype E] [DecidableEq E] {K : Type u} [Field K]

omit [Fintype E] [DecidableEq E] in
lemma scaleBar_apply (l : E → K) (v : BarTree E →₀ K) (x : BarTree E) :
    scaleBar K l v x = wtB l x * v x := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v v' hv hv' => rw [map_add, Finsupp.add_apply, hv, hv', Finsupp.add_apply, mul_add]
  | single y c =>
    rw [scaleBar_single, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply,
      Finsupp.single_apply]
    split_ifs with h
    · subst h
      ring
    · simp

omit [Fintype E] [DecidableEq E] in
lemma wtB_fullBar (l : E → K) (m : LTree E) : wtB l (fullBar m) = wt l m := by
  rw [wtB_eq, full_fullBar]

variable (K) in
/-- **The rescaling of the functions on the monomials**: the value at a monomial times its
weight. -/
noncomputable def scaleMono (l : E → K) (n : ℕ) : (Mono E n → K) →ₗ[K] (Mono E n → K) where
  toFun x m := wt l m.1 * x m
  map_add' x y := by
    funext m
    simp [mul_add]
  map_smul' c x := by
    funext m
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

lemma toMono_scaleBar (l : E → K) (n : ℕ) (v : BarTree E →₀ K) :
    toMono K n (scaleBar K l v) = scaleMono K l n (toMono K n v) := by
  funext m
  show (tauS m.1 : K) * scaleBar K l v (fullBar m.1) =
    wt l m.1 * ((tauS m.1 : K) * v (fullBar m.1))
  rw [scaleBar_apply, wtB_fullBar]
  ring

/-- **The Koszul dual cooperad of the rescaled relators, on the monomials, is the rescaled Koszul
dual cooperad**, for nonzero scalars. -/
theorem KDmono_rescale (l : E → K) (hl : ∀ e, l e ≠ 0) (R : Submodule K (Mono E 3 → K)) {n : ℕ}
    (hn : 2 ≤ n) : KDmono K (R.map (rescale K l)) n = (KDmono K R n).map (scaleMono K l n) := by
  rw [KDmono_eq_map _ hn, KDmono_eq_map R hn, ← map_scaleBar_KD K l hl R n,
    ← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  exact LinearMap.ext fun v => toMono_scaleBar l n v

lemma scaleMono_pow (w : E → ℕ) (n : ℕ) (c : K) :
    scaleMono K (fun e => c⁻¹ ^ w e) n = scaleInv (wMono w n) c := by
  refine LinearMap.ext fun x => funext fun m => ?_
  show wt (fun e => c⁻¹ ^ w e) m.1 * x m = c⁻¹ ^ wdeg w m.1 * x m
  rw [wt_pow]

/-- **The Koszul dual cooperad of the relators rescaled by `c^{-w}`** is that of `R` rescaled by
`c^{-wdeg}`, on the monomials. -/
theorem KDmono_rescale_pow (w : E → ℕ) {c : K} (hc : c ≠ 0) (R : Submodule K (Mono E 3 → K))
    {n : ℕ} (hn : 2 ≤ n) :
    KDmono K (R.map (rescale K fun e => c⁻¹ ^ w e)) n =
      (KDmono K R n).map (scaleInv (wMono w n) c) := by
  rw [KDmono_rescale _ (fun e => pow_ne_zero _ (inv_ne_zero hc)) R hn, scaleMono_pow]

/-! ## The Rees family -/

variable (w : E → ℕ) {R R₀ : Submodule K (Mono E 3 → K)} {n : ℕ}

/-- **The fiber at `c ≠ 0` of the Rees module of the Koszul dual cooperad of `R` is the Koszul
dual cooperad of `R` rescaled by `c^{-w}`.** -/
theorem fiber_rees_KDmono_of_ne_zero (hn : 2 ≤ n) {c : K} (hc : c ≠ 0) :
    fiber (W := wMono w n) (KDmono K R n) c =
      KDmono K (R.map (rescale K fun e => c⁻¹ ^ w e)) n := by
  rw [evalAt_rees_of_ne_zero _ hc, KDmono_rescale_pow w hc R hn]

/-- **Its fiber at `0` is the Koszul dual cooperad of the leading forms `R₀`**, when that is the
associated graded. -/
theorem fiber_rees_KDmono_zero (hn : 2 ≤ n) (h : KD K R₀ n = grW K (wdegB w) (KD K R n)) :
    fiber (W := wMono w n) (KDmono K R n) 0 = KDmono K R₀ n := by
  rw [evalAt_rees_zero, KDmono_eq_grF w hn h]

/-- **The rank of the Rees module of the Koszul dual cooperad** is its dimension. -/
theorem finrank_rees_KDmono (hn : 2 ≤ n) :
    Module.finrank K[X] (rees K (wMono w n) (KDmono K R n)) = Module.finrank K (KD K R n) := by
  rw [finrank_rees _ 1, evalAt_rees_one, (kdEquivKDmono R hn).finrank_eq]

/-- **The Rees module of the Koszul dual cooperad of `R` is the module of polynomial sections of
the family of Koszul dual cooperads of the relators `R_c`**, equal to `R₀` at `c = 0` and to `R`
rescaled by `c^{-w}` at `c ≠ 0`, over an infinite field. -/
theorem sections_KDmono_eq_rees [Infinite K] (hn : 2 ≤ n)
    (h : KD K R₀ n = grW K (wdegB w) (KD K R n)) (Rc : K → Submodule K (Mono E 3 → K))
    (h0 : Rc 0 = R₀) (hc : ∀ c, c ≠ 0 → Rc c = R.map (rescale K fun e => c⁻¹ ^ w e)) :
    sections K (fun c => KDmono K (Rc c) n) = rees K (wMono w n) (KDmono K R n) := by
  rw [← sections_fiber]
  congr 1
  funext c
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [h0, fiber_rees_KDmono_zero w hn h]
  · rw [hc c hc0, fiber_rees_KDmono_of_ne_zero w hn hc0]

end ShuffleBar

end Operad
