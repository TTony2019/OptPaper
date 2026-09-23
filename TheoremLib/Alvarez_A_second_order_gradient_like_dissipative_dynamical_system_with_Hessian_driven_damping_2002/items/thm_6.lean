import Mathlib
import Foundation.Optimization.Argmin
import Foundation.Hilbert.WeakConvergence
import Foundation.Hilbert.WeakTopology
import Foundation.Convex.ArgminExistence
import Foundation.FixedPoint.Nonexpansive
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.ext_lem_2
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.thm_5
namespace Alvarez2002
open Filter
set_option maxHeartbeats 1000000

private theorem gdin_grad_lipschitzOnBounded_thm6
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (gradΦ : H → H)
    (hloclip : ∀ R : ℝ, ∃ L : ℝ, ∀ x y, ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖gradΦ x - gradΦ y‖ ≤ L * ‖x - y‖) :
    LipschitzOnBoundedSets gradΦ := by
  intro s hs
  rcases isBounded_iff_forall_norm_le.1 hs with ⟨R, hR⟩
  let R' : ℝ := max R 0
  rcases hloclip R' with ⟨L, hL⟩
  let K : NNReal := ⟨max L 0, le_max_right L 0⟩
  refine ⟨K, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  have hxR : ‖x‖ ≤ R' := (hR x hx).trans (le_max_left _ _)
  have hyR : ‖y‖ ≤ R' := (hR y hy).trans (le_max_left _ _)
  have hxy := hL x y hxR hyR
  simpa only [dist_eq_norm, NNReal.coe_mk] using
    hxy.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

private theorem gdin_distance_limit {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Φ : H → ℝ) (β a b : ℝ)
    (x y : ℝ → H) (hbounded : ∃ m : ℝ, ∀ x, m ≤ Φ x) (x₀ y₀ : H)
    (hΦ : ContDiff ℝ 1 Φ)
    (hloclip : ∀ R : ℝ, ∃ L : ℝ, ∀ x y, ‖x‖ ≤ R →
      ‖y‖ ≤ R → ‖gradient Φ x - gradient Φ y‖ ≤ L * ‖x - y‖)
    (hβ : 0 < β) (hb : 0 < b) (hab : 0 < b + a)
    (hconvex : ConvexOn ℝ Set.univ Φ)
    (hxy : ContDiffOn ℝ 1 x (Set.Ici 0) ∧ ContDiffOn ℝ 2 y (Set.Ici 0))
    (hsol : IsSolution_gDIN Φ β a b x₀ y₀ x y)
    {z : H} (hz : z ∈ Optimization.argminSet Φ) :
    ∃ d : ℝ, Tendsto (fun t => ‖x t - z‖) atTop (nhds d) := by
  have hab' : 0 < a + b := by linarith
  have hgrad_lip : LipschitzOnBoundedSets (gradient Φ) :=
    gdin_grad_lipschitzOnBounded_thm6 (gradient Φ) hloclip
  have hgradF : ∀ w : H, HasFDerivAt Φ (innerSL ℝ (gradient Φ w)) w := by
    intro w
    simpa [innerSL] using ((hΦ.differentiable (by norm_num) w).hasGradientAt.hasFDerivAt)
  have hphi_x : ∃ l : ℝ, Tendsto (fun t => Φ (x t)) atTop (nhds l) :=
    gdin_phi_limit Φ β a b hΦ hbounded hβ hb hab' x₀ y₀ x y hxy hsol
  have hres_x : Tendsto (fun t => deriv x t + β • gradient Φ (x t)) atTop (nhds 0) :=
    gdin_residual_limit Φ β a b hΦ hbounded hβ hb hab' x₀ y₀ x y hxy hsol
  let v : ℝ → H := deriv x
  let g : ℝ → H := fun t => gradient Φ (x t)
  let r : ℝ → H := fun t => -a • x t - b • y t
  let u : ℝ → H := fun t => x t - z
  let c : ℝ := a + b
  let κ : ℝ := β * (a + 2 * b)
  have hc : 0 < c := by dsimp [c]; linarith
  have hκ : 0 < κ := by
    dsimp [κ]
    have : 0 < a + 2 * b := by linarith
    exact mul_pos hβ this
  have hvr : ∀ t, 0 ≤ t → v t + β • g t = r t := by
    intro t ht
    dsimp [v, g, r]
    rw [show -a • x t - b • y t = -(a • x t + b • y t) by module]
    exact eq_neg_iff_add_eq_zero.mpr (by simpa [add_assoc] using hsol.1 t ht)
  have hyr : ∀ t, 0 ≤ t → deriv y t = r t := by
    intro t ht
    dsimp [r]
    rw [show -a • x t - b • y t = -(a • x t + b • y t) by module]
    exact eq_neg_iff_add_eq_zero.mpr (by simpa [add_assoc] using hsol.2.1 t ht)
  have hx_cont : ContinuousOn x (Set.Ici (0 : ℝ)) := hxy.1.continuousOn
  have hy_cont : ContinuousOn y (Set.Ici (0 : ℝ)) := hxy.2.continuousOn
  have hr_cont : ContinuousOn r (Set.Ici (0 : ℝ)) := by
    simpa [r] using (hx_cont.const_smul (-a)).sub (hy_cont.const_smul b)
  have hphi_cont : ContinuousOn (fun t => Φ (x t)) (Set.Ici (0 : ℝ)) := by
    exact hΦ.continuous.continuousOn.comp hx_cont (fun _ _ => Set.mem_univ _)
  have hr_at (t : ℝ) (ht : 0 < t) : HasDerivAt r (-a • v t - b • r t) t := by
    have hxAt : HasDerivAt x (v t) t := by
      have h := hxy.1.differentiableOn (by norm_num) t ht.le
      exact (h.differentiableAt (Ici_mem_nhds ht)).hasDerivAt
    have hyAt : HasDerivAt y (deriv y t) t := by
      have h := hxy.2.differentiableOn (by norm_num) t ht.le
      exact (h.differentiableAt (Ici_mem_nhds ht)).hasDerivAt
    have hraw : HasDerivAt r ((-a) • v t - b • deriv y t) t := by
      simpa [r, v] using (hxAt.const_smul (-a)).sub (hyAt.const_smul b)
    convert hraw using 1
    rw [hyr t ht.le]
  have hr_lim : Tendsto r atTop (nhds 0) := by
    apply hres_x.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hvr t ht]
  let E : ℝ → ℝ := fun t => κ * Φ (x t) + (1 / 2) * ‖r t‖ ^ 2
  have hE_cont : ContinuousOn E (Set.Ici (0 : ℝ)) := by
    simpa [E] using (hphi_cont.const_smul κ).add ((hr_cont.norm.pow 2).const_mul (1 / 2 : ℝ))
  have hE_lim : ∃ l : ℝ, Tendsto E atTop (nhds l) := by
    rcases hphi_x with ⟨l, hl⟩
    have hpot : Tendsto (fun t => κ * Φ (x t)) atTop (nhds (κ * l)) :=
      tendsto_const_nhds.mul hl
    have hkin : Tendsto (fun t => (1 / 2 : ℝ) * ‖r t‖ ^ 2) atTop (nhds 0) := by
      have := hr_lim.norm.pow 2
      simpa using (tendsto_const_nhds.mul this)
    refine ⟨κ * l, ?_⟩
    simpa [E] using hpot.add hkin
  have hgrad_inner : ∀ t : ℝ, 0 ≤ inner ℝ (g t) (u t) := by
    intro t
    have hgradΦ : ∀ w : H, HasGradientAt Φ (gradient Φ w) w := fun w =>
      (hΦ.differentiable (by norm_num) w).hasGradientAt
    have hs := convex_supporting_baillon_haddad Φ (gradient Φ) hconvex hgradΦ (x t) z
    have hzle : Φ z ≤ Φ (x t) := hz (x t)
    have hs' : Φ (x t) + inner ℝ (g t) (z - x t) ≤ Φ z := by
      simpa [g] using hs
    rw [show z - x t = -(x t - z) by module, inner_neg_right] at hs'
    dsimp [u]
    linarith
  let ε : ℝ := min (c / 2) b
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (by positivity) hb
  have hεc : ε ≤ c / 2 := min_le_left _ _
  have hεb : ε ≤ b := min_le_right _ _
  have hE_at (t : ℝ) (ht : 0 < t) : HasDerivAt E
      (-c * ‖v t‖ ^ 2 - b * β ^ 2 * ‖g t‖ ^ 2) t := by
    have hxAt : HasDerivAt x (v t) t := by
      have h := hxy.1.differentiableOn (by norm_num) t ht.le
      exact (h.differentiableAt (Ici_mem_nhds ht)).hasDerivAt
    have hp := (hgradF (x t)).comp_hasDerivAt t hxAt
    have hp' : HasDerivAt (fun s => Φ (x s)) (inner ℝ (g t) (v t)) t := by
      simpa [g, v, Function.comp_def] using hp
    have hk := (hr_at t ht).norm_sq.const_mul (1 / 2 : ℝ)
    have he := (hp'.const_smul κ).add hk
    convert he using 1
    rw [← hvr t ht.le]
    dsimp [E, κ, c]
    simp only [smul_add, inner_add_left, inner_add_right, inner_sub_right, inner_smul_left,
      inner_smul_right, real_inner_self_eq_norm_sq]
    simp [real_inner_comm]
    ring_nf
  let haux : ℝ → ℝ := fun t => E t + ε *
    (c / 2 * ‖u t‖ ^ 2 + inner ℝ (r t) (u t))
  have hu_at (t : ℝ) (ht : 0 < t) : HasDerivAt u (v t) t := by
    have hxAt : HasDerivAt x (v t) t := by
      have h := hxy.1.differentiableOn (by norm_num) t ht.le
      exact (h.differentiableAt (Ici_mem_nhds ht)).hasDerivAt
    simpa [u, v] using hxAt.sub_const z
  have haux_at (t : ℝ) (ht : 0 < t) : HasDerivAt haux
      (-(c - ε) * ‖v t‖ ^ 2 - b * β ^ 2 * ‖g t‖ ^ 2
        + ε * β * inner ℝ (g t) (v t) - ε * b * β * inner ℝ (g t) (u t)) t := by
    have hk := (hu_at t ht).norm_sq.const_mul (c / 2)
    have hi := (hr_at t ht).inner ℝ (hu_at t ht)
    have hi' := (hk.add hi).const_smul ε
    have he := (hE_at t ht).add hi'
    change HasDerivAt (fun t => E t + ε *
      (c / 2 * ‖u t‖ ^ 2 + inner ℝ (r t) (u t))) _ _
    convert he using 1
    rw [← hvr t ht.le]
    dsimp [c]
    simp only [inner_sub_left, inner_smul_left, inner_add_left,
      real_inner_self_eq_norm_sq]
    simp [real_inner_comm]
    ring_nf
  have haux_deriv_nonpos : ∀ t, 0 < t → deriv haux t ≤ 0 := by
    intro t ht
    rw [(haux_at t ht).deriv]
    have hmul := mul_le_mul_of_nonneg_left (real_inner_le_norm (g t) (v t))
      (mul_nonneg hε.le hβ.le)
    have hsq := mul_nonneg hε.le (sq_nonneg (‖v t‖ - β * ‖g t‖))
    have hgu := hgrad_inner t
    have hcv : 0 ≤ c - ε - ε / 2 := by linarith
    have hcb : 0 ≤ b - ε / 2 := by linarith
    have hvterm : 0 ≤ (c - ε - ε / 2) * ‖v t‖ ^ 2 :=
      mul_nonneg hcv (sq_nonneg _)
    have hgterm : 0 ≤ (b - ε / 2) * β ^ 2 * ‖g t‖ ^ 2 := by positivity
    have hgu' : 0 ≤ ε * b * β * inner ℝ (g t) (u t) := by positivity
    nlinarith
  have haux_cont : ContinuousOn haux (Set.Ici (0 : ℝ)) := by
    have hu_cont : ContinuousOn u (Set.Ici (0 : ℝ)) := by
      simpa [u] using hx_cont.sub continuousOn_const
    have hcross_cont : ContinuousOn (fun t => inner ℝ (r t) (u t))
        (Set.Ici (0 : ℝ)) := hr_cont.inner hu_cont
    have hbracket : ContinuousOn (fun t => c / 2 * ‖u t‖ ^ 2 +
        inner ℝ (r t) (u t)) (Set.Ici (0 : ℝ)) :=
      (continuousOn_const.mul (hu_cont.norm.pow 2)).add hcross_cont
    simpa [haux] using hE_cont.add (hbracket.const_mul ε)
  have haux_diff : DifferentiableOn ℝ haux (interior (Set.Ici (0 : ℝ))) := by
    intro t ht
    have ht' : 0 < t := by simpa [interior_Ici] using ht
    exact (haux_at t ht').differentiableAt.differentiableWithinAt
  have haux_anti : AntitoneOn haux (Set.Ici (0 : ℝ)) :=
    antitoneOn_of_deriv_nonpos (convex_Ici 0) haux_cont haux_diff
      (fun t ht => haux_deriv_nonpos t (by simpa [interior_Ici] using ht))
  rcases hbounded with ⟨m, hm⟩
  have hE_lower : ∀ t, 0 ≤ t → κ * m + (1 / 2) * ‖r t‖ ^ 2 ≤ E t := by
    intro t ht
    dsimp [E]
    have hm' := hm (x t)
    exact add_le_add (mul_le_mul_of_nonneg_left hm' hκ.le) le_rfl
  have haux_lower : ∀ t, 0 ≤ t → κ * m + ε * c / 4 * ‖u t‖ ^ 2 ≤ haux t := by
    intro t ht
    have hcross := real_inner_le_norm (-(r t)) (u t)
    rw [inner_neg_left, norm_neg] at hcross
    have hcross' : -‖r t‖ * ‖u t‖ ≤ inner ℝ (r t) (u t) := by linarith
    have hcross_scaled := mul_le_mul_of_nonneg_left hcross' hε.le
    have hs := sq_nonneg (‖r t‖ - ε * ‖u t‖)
    have hEm := hE_lower t ht
    have hcc : 0 ≤ c - 2 * ε := by linarith
    have hcoef : 0 ≤ ε * (c - 2 * ε) / 4 := by
      exact div_nonneg (mul_nonneg hε.le hcc) (by norm_num)
    have hcoefnu := mul_nonneg hcoef (sq_nonneg ‖u t‖)
    dsimp [haux]
    nlinarith
  let q : ℝ → ℝ := fun t => haux (max t 0)
  have hqanti : Antitone q := by
    intro s t hst
    exact haux_anti (le_max_right s 0) (le_max_right t 0)
      (max_le_max_right 0 hst)
  have hq_lower : BddBelow (Set.range q) := by
    refine ⟨κ * m, ?_⟩
    rintro y ⟨t, rfl⟩
    exact (le_add_of_nonneg_right (by positivity)).trans
      (haux_lower (max t 0) (le_max_right t 0))
  have haux_lim : ∃ l : ℝ, Tendsto haux atTop (nhds l) := by
    refine ⟨⨅ t, q t, ?_⟩
    apply (tendsto_atTop_ciInf hqanti hq_lower).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simp [q, max_eq_left ht]
  have hdist_sq_lim : ∃ l : ℝ, Tendsto (fun t => ‖u t‖ ^ 2) atTop (nhds l) := by
    rcases haux_lim with ⟨laux, hlaux⟩
    rcases hE_lim with ⟨lE, hlE⟩
    have hupper : ∀ t, 0 ≤ t → haux t ≤ haux 0 := by
      intro t ht
      exact haux_anti (by simp) ht ht
    let Q : ℝ := 4 * (haux 0 - κ * m) / (ε * c)
    have hQ : 0 ≤ Q := by
      have h0 := haux_lower 0 (by norm_num)
      have hnon : 0 ≤ ε * c / 4 * ‖u 0‖ ^ 2 := by positivity
      have hnum : 0 ≤ haux 0 - κ * m := by nlinarith [h0, hnon]
      dsimp [Q]
      exact div_nonneg (mul_nonneg (by norm_num) hnum)
        (le_of_lt (mul_pos hε hc))
    have hQbound : ∀ t, 0 ≤ t → ‖u t‖ ^ 2 ≤ Q := by
      intro t ht
      have hl := haux_lower t ht
      have hu := hupper t ht
      have hpos : 0 < ε * c := mul_pos hε hc
      dsimp [Q]
      apply (le_div_iff₀ hpos).2
      nlinarith
    have hCbound : ∃ C : ℝ, ∀ t, 0 ≤ t → ‖u t‖ ≤ C := by
      refine ⟨Real.sqrt Q, ?_⟩
      intro t ht
      have hq := hQbound t ht
      have hsqrt : (Real.sqrt Q) ^ 2 = Q := Real.sq_sqrt hQ
      nlinarith [Real.sqrt_nonneg Q, norm_nonneg (u t)]
    have hinner_lim : Tendsto (fun t => inner ℝ (r t) (u t)) atTop (nhds 0) := by
      rcases hCbound with ⟨C, hC⟩
      have hbound : ∀ᶠ t in atTop, ‖inner ℝ (r t) (u t)‖ ≤ C * ‖r t‖ := by
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
        rw [Real.norm_eq_abs]
        exact (abs_real_inner_le_norm (r t) (u t)).trans (by
          calc
            ‖r t‖ * ‖u t‖ ≤ ‖r t‖ * C :=
              mul_le_mul_of_nonneg_left (hC t ht) (norm_nonneg _)
            _ = C * ‖r t‖ := by ring)
      have hprod : Tendsto (fun t => C * ‖r t‖) atTop (nhds 0) := by
        simpa using (tendsto_const_nhds.mul hr_lim.norm)
      exact squeeze_zero_norm' hbound hprod
    have hdiff := hlaux.sub hlE
    have hsub := hdiff.sub (hinner_lim.const_mul ε)
    have hscale := hsub.const_mul (2 / (ε * c))
    have hscale' : Tendsto (fun t => 2 / (ε * c) *
        (haux t - E t - ε * inner ℝ (r t) (u t))) atTop
        (nhds ((2 / (ε * c)) * (laux - lE))) := by
      simpa using hscale
    refine ⟨(2 / (ε * c)) * (laux - lE), ?_⟩
    convert hscale' using 1
    funext t
    dsimp [haux]
    field_simp [ne_of_gt (mul_pos hε hc)]
    ring
  rcases hdist_sq_lim with ⟨lq, hlq⟩
  have hlq_nonneg : 0 ≤ lq :=
    ge_of_tendsto hlq (Filter.Eventually.of_forall (fun t => sq_nonneg ‖u t‖))
  have hnorm_lim : Tendsto (fun t => ‖u t‖) atTop (nhds (Real.sqrt lq)) := by
    have hs : Tendsto (fun y : ℝ => Real.sqrt y) (nhds lq)
        (nhds (Real.sqrt lq)) := Real.continuous_sqrt.continuousAt
    have hs := hs.comp hlq
    simpa [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hs
  refine ⟨Real.sqrt lq, ?_⟩
  simpa [u] using hnorm_lim


/--
Theorem 6.3: (Human checked)
weak convergence of `(g-DIN)` to an unconstrained minimizer for convex
potentials.
-/
theorem gdin_weakly_converges_to_argmin {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Φ : H → ℝ) (β a b : ℝ)
    (x y : ℝ → H) (hbounded : ∃ m : ℝ, ∀ x, m ≤ Φ x) (x₀ y₀ : H)
    (hΦ : ContDiff ℝ 1 Φ)
    (hloclip : ∀ R : ℝ, ∃ L : ℝ, ∀ x y, ‖x‖ ≤ R →
      ‖y‖ ≤ R → ‖gradient Φ x - gradient Φ y‖ ≤ L * ‖x - y‖)
    (hβ : 0 < β) (hb : 0 < b) (hab : 0 < b + a)
    (hconvex : ConvexOn ℝ Set.univ Φ)
    (hxy : ContDiffOn ℝ 1 x (Set.Ici 0) ∧ ContDiffOn ℝ 2 y (Set.Ici 0))
    (hmin : (Optimization.argminSet Φ).Nonempty)
    (hsol : IsSolution_gDIN Φ β a b x₀ y₀ x y) :
    ∃ z, z ∈ Optimization.argminSet Φ ∧
      Tendsto (fun t => toWeakSpace ℝ H (x t)) atTop (nhds (toWeakSpace ℝ H z)) := by
  have hab' : 0 < a + b := by linarith
  have hgrad_lip : LipschitzOnBoundedSets (gradient Φ) :=
    gdin_grad_lipschitzOnBounded_thm6 (gradient Φ) hloclip
  have hdist : ∀ z, z ∈ Optimization.argminSet Φ →
      ∃ d : ℝ, Tendsto (fun t => ‖x t - z‖) atTop (nhds d) := by
    intro z hz
    exact gdin_distance_limit Φ β a b x y hbounded x₀ y₀ hΦ hloclip hβ hb hab
      hconvex hxy hsol hz
  have hphi_x : ∃ l : ℝ, Tendsto (fun t => Φ (x t)) atTop (nhds l) :=
    gdin_phi_limit Φ β a b hΦ hbounded hβ hb hab' x₀ y₀ x y hxy hsol
  have hx_bounded : Bornology.IsBounded (x '' Set.Ici (0 : ℝ)) := by
    rcases hmin with ⟨z₀, hz₀⟩
    rcases hdist z₀ hz₀ with ⟨d₀, hd₀⟩
    obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.1 hd₀) 1 zero_lt_one
    let T₀ : ℝ := max T 0
    have htail : ∀ t, T₀ ≤ t → ‖x t - z₀‖ ≤ |d₀| + 1 := by
      intro t ht
      have hdist' : dist (‖x t - z₀‖) d₀ < 1 := by
        simpa [Real.dist_eq] using hT t (le_trans (le_max_left T 0) ht)
      have habs : |‖x t - z₀‖ - d₀| < 1 := by simpa [Real.dist_eq] using hdist'
      have hle : ‖x t - z₀‖ - d₀ ≤ |‖x t - z₀‖ - d₀| := le_abs_self _
      have hnormd : ‖x t - z₀‖ ≤ d₀ + 1 := by nlinarith
      exact hnormd.trans (by linarith [le_abs_self d₀])
    have hcompact : IsCompact (x '' Set.Icc (0 : ℝ) T₀) := by
      exact isCompact_Icc.image_of_continuousOn
        (hxy.1.continuousOn.mono Set.Icc_subset_Ici_self)
    rcases isBounded_iff_forall_norm_le.mp hcompact.isBounded with ⟨R₀, hR₀⟩
    refine isBounded_iff_forall_norm_le.mpr ⟨max R₀ (|d₀| + 1 + ‖z₀‖), ?_⟩
    rintro q ⟨t, ht, rfl⟩
    by_cases hle : t ≤ T₀
    · exact (hR₀ _ ⟨t, ⟨ht, hle⟩, rfl⟩).trans (le_max_left _ _)
    · have hge : T₀ ≤ t := le_of_not_ge hle
      have htri : ‖x t‖ ≤ ‖x t - z₀‖ + ‖z₀‖ := by
        calc
          ‖x t‖ = ‖(x t - z₀) + z₀‖ := by rw [sub_add_cancel]
          _ ≤ ‖x t - z₀‖ + ‖z₀‖ := norm_add_le _ _
      have htri' : ‖x t - z₀‖ + ‖z₀‖ ≤ (|d₀| + 1) + ‖z₀‖ := by
        simpa [add_comm, add_left_comm, add_assoc] using
          (add_le_add_right (htail t hge) ‖z₀‖)
      exact (htri.trans htri').trans (le_max_right _ _)
  have hbounded_asym := gdin_bounded_asymptotics Φ β a b hΦ hbounded hgrad_lip
    hβ hb hab' x₀ y₀ x y hxy hsol hx_bounded
  have hgrad_at_top : Tendsto (fun t => gradient Φ (x t)) atTop (nhds 0) := hbounded_asym.2.2.2
  have hgrad_at (y : H) : HasGradientAt Φ (gradient Φ y) y :=
    (hΦ.differentiable (by norm_num) y).hasGradientAt
  have hsupport : ∀ y p : H,
      Φ y + inner ℝ (gradient Φ y) (p - y) ≤ Φ p := by
    intro y p
    exact convex_supporting_baillon_haddad Φ (gradient Φ) hconvex
      (fun w => hgrad_at w) y p
  have hinner_zero_of_strong_bounded : ∀ (a b : ℕ → H),
      Tendsto a atTop (nhds 0) → Bornology.IsBounded (Set.range b) →
        Tendsto (fun n => inner ℝ (a n) (b n)) atTop (nhds 0) := by
    intro a b ha hb
    rcases isBounded_iff_forall_norm_le.mp hb with ⟨C, hC⟩
    let M : ℝ := max C 0
    have hbM : ∀ n, ‖b n‖ ≤ M := by
      intro n
      exact (hC _ ⟨n, rfl⟩).trans (le_max_left _ _)
    have hanorm : Tendsto (fun n => ‖a n‖) atTop (nhds 0) := by
      simpa using ha.norm
    have hbound : ∀ n, |inner ℝ (a n) (b n)| ≤ ‖a n‖ * M := by
      intro n
      calc
        |inner ℝ (a n) (b n)| ≤ ‖a n‖ * ‖b n‖ := by
          simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (a n) (b n)
        _ ≤ ‖a n‖ * M := mul_le_mul_of_nonneg_left (hbM n) (norm_nonneg _)
    have hmajor : Tendsto (fun n => ‖a n‖ * M) atTop (nhds 0) := by
      simpa [zero_mul] using hanorm.mul tendsto_const_nhds
    have habs : Tendsto (fun n => |inner ℝ (a n) (b n)|) atTop (nhds 0) :=
      squeeze_zero (fun _ => abs_nonneg _) hbound hmajor
    have hneg : Tendsto (fun n => -|inner ℝ (a n) (b n)|) atTop (nhds 0) := by
      simpa using habs.neg
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hneg habs
      (fun _ => neg_abs_le _) (fun _ => le_abs_self _)
  have hcluster : ∀ s : ℕ → ℝ, Tendsto s atTop atTop → ∀ z,
      Tendsto (fun n => toWeakSpace ℝ H (x (s n))) atTop
        (nhds (toWeakSpace ℝ H z)) → z ∈ Optimization.argminSet Φ := by
    intro s hs z hweak
    rcases hphi_x with ⟨l, hl⟩
    have hgrad_seq : Tendsto (fun n => gradient Φ (x (s n))) atTop (nhds 0) :=
      hgrad_at_top.comp hs
    have hxseq_bounded : Bornology.IsBounded (Set.range (fun n => x (s n))) :=
      bounded_range_of_tendsto_weakly hweak
    have hinner_x : Tendsto
        (fun n => inner ℝ (gradient Φ (x (s n))) (x (s n))) atTop (nhds 0) :=
      hinner_zero_of_strong_bounded _ _ hgrad_seq hxseq_bounded
    have hineq_limit : ∀ p : H, l ≤ Φ p := by
      intro p
      have hlseq : Tendsto (fun n => Φ (x (s n))) atTop (nhds l) := hl.comp hs
      have hinner_p : Tendsto
          (fun n => inner ℝ (gradient Φ (x (s n))) p) atTop (nhds 0) := by
        simpa using hinner_zero_of_strong_bounded _ (fun _ => p) hgrad_seq
          (by simp)
      have hinner_diff : Tendsto
          (fun n => inner ℝ (gradient Φ (x (s n))) (p - x (s n))) atTop (nhds 0) := by
        simpa [inner_sub_right] using hinner_p.sub hinner_x
      have hsum : Tendsto
          (fun n => Φ (x (s n)) + inner ℝ (gradient Φ (x (s n)))
            (p - x (s n))) atTop (nhds l) := by
        simpa using hlseq.add hinner_diff
      apply le_of_tendsto hsum
      exact Filter.Eventually.of_forall (fun n => hsupport (x (s n)) p)
    let f : H → EReal := fun y => (Φ y : EReal)
    have hf_lsc : LowerSemicontinuous f := by
      simpa [f] using (continuous_coe_real_ereal.comp hΦ.continuous).lowerSemicontinuous
    have hf_quasi : QuasiconvexOn ℝ Set.univ f := by
      rw [ERealFunction.quasiconvexOn_univ_iff_convex_lowerLevelSet f]
      intro ξ
      apply (convex_iff_forall_pos).2
      intro a ha b hb wa wb hwa hwb hwab
      have haE := (ERealFunction.mem_lowerLevelSet_iff f ξ a).1 ha
      have hbE := (ERealFunction.mem_lowerLevelSet_iff f ξ b).1 hb
      change (Φ a : EReal) ≤ (ξ : EReal) at haE
      change (Φ b : EReal) ≤ (ξ : EReal) at hbE
      have ha' : Φ a ≤ ξ := by exact_mod_cast haE
      have hb' : Φ b ≤ ξ := by exact_mod_cast hbE
      have hconv := hconvex.2 (Set.mem_univ a) (Set.mem_univ b) hwa.le hwb.le hwab
      have hconv' : Φ (wa • a + wb • b) ≤ wa * Φ a + wb * Φ b := by
        simpa [smul_eq_mul] using hconv
      have hweighted : wa * Φ a + wb * Φ b ≤ ξ := by
        calc
          wa * Φ a + wb * Φ b ≤ wa * ξ + wb * ξ := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left ha' hwa.le)
              (mul_le_mul_of_nonneg_left hb' hwb.le)
          _ = ξ := by rw [← add_mul, hwab, one_mul]
      have hcombo : Φ (wa • a + wb • b) ≤ ξ := hconv'.trans hweighted
      apply (ERealFunction.mem_lowerLevelSet_iff f ξ (wa • a + wb • b)).2
      change (Φ (wa • a + wb • b) : EReal) ≤ (ξ : EReal)
      exact_mod_cast hcombo
    have hfweak_lsc := ERealFunction.weaklyLowerSemicontinuous_of_quasiconvexOn_univ hf_quasi hf_lsc
    have hlseq : Tendsto (fun n => Φ (x (s n))) atTop (nhds l) := hl.comp hs
    have hlseqE : Tendsto (fun n => f (x (s n))) atTop (nhds (l : EReal)) := by
      simpa [f] using (continuous_coe_real_ereal.tendsto l).comp hlseq
    have hz_le_l : f z ≤ (l : EReal) := by
      calc
        f z = (f ∘ (toWeakSpace ℝ H).symm) (toWeakSpace ℝ H z) := by simp
        _ ≤ liminf (f ∘ (toWeakSpace ℝ H).symm)
            (nhds (toWeakSpace ℝ H z)) := hfweak_lsc.le_liminf _
        _ ≤ liminf (f ∘ (toWeakSpace ℝ H).symm)
            (Filter.map (fun n => toWeakSpace ℝ H (x (s n))) atTop) :=
          Filter.liminf_le_liminf_of_le hweak
        _ = liminf (f ∘ (fun n => x (s n))) atTop := by
          rw [← Filter.liminf_comp]
          congr 1
        _ = (l : EReal) := hlseqE.liminf_eq
    have hz_le_l_real : Φ z ≤ l := by
      change (Φ z : EReal) ≤ (l : EReal) at hz_le_l
      exact_mod_cast hz_le_l
    have hl_le_z := hineq_limit z
    have hz_eq : Φ z = l := le_antisymm hz_le_l_real hl_le_z
    intro y
    have hl_le_y := hineq_limit y
    rw [hz_eq]
    exact hl_le_y
  exact Alvarez2002.opial_continuous_time x (Optimization.argminSet Φ) hmin hcluster hdist
end Alvarez2002
