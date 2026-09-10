import Mathlib
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_7
namespace Alvarez2002

/-!
## The Łojasiewicz gradient inequality as an explicit external input

Theorem 4.1 of the source assumes only that `Φ` is real analytic, and deduces convergence from
Łojasiewicz's lemma (Lemma 4.1 of the paper, quoted from [25]): near a critical point `a` of a
real-analytic potential there are `σ > 0` and `θ ∈ (0, 1/2)` with

  `|Φ x - Φ a| ^ (1 - θ) ≤ ‖∇Φ x‖`  for `‖x - a‖ < σ`.

That finite-dimensional real-analytic theorem is not available in Mathlib — it needs a
multivariate curve-selection or Puiseux-type argument — so we take its conclusion as an
explicit hypothesis, `HasLojasiewiczGradientInequality`, and record in the statements below
that this is exactly the external input the paper cites.
-/

/-- The Łojasiewicz gradient inequality at every critical point: the external analytic input
that the source cites as Lemma 4.1 (Łojasiewicz [25]).  It is automatic for real-analytic `Φ`,
which is precisely the content of the cited lemma. -/
def HasLojasiewiczGradientInequality {N : Type*} [Fintype N]
    (Φ : EuclideanSpace ℝ N → ℝ) : Prop :=
  ∀ a : EuclideanSpace ℝ N, gradient Φ a = 0 →
    ∃ σ θ : ℝ, 0 < σ ∧ 0 < θ ∧ θ < 1 / 2 ∧
      ∀ x, ‖x - a‖ < σ → Real.rpow |Φ x - Φ a| (1 - θ) ≤ ‖gradient Φ x‖

/-- Łojasiewicz's local gradient inequality near a critical point.

The `C¹` and analyticity hypotheses record the analytic setting of the source (Lemma 4.1 is a
statement about real-analytic potentials); the substance used by the argument is the explicit
hypothesis `hLoj`, which by Łojasiewicz's theorem holds for every real-analytic `Φ`. -/
theorem lojasiewicz_gradient_inequality {N : Type*} [Fintype N] (Φ : EuclideanSpace ℝ N → ℝ)
    (a : EuclideanSpace ℝ N)
    (_hΦdiff : ContDiff ℝ 1 Φ)
    (_hanalytic : ∃ Ω : Set (EuclideanSpace ℝ N), IsRealAnalyticOn Ω Φ ∧ a ∈ Ω)
    (hcritical : gradient Φ a = 0) (hLoj : HasLojasiewiczGradientInequality Φ) :
    ∃ σ θ : ℝ, 0 < σ ∧ 0 < θ ∧ θ < 1 / 2 ∧
      ∀ x, ‖x - a‖ < σ → Real.rpow |Φ x - Φ a| (1 - θ) ≤ ‖gradient Φ x‖ :=
  hLoj a hcritical
end Alvarez2002

/-!
## One-dimensional Łojasiewicz gradient inequality

For a real-analytic function `h : ℝ → ℝ` with `h 0 = 0` there are `σ > 0` and
`θ ∈ (0, 1/2)` with `|h t| ^ (1 - θ) ≤ |h'(t)|` for every `|t| < σ`.  This is the
one-variable ingredient of the finite-dimensional Łojasiewicz gradient inequality.
-/

open Filter
open scoped Topology

namespace LojasiewiczOneDim

/-- **One-dimensional Łojasiewicz gradient inequality.**

If `h : ℝ → ℝ` is real-analytic at `0` with `h 0 = 0`, then there are `σ > 0`
and `θ ∈ (0, 1/2)` such that `|h t| ^ (1 - θ) ≤ |deriv h t|` for all `t` with
`|t| < σ`. -/
theorem exists_rpow_abs_le_abs_deriv (h : ℝ → ℝ) (h0 : h 0 = 0) (han : AnalyticAt ℝ h 0) :
    ∃ σ θ : ℝ, 0 < σ ∧ 0 < θ ∧ θ < 1 / 2 ∧
      ∀ t : ℝ, |t| < σ → |h t| ^ (1 - θ) ≤ |deriv h t| := by
  by_cases hz : ∀ᶠ z in 𝓝 (0 : ℝ), h z = 0
  · -- `h` vanishes in a neighbourhood of `0`
    rcases Metric.mem_nhds_iff.mp hz with ⟨ρ, hρ, hsub⟩
    refine ⟨ρ, 1 / 4, hρ, by norm_num, by norm_num, ?_⟩
    intro t ht
    have hht : h t = 0 := hsub (by simpa [Metric.mem_ball, Real.dist_eq, sub_zero] using ht)
    have hev : ∀ᶠ y in 𝓝 t, h y = 0 := by
      rw [Metric.eventually_nhds_iff]
      refine ⟨ρ - |t|, by linarith, ?_⟩
      intro y hy
      apply hsub
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]
      have hy' : |y - t| < ρ - |t| := by simpa [Real.dist_eq] using hy
      calc |y| = |y - t + t| := by ring_nf
        _ ≤ |y - t| + |t| := abs_add_le _ _
        _ < ρ := by linarith
    have hdt : deriv h t = 0 := by
      rw [Filter.EventuallyEq.deriv_eq hev]
      simp
    rw [hht, hdt]
    simp only [abs_zero]
    rw [Real.zero_rpow (by norm_num : (1 : ℝ) - 1 / 4 ≠ 0)]
  · -- main case: `h` has a nontrivial local factorisation `t ↦ t ^ n * u t`
    obtain ⟨n, u, hu_an, hu_ne, hu_eq⟩ := han.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hz
    rcases Metric.mem_nhds_iff.mp hu_eq with ⟨ρ₁, hρ₁, hsub₁⟩
    have hn1 : 1 ≤ n := by
      by_contra hn
      have hn0 : n = 0 := by omega
      subst hn0
      have heq : h =ᶠ[𝓝 (0 : ℝ)] u := by
        filter_upwards [hu_eq] with z hzv
        simpa using hzv
      have key := heq.eq_of_nhds
      rw [h0] at key
      exact hu_ne key.symm
    set c : ℝ := |u 0| with hc
    have hcpos : 0 < c := by rw [hc]; exact abs_pos.mpr hu_ne
    -- continuity data for `u` and for `deriv u`
    obtain ⟨δu, hδu, hδusub⟩ :=
      Metric.continuousAt_iff.mp hu_an.continuousAt (c / 2) (by linarith)
    have hdu_cont : ContinuousAt (deriv u) 0 := by
      have h1 : ContinuousAt (fun z : ℝ => (fderiv ℝ u z) (1 : ℝ)) 0 :=
        (hu_an.fderiv.continuousAt).clm_apply continuousAt_const
      simpa only [fderiv_apply_one_eq_deriv] using h1
    set M : ℝ := |deriv u 0| + 1 with hM
    have hMpos : 0 < M := by rw [hM]; positivity
    obtain ⟨δd, hδd, hδdsub⟩ := Metric.continuousAt_iff.mp hdu_cont M hMpos
    have hev_an : ∀ᶠ t in 𝓝 (0 : ℝ), AnalyticAt ℝ u t :=
      (isOpen_analyticAt ℝ u).mem_nhds hu_an
    have hev_ud : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ u t :=
      hev_an.mono fun t ht => (ht.contDiffAt (n := 1)).differentiableAt_one
    have hev_hd : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ᶠ y in 𝓝 t, h y = y ^ n * u y := by
      rw [Metric.eventually_nhds_iff]
      refine ⟨ρ₁, hρ₁, ?_⟩
      intro t ht
      rw [Metric.eventually_nhds_iff]
      refine ⟨ρ₁ - dist t 0, by linarith, ?_⟩
      intro y hy
      have hρ : dist y 0 < ρ₁ := by linarith [dist_triangle y t 0]
      simpa [smul_eq_mul] using hsub₁ (by simpa [Metric.mem_ball] using hρ)
    -- the exponent
    set θ : ℝ := 1 / (2 * ((n : ℝ) + 1)) with hθ
    have hθpos : 0 < θ := by rw [hθ]; positivity
    have hθhalf : θ < 1 / 2 := by
      rw [hθ]
      have h2 : (2 : ℝ) < 2 * ((n : ℝ) + 1) := by
        have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        linarith
      have h := one_div_lt_one_div_of_lt (show (0 : ℝ) < 2 by norm_num) h2
      simpa using h
    have hθn : (n : ℝ) * θ < 1 := by
      rw [hθ, mul_one_div, div_lt_one (by positivity)]
      have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      linarith
    have h1nθ : 0 < 1 - (n : ℝ) * θ := by linarith
    -- the constants
    set A : ℝ := 3 * c / 2 with hA
    have hApos : 0 < A := by rw [hA]; linarith
    set B : ℝ := n * c / 4 with hB
    have hBpos : 0 < B := by rw [hB]; positivity
    set η₂ : ℝ := n * c / (8 * M) with hη₂
    have hη₂pos : 0 < η₂ := by rw [hη₂]; positivity
    set η₁ : ℝ := (B / A ^ (1 - θ)) ^ (1 / (1 - (n : ℝ) * θ)) with hη₁
    have hη₁pos : 0 < η₁ := by
      rw [hη₁]
      exact Real.rpow_pos_of_pos (div_pos hBpos (Real.rpow_pos_of_pos hApos _)) _
    have hδu_ev : ∀ᶠ t in 𝓝 (0 : ℝ), dist (u t) (u 0) < c / 2 := by
      rw [Metric.eventually_nhds_iff]
      exact ⟨δu, hδu, fun y hy => hδusub hy⟩
    have hδd_ev : ∀ᶠ t in 𝓝 (0 : ℝ), dist (deriv u t) (deriv u 0) < M := by
      rw [Metric.eventually_nhds_iff]
      exact ⟨δd, hδd, fun y hy => hδdsub hy⟩
    have hη₁_ev : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < η₁ := by
      rw [Metric.eventually_nhds_iff]
      refine ⟨η₁, hη₁pos, ?_⟩
      intro y hy
      rwa [Real.dist_eq, sub_zero] at hy
    have hη₂_ev : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < η₂ := by
      rw [Metric.eventually_nhds_iff]
      refine ⟨η₂, hη₂pos, ?_⟩
      intro y hy
      rwa [Real.dist_eq, sub_zero] at hy
    have hev_ineq : ∀ᶠ t in 𝓝 (0 : ℝ), |h t| ^ (1 - θ) ≤ |deriv h t| := by
      filter_upwards [hu_eq, hδu_ev, hδd_ev, hev_ud, hev_hd, hη₁_ev, hη₂_ev]
        with t ht_eq ht_u ht_du ht_ud ht_hd ht_η₁ ht_η₂
      by_cases ht0 : t = 0
      · subst ht0
        simp [h0, abs_zero, Real.zero_rpow (by linarith : (1 : ℝ) - θ ≠ 0)]
      · have htabs : 0 < |t| := abs_pos.mpr ht0
        have hht : h t = t ^ n * u t := by simpa [smul_eq_mul] using ht_eq
        -- derivative formula
        have hprod : HasDerivAt (fun z : ℝ => z ^ n * u z)
            (n * t ^ (n - 1) * u t + t ^ n * deriv u t) t := by
          have h1 : HasDerivAt (fun z : ℝ => z ^ n) (n * t ^ (n - 1)) t := by
            simpa using hasDerivAt_pow n t
          exact h1.mul ht_ud.hasDerivAt
        have hderivh : deriv h t = n * t ^ (n - 1) * u t + t ^ n * deriv u t := by
          rw [Filter.EventuallyEq.deriv_eq ht_hd, hprod.deriv]
        have hfac : n * t ^ (n - 1) * u t + t ^ n * deriv u t
            = t ^ (n - 1) * (n * u t + t * deriv u t) := by
          have hpow : t ^ n = t ^ (n - 1) * t := by
            conv_lhs => rw [← Nat.sub_add_cancel hn1, pow_succ]
          rw [hpow]; ring
        -- bounds on `u t` in terms of `c`
        have hut_lo : c / 2 ≤ |u t| := by
          have h := ht_u
          rw [Real.dist_eq] at h
          have h' := abs_sub_abs_le_abs_sub (u 0) (u t)
          rw [← hc, abs_sub_comm] at h'
          linarith [le_abs_self (c - |u t|)]
        have hut_hi : |u t| ≤ A := by
          have h := ht_u
          rw [Real.dist_eq] at h
          have h2 : |u t| ≤ |u 0| + |u t - u 0| := by
            have h'' := abs_sub_abs_le_abs_sub (u t) (u 0)
            linarith [le_abs_self (|u t| - |u 0|)]
          rw [← hc] at h2
          rw [hA]
          linarith
        have hdu_hi : |deriv u t| ≤ 2 * M := by
          have h := ht_du
          rw [Real.dist_eq] at h
          have hM1 : |deriv u 0| = M - 1 := by rw [hM]; ring
          have h2 : |deriv u t| ≤ |deriv u 0| + |deriv u t - deriv u 0| := by
            have h'' := abs_sub_abs_le_abs_sub (deriv u t) (deriv u 0)
            linarith [le_abs_self (|deriv u t| - |deriv u 0|)]
          rw [hM1] at h2
          linarith
        have hsmall : |t| * |deriv u t| ≤ n * c / 4 := by
          have h1 : |t| * |deriv u t| ≤ η₂ * (2 * M) :=
            mul_le_mul (le_of_lt ht_η₂) hdu_hi (abs_nonneg _) (le_of_lt hη₂pos)
          have h2 : η₂ * (2 * M) = n * c / 4 := by
            rw [hη₂]; field_simp; ring
          linarith [h1, h2.le]
        -- lower bound on `|n * u t + t * deriv u t|`
        have hnt : B ≤ |n * u t + t * deriv u t| := by
          have hsplit : |n * u t| - |t * deriv u t| ≤ |n * u t + t * deriv u t| := by
            have h3 : |n * u t| ≤ |n * u t + t * deriv u t| + |t * deriv u t| := by
              calc |n * u t| = |(n * u t + t * deriv u t) + (-(t * deriv u t))| := by
                    congr 1; ring
                _ ≤ |n * u t + t * deriv u t| + |-(t * deriv u t)| := abs_add_le _ _
                _ = |n * u t + t * deriv u t| + |t * deriv u t| := by rw [abs_neg]
            linarith
          have h1 : |n * u t| = (n : ℝ) * |u t| := by
            rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
          have h2 : |t * deriv u t| = |t| * |deriv u t| := abs_mul _ _
          have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          have h3 : (n : ℝ) * (c / 2) ≤ (n : ℝ) * |u t| := mul_le_mul_of_nonneg_left hut_lo hn0
          have h4 : (n : ℝ) * (c / 2) = n * c / 2 := by ring
          have h5 : n * c / 2 - n * c / 4 = n * c / 4 := by ring
          rw [hB]
          linarith
        have hlower : |t| ^ (n - 1) * B ≤ |deriv h t| := by
          rw [hderivh, hfac, abs_mul, abs_pow]
          exact mul_le_mul_of_nonneg_left hnt (by positivity)
        -- upper bound via `|h t| ≤ |t| ^ n * A`
        have hupper : |h t| ^ (1 - θ)
            ≤ |t| ^ (n - 1) * (|t| ^ (1 - (n : ℝ) * θ) * A ^ (1 - θ)) := by
          have hht' : |h t| ≤ |t| ^ (n : ℝ) * A := by
            rw [hht, abs_mul, abs_pow, ← Real.rpow_natCast |t| n]
            exact mul_le_mul_of_nonneg_left hut_hi (Real.rpow_nonneg (abs_nonneg t) (n : ℝ))
          have h1 : |h t| ^ (1 - θ)
              ≤ (|t| ^ (n : ℝ) * A) ^ (1 - θ) :=
            Real.rpow_le_rpow (abs_nonneg _) hht' (by linarith)
          have h2 : (|t| ^ (n : ℝ) * A) ^ (1 - θ)
              = (|t| ^ (n : ℝ)) ^ (1 - θ) * A ^ (1 - θ) :=
            Real.mul_rpow (Real.rpow_nonneg (abs_nonneg t) (n : ℝ)) hApos.le
          have h3 : (|t| ^ (n : ℝ)) ^ (1 - θ)
              = |t| ^ ((n : ℝ) * (1 - θ)) :=
            (Real.rpow_mul (abs_nonneg t) (n : ℝ) (1 - θ)).symm
          have h4 : |t| ^ ((n : ℝ) * (1 - θ))
              = |t| ^ ((n : ℝ) - 1) * |t| ^ (1 - (n : ℝ) * θ) := by
            have hs : (n : ℝ) * (1 - θ) = ((n : ℝ) - 1) + (1 - (n : ℝ) * θ) := by ring
            rw [hs, Real.rpow_add (abs_pos.mpr ht0)]
          have h5 : |t| ^ ((n : ℝ) - 1) = |t| ^ (n - 1) := by
            have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
              rw [Nat.cast_sub hn1]; norm_num
            rw [← hcast, Real.rpow_natCast]
          calc |h t| ^ (1 - θ) ≤ (|t| ^ (n : ℝ) * A) ^ (1 - θ) := h1
            _ = (|t| ^ (n : ℝ)) ^ (1 - θ) * A ^ (1 - θ) := h2
            _ = |t| ^ ((n : ℝ) * (1 - θ)) * A ^ (1 - θ) := by rw [h3]
            _ = (|t| ^ ((n : ℝ) - 1) * |t| ^ (1 - (n : ℝ) * θ)) * A ^ (1 - θ) := by rw [h4]
            _ = |t| ^ (n - 1) * (|t| ^ (1 - (n : ℝ) * θ) * A ^ (1 - θ)) := by
                  rw [h5]; ring
        -- the smallness condition fixes the exponent
        have hη₁' : |t| ^ (1 - (n : ℝ) * θ) ≤ B / A ^ (1 - θ) := by
          have hxpos : 0 < B / A ^ (1 - θ) :=
            div_pos hBpos (Real.rpow_pos_of_pos hApos (1 - θ))
          have h1 : |t| ^ (1 - (n : ℝ) * θ) < η₁ ^ (1 - (n : ℝ) * θ) :=
            Real.rpow_lt_rpow (abs_nonneg t) ht_η₁ h1nθ
          have h2 : η₁ ^ (1 - (n : ℝ) * θ) = B / A ^ (1 - θ) := by
            rw [hη₁, ← Real.rpow_mul hxpos.le, one_div, inv_mul_cancel₀ (ne_of_gt h1nθ),
              Real.rpow_one]
          linarith [h1, h2.le]
        have hfinal : |h t| ^ (1 - θ) ≤ |t| ^ (n - 1) * B := by
          have hA_nn : 0 ≤ A ^ (1 - θ) := Real.rpow_nonneg hApos.le (1 - θ)
          have h1 : |t| ^ (1 - (n : ℝ) * θ) * A ^ (1 - θ)
              ≤ (B / A ^ (1 - θ)) * A ^ (1 - θ) :=
            mul_le_mul_of_nonneg_right hη₁' hA_nn
          have h2 : (B / A ^ (1 - θ)) * A ^ (1 - θ) = B :=
            div_mul_cancel₀ B (ne_of_gt (Real.rpow_pos_of_pos hApos (1 - θ)))
          rw [h2] at h1
          exact le_trans hupper (mul_le_mul_of_nonneg_left h1 (by positivity))
        exact le_trans hfinal hlower
    rw [Metric.eventually_nhds_iff] at hev_ineq
    obtain ⟨σ, hσ, hσsub⟩ := hev_ineq
    refine ⟨σ, θ, hσ, hθpos, hθhalf, ?_⟩
    intro t ht
    exact hσsub (by rw [Real.dist_eq, sub_zero]; exact ht)

end LojasiewiczOneDim
