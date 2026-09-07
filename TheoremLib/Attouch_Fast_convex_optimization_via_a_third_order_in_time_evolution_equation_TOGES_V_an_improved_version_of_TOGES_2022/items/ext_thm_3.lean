import Mathlib
import Foundation.Hilbert.WeakConvergence

open Filter
open MeasureTheory

private theorem weighted_cesaro_real_tendsto_zero (w g : ℝ → ℝ) (t0 : ℝ)
    (hg : Tendsto g atTop (nhds 0))
    (hw_nonneg : ∀ t ≥ t0, 0 ≤ w t)
    (hw_integrable : ∀ a b, IntervalIntegrable w volume a b)
    (hwg_integrable : ∀ a b, IntervalIntegrable (fun s => w s * g s) volume a b)
    (hW : Tendsto (fun t => ∫ s in t0..t, w s) atTop atTop) :
    Tendsto (fun t => (∫ s in t0..t, w s)⁻¹ * ∫ s in t0..t, w s * g s) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  have hgabs : Tendsto (fun s => |g s|) atTop (nhds 0) := by
    simpa only [Real.norm_eq_abs] using (tendsto_zero_iff_norm_tendsto_zero.1 hg)
  obtain ⟨T1, hT1⟩ := Filter.eventually_atTop.1
    (hgabs.eventually (eventually_lt_nhds (by linarith : 0 < eps / 2)))
  let T := max t0 T1
  let A := ∫ s in t0..T, w s * g s
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1
    (Filter.tendsto_atTop.1 hW (max T (2 * |A| / eps + 1)))
  refine ⟨max T K, fun t ht => ?_⟩
  have hKt := hK t (le_trans (le_max_right _ _) ht)
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  have hlarge : 2 * |A| / eps < ∫ s in t0..t, w s := by
    have := le_max_right T (2 * |A| / eps + 1) |>.trans hKt
    linarith
  have hWpos : 0 < ∫ s in t0..t, w s :=
    lt_of_le_of_lt (div_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) heps.le) hlarge
  have hsplit : (∫ s in t0..t, w s * g s) = A + ∫ s in T..t, w s * g s := by
    dsimp [A]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hwg_integrable t0 T)
      (hwg_integrable T t)]
  have hWsplit : (∫ s in t0..t, w s) = (∫ s in t0..T, w s) + ∫ s in T..t, w s := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hw_integrable t0 T)
      (hw_integrable T t)]
  have htail : |∫ s in T..t, w s * g s| ≤ (eps / 2) * (∫ s in T..t, w s) := by
    calc
      |∫ s in T..t, w s * g s| ≤ ∫ s in T..t, |w s * g s| :=
        intervalIntegral.abs_integral_le_integral_abs htT
      _ ≤ ∫ s in T..t, w s * (eps / 2) := by
        apply intervalIntegral.integral_mono_on htT
          (hwg_integrable T t).abs
          ((hw_integrable T t).mul_const _)
        intro s hs
        rw [abs_mul, abs_of_nonneg (hw_nonneg s (le_trans (le_max_left _ _) hs.1))]
        exact mul_le_mul_of_nonneg_left (le_of_lt (hT1 s (le_trans (le_max_right _ _) hs.1)))
          (hw_nonneg s (le_trans (le_max_left _ _) hs.1))
      _ = (eps / 2) * ∫ s in T..t, w s := by
        rw [intervalIntegral.integral_mul_const]
        ring
  rw [dist_zero_right, Real.norm_eq_abs]
  rw [hsplit]
  rw [mul_add]
  calc
    |(∫ s in t0..t, w s)⁻¹ * A + (∫ s in t0..t, w s)⁻¹ * ∫ s in T..t, w s * g s| ≤
        |(∫ s in t0..t, w s)⁻¹ * A| + |(∫ s in t0..t, w s)⁻¹ * ∫ s in T..t, w s * g s| :=
      abs_add_le _ _
    _ < eps / 2 + eps / 2 := by
      apply add_lt_add_of_lt_of_le
      · rw [abs_mul, abs_inv, abs_of_pos hWpos]
        rw [← div_eq_inv_mul]
        apply (div_lt_iff₀ hWpos).2
        have hlarge' := (div_lt_iff₀ heps).1 hlarge
        nlinarith
      · rw [abs_mul, abs_inv, abs_of_pos hWpos]
        rw [← div_eq_inv_mul]
        have htotal : ∫ s in T..t, w s ≤ ∫ s in t0..t, w s := by
          rw [hWsplit]
          have hprefix : 0 ≤ ∫ s in t0..T, w s := by
            apply intervalIntegral.integral_nonneg (le_max_left _ _)
            intro s hs
            exact hw_nonneg s hs.1
          linarith
        apply (div_le_iff₀ hWpos).2
        exact htail.trans (mul_le_mul_of_nonneg_left htotal (by linarith))
    _ = eps := by ring

/-- Weak weighted Cesaro convergence. -/
theorem weak_weighted_cesaro_convergence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (v : ℝ → H) (vInfinity : H) (w : ℝ → ℝ) (t0 : ℝ)
    (hv : Tendsto (fun t => toWeakSpace ℝ H (v t)) atTop (nhds (toWeakSpace ℝ H vInfinity)))
    (hw_nonneg : ∀ t ≥ t0, 0 ≤ w t)
    (hw_integrable : ∀ a b, IntervalIntegrable w volume a b)
    (hwv_integrable : ∀ a b, IntervalIntegrable (fun s => w s • v s) volume a b)
    (hW : Tendsto (fun t => ∫ s in t0..t, w s) atTop atTop) :
    Tendsto (fun t => toWeakSpace ℝ H ((∫ s in t0..t, w s)⁻¹ • ∫ s in t0..t, w s • v s)) atTop
      (nhds (toWeakSpace ℝ H vInfinity)) := by
  apply (weakConvergence_iff_forall_tendsto_inner_right _ vInfinity).2
  intro u
  have hv_coord := (weakConvergence_iff_forall_tendsto_inner_right v vInfinity).1 hv u
  have hcentered : ∀ a b, IntervalIntegrable (fun s => w s • (v s - vInfinity)) volume a b := by
    intro a b
    have hconst : IntervalIntegrable (fun s => w s • vInfinity) volume a b :=
      ⟨(hw_integrable a b).1.smul_const vInfinity, (hw_integrable a b).2.smul_const vInfinity⟩
    convert (hwv_integrable a b).sub hconst using 1
    · ext s
      module
  have hscalar : ∀ a b,
      IntervalIntegrable (fun s => w s * inner ℝ (v s - vInfinity) u) volume a b := by
    intro a b
    have h := hcentered a b
    constructor
    · simpa [Function.comp_def, innerSL_apply_apply, real_inner_comm, real_inner_smul_left,
        real_inner_smul_right] using
        (innerSL ℝ u).integrableOn_comp h.1
    · simpa [Function.comp_def, innerSL_apply_apply, real_inner_comm, real_inner_smul_left,
        real_inner_smul_right] using
        (innerSL ℝ u).integrableOn_comp h.2
  have hcoord : Tendsto (fun t => inner ℝ (v t - vInfinity) u) atTop (nhds 0) := by
    simpa only [inner_sub_left, sub_self] using
      hv_coord.sub (tendsto_const_nhds : Tendsto (fun _ : ℝ => inner ℝ vInfinity u) atTop
        (nhds (inner ℝ vInfinity u)))
  have havg := weighted_cesaro_real_tendsto_zero w
    (fun s => inner ℝ (v s - vInfinity) u) t0 hcoord hw_nonneg hw_integrable hscalar hW
  have hnonzero : ∀ᶠ t in atTop, (∫ s in t0..t, w s) ≠ 0 := by
    filter_upwards [(Filter.tendsto_atTop.1 hW 1)] with t ht
    linarith
  have hident : ∀ᶠ t in atTop,
      inner ℝ ((∫ s in t0..t, w s)⁻¹ • ∫ s in t0..t, w s • v s) u =
        inner ℝ vInfinity u + (∫ s in t0..t, w s)⁻¹ *
          ∫ s in t0..t, w s * inner ℝ (v s - vInfinity) u := by
    filter_upwards [hnonzero] with t ht
    have hconst : IntervalIntegrable (fun s => w s • vInfinity) volume t0 t :=
      ⟨(hw_integrable t0 t).1.smul_const vInfinity,
        (hw_integrable t0 t).2.smul_const vInfinity⟩
    have hdecomp : (∫ s in t0..t, w s • v s) =
        (∫ s in t0..t, w s • vInfinity) + ∫ s in t0..t, w s • (v s - vInfinity) := by
      rw [← intervalIntegral.integral_add hconst (hcentered t0 t)]
      apply intervalIntegral.integral_congr
      intro s hs
      module
    have hinter : inner ℝ (∫ s in t0..t, w s • (v s - vInfinity)) u =
        ∫ s in t0..t, w s * inner ℝ (v s - vInfinity) u := by
      simpa [Function.comp_def, innerSL_apply_apply, real_inner_comm, real_inner_smul_left] using
        ((innerSL ℝ u).intervalIntegral_comp_comm (hcentered t0 t)).symm
    rw [hdecomp, intervalIntegral.integral_smul_const]
    simp only [smul_add, inner_add_left, real_inner_smul_left]
    rw [hinter]
    field_simp [ht]
  refine Tendsto.congr' ?_ (by simpa using tendsto_const_nhds.add havg)
  filter_upwards [hident] with t ht
  exact ht.symm
