import Mathlib

private theorem scalar_differential_weighted_integrable (b : ℝ → ℝ) (t0 t a : ℝ)
    (_ht : t0 ≤ t) (hb : IntervalIntegrable b MeasureTheory.volume t0 t) :
    IntervalIntegrable (fun s => Real.exp (a * (s - t0)) * b s)
      MeasureTheory.volume t0 t := by
  exact hb.continuousOn_mul (Real.continuous_exp.comp
    (continuous_const.mul (continuous_id.sub continuous_const)) |>.continuousOn
  )

private theorem scalar_differential_kernel_identity (t0 t a s : ℝ) :
    Real.exp (-a * (t - t0)) * Real.exp (a * (s - t0)) =
      Real.exp (-a * (t - s)) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- Scalar differential comparison by integrating factors. -/
theorem scalar_differential_comparison (E b : ℝ → ℝ) (t0 a : ℝ)
    (ha : 0 ≤ a)
    (hIntegrable : ∀ t ≥ t0, IntervalIntegrable b MeasureTheory.volume t0 t)
    (hDifferentiable : ∀ t ≥ t0, HasDerivAt E (deriv E t) t)
    (h : ∀ t ≥ t0, deriv E t + a * E t ≤ b t) :
    ∀ t ≥ t0, E t ≤ Real.exp (-a * (t - t0)) * E t0 +
      ∫ s in t0..t, Real.exp (-a * (t - s)) * b s := by
  intro t ht
  rcases ht.eq_or_lt with rfl | htlt
  · simp
  let w : ℝ → ℝ := fun s => Real.exp (a * (s - t0))
  let q : ℝ → ℝ := fun s => w s * E s
  let φ : ℝ → ℝ := fun s => w s * b s
  have hw_cont : Continuous w := by
    exact Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.sub continuous_const))
  have hE_cont : ContinuousOn E (Set.Icc t0 t) := by
    intro s hs
    exact (hDifferentiable s hs.1).continuousAt.continuousWithinAt
  have hq_cont : ContinuousOn q (Set.Icc t0 t) :=
    hw_cont.continuousOn.mul hE_cont
  have hφ_interval : IntervalIntegrable φ MeasureTheory.volume t0 t := by
    exact scalar_differential_weighted_integrable b t0 t a htlt.le (hIntegrable t htlt.le)
  have hφ_int : MeasureTheory.IntegrableOn φ (Set.Icc t0 t) MeasureTheory.volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le htlt.le).mp hφ_interval
  have hq_deriv : ∀ s ∈ Set.Ioo t0 t,
      HasDerivWithinAt q (w s * (deriv E s + a * E s)) (Set.Ioi s) s := by
    intro s hs
    have hlin : HasDerivAt (fun u : ℝ => a * (u - t0)) a s := by
      convert ((hasDerivAt_id s).sub_const t0).const_mul a using 1 <;> ring
    have hw_deriv : HasDerivAt w (w s * a) s := by
      exact (Real.hasDerivAt_exp (a * (s - t0))).comp s hlin
    have hprod := hw_deriv.mul (hDifferentiable s hs.1.le)
    convert hprod.hasDerivWithinAt using 1 <;> dsimp [q, w] <;> ring
  have hneg_deriv : ∀ s ∈ Set.Ioo t0 t,
      HasDerivWithinAt (fun u => -q u) (-(w s * (deriv E s + a * E s))) (Set.Ioi s) s := by
    intro s hs
    convert (hq_deriv s hs).neg using 1
  have hneg_le : ∀ s ∈ Set.Ioo t0 t,
      -(w s * b s) ≤ -(w s * (deriv E s + a * E s)) := by
    intro s hs
    have hbase := h s hs.1.le
    have hmul : w s * (deriv E s + a * E s) ≤ w s * b s :=
      mul_le_mul_of_nonneg_left hbase (show 0 ≤ w s from Real.exp_nonneg _)
    linarith
  have hcmp := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le
    (g := fun u => -q u)
    (g' := fun u => -(w u * (deriv E u + a * E u)))
    (φ := fun u => -(w u * b u)) htlt.le hq_cont.neg hneg_deriv hφ_int.neg hneg_le
  have hweighted : w t * E t ≤ E t0 + ∫ s in t0..t, w s * b s := by
    change (∫ y in t0..t, -(w y * b y)) ≤ -q t - -q t0 at hcmp
    rw [intervalIntegral.integral_neg] at hcmp
    dsimp [q] at hcmp
    dsimp [w] at hcmp ⊢
    simp only [sub_self, mul_zero, Real.exp_zero, one_mul] at hcmp
    linarith
  have hcancel := mul_le_mul_of_nonneg_left hweighted (Real.exp_nonneg (-a * (t - t0)))
  have hresult : E t ≤ Real.exp (-a * (t - t0)) * E t0 +
      Real.exp (-a * (t - t0)) * ∫ s in t0..t, w s * b s := by
    dsimp [w] at hcancel
    have hprod : Real.exp (-a * (t - t0)) * Real.exp (a * (t - t0)) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1 <;> ring
    rw [mul_add, ← mul_assoc, hprod, one_mul] at hcancel
    exact hcancel
  have hkernel : Real.exp (-a * (t - t0)) * ∫ s in t0..t, w s * b s =
      ∫ s in t0..t, Real.exp (-a * (t - s)) * b s := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp [w]
    rw [← mul_assoc, scalar_differential_kernel_identity]
  linarith
