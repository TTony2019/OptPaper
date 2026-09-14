import Mathlib
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.thm_3

/-!
# Remark 5.2
Estimate (28) of the discrete velocity $|x_{n+1} - x_n|$ allows to evaluate
the distance of the iterate $x_n$ to the limit $x_\infty$. More precisely,
we immediately deduce from inequality (28) that
$$\forall n \geqslant n_0, \quad |x_n - x_\infty| \leqslant \frac{K}{1 - q} q^n.$$
-/
open Set
open Filter
open scoped Topology

variable {H : Type _} [NormedAddCommGroup H]

/-- Finite geometric tail bound obtained by telescoping the iterate differences. -/
private theorem rem52_finite_tail_bound (x : ℕ → H) (n0 n m : ℕ)
    (K q : ℝ) (hK_nonneg : 0 ≤ K) (hq_nonneg : 0 ≤ q) (hq1 : q < 1)
    (h_vel_decay : ∀ i ≥ n0, ‖x (i + 1) - x i‖ ≤ K * q ^ i)
    (hn : n0 ≤ n) (hmn : n ≤ m) :
    ‖x n - x m‖ ≤ (K / (1 - q)) * q ^ n := by
  calc
    ‖x n - x m‖ = dist (x n) (x m) := (dist_eq_norm (x n) (x m)).symm
    _ ≤ ∑ i ∈ Finset.Ico n m, dist (x i) (x (i + 1)) :=
      dist_le_Ico_sum_dist x hmn
    _ = ∑ i ∈ Finset.Ico n m, ‖x i - x (i + 1)‖ :=
      Finset.sum_congr rfl fun i _ => dist_eq_norm (x i) (x (i + 1))
    _ = ∑ i ∈ Finset.Ico n m, ‖x (i + 1) - x i‖ := by
      exact Finset.sum_congr rfl fun i _ => norm_sub_rev (x i) (x (i + 1))
    _ ≤ ∑ i ∈ Finset.Ico n m, K * q ^ i := by
      exact Finset.sum_le_sum fun i hi => h_vel_decay i (le_trans hn (Finset.mem_Ico.mp hi).1)
    _ = K * ∑ i ∈ Finset.Ico n m, q ^ i := by
      rw [Finset.mul_sum]
    _ ≤ K * (q ^ n / (1 - q)) :=
      mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hq_nonneg hq1) hK_nonneg
    _ = (K / (1 - q)) * q ^ n := by ring

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Remark 5.2: from the geometric decay of velocity to the geometric decay of distance. -/
theorem rem_5_2 (x : ℕ → H) (xInf : H) (n0 : ℕ) (K : ℝ) (q : ℝ) (hK : K > 0) (hq0 : q > 0)
    (hq1 : q < 1) (h_vel_decay : ∀ n ≥ n0, ‖x (n + 1) - x n‖ ≤ K * q ^ n)
    (hxInf : Tendsto x atTop (𝓝 xInf)) :
    ∀ n ≥ n0, ‖x n - xInf‖ ≤ (K / (1 - q)) * q ^ n := by
  intro n hn
  have hK_nonneg : 0 ≤ K := le_of_lt hK
  have hq_nonneg : 0 ≤ q := le_of_lt hq0
  let R : ℝ := (K / (1 - q)) * q ^ n
  have h_eventual : (fun m : ℕ => ‖x n - x m‖) ≤ᶠ[atTop] (fun _ : ℕ => R) := by
    change ∀ᶠ m : ℕ in atTop, ‖x n - x m‖ ≤ R
    rw [Filter.eventually_atTop]
    exact ⟨n, fun m hm =>
      rem52_finite_tail_bound x n0 n m K q hK_nonneg hq_nonneg hq1 h_vel_decay hn hm⟩
  have hcont : Continuous (fun y : H => ‖x n - y‖) :=
    (continuous_const.sub continuous_id).norm
  have h_tend : Tendsto (fun m : ℕ => ‖x n - x m‖) atTop (𝓝 ‖x n - xInf‖) := by
    exact (hcont.tendsto xInf).comp hxInf
  simpa [R] using le_of_tendsto_of_tendsto h_tend tendsto_const_nhds h_eventual
