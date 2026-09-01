import Mathlib
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_2
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.thm_3
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_3

namespace AttouchAdlyDryFrictionDynamics2023

private theorem frictionBall_not_mem_initial_infDist_pos
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {x : H} {r : ℝ} (hr : 0 ≤ r) (hx : r < ‖x‖) :
    0 < Metric.infDist x (frictionBall r) := by
  have hnotmem : x ∉ frictionBall r := by
    intro hmem
    have hle : ‖x‖ ≤ r := by
      simpa [frictionBall, dist_zero_right] using hmem
    exact (not_le_of_gt hx) hle
  have hnonempty : (frictionBall (H := H) r).Nonempty := by
    simpa [frictionBall] using
      (Metric.nonempty_closedBall.mpr hr : (Metric.closedBall (0 : H) r).Nonempty)
  have hclosed : IsClosed (frictionBall (H := H) r) := by
    simpa [frictionBall] using
      (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0 : H) r))
  exact (hclosed.notMem_iff_infDist_pos hnonempty).mp hnotmem

private theorem weighted_energy_antitone {E : ℝ → ℝ} {a : ℝ}
    (hE : ∀ t, HasDerivAt E (deriv E t) t)
    (hineq : ∀ t, deriv E t + a * E t ≤ 0) :
    Antitone (fun t => Real.exp (a * t) * E t) := by
  apply antitone_of_deriv_nonpos
  · intro t
    have hdiff := (((hasDerivAt_id t).const_mul a).exp).differentiableAt.mul
      (hE t).differentiableAt
    simpa only [Pi.mul_apply, id_eq] using hdiff
  · intro t
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (a * s))
        (Real.exp (a * t) * a) t := by
      simpa using (((hasDerivAt_id t).const_mul a).exp)
    have hformula : deriv (fun s : ℝ => Real.exp (a * s) * E s) t =
        Real.exp (a * t) * (deriv E t + a * E t) := by
      change deriv ((fun s : ℝ => Real.exp (a * s)) * E) t = _
      rw [(hexp.mul (hE t)).deriv]
      ring
    rw [hformula]
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) (hineq t)

private theorem weighted_energy_monotone {E : ℝ → ℝ} {a : ℝ}
    (hE : ∀ t, HasDerivAt E (deriv E t) t)
    (hineq : ∀ t, 0 ≤ deriv E t + a * E t) :
    Monotone (fun t => Real.exp (a * t) * E t) := by
  apply monotone_of_deriv_nonneg
  · intro t
    have hdiff := (((hasDerivAt_id t).const_mul a).exp).differentiableAt.mul
      (hE t).differentiableAt
    simpa only [Pi.mul_apply, id_eq] using hdiff
  · intro t
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (a * s))
        (Real.exp (a * t) * a) t := by
      simpa using (((hasDerivAt_id t).const_mul a).exp)
    have hderiv := hexp.mul (hE t)
    have hformula : deriv (fun s : ℝ => Real.exp (a * s) * E s) t =
        Real.exp (a * t) * (deriv E t + a * E t) := by
      change deriv ((fun s : ℝ => Real.exp (a * s)) * E) t = _
      rw [hderiv.deriv]
      ring
    rw [hformula]
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) (hineq t)

/-- Theorem 3.3: exponential upper and lower bounds for the quadratic case. -/
theorem theorem_3_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {t₀ r : ℝ} (hr : 0 < r) (A : H →L[ℝ] H) (g p : ℝ → H)
    (hsymm : A.IsSymmetric) (hpos : ∀ x ≠ 0, 0 < inner ℝ (A x) x)
    (hdualDrygrad : ∀ t, p t ∈ frictionBallProjector r (g t) ∧
      HasDerivAt g (A (p t - g t)) t)
    (hcoercive : ∃ μ ν : ℝ, 0 < μ ∧ 0 < ν ∧ ∀ ξ : H,
      μ * ‖ξ‖ ^ 2 ≤ inner ℝ (A ξ) ξ ∧ inner ℝ (A ξ) ξ ≤ ν * ‖ξ‖ ^ 2)
    (henergyDeriv : ∀ t : ℝ, HasDerivAt
      (fun s => Metric.infDist (g s) (frictionBall r) ^ 2 / 2)
      (- inner ℝ (g t - p t) (A (g t - p t))) t)
    (hinitial : r < ‖g t₀‖) :
    ∃ Cupper Clower μ ν : ℝ, 0 < Cupper ∧ 0 < Clower ∧ 0 < μ ∧ 0 < ν ∧
      (∀ t ∈ Set.Ici t₀, Metric.infDist (g t) (frictionBall r) ≤ Cupper * Real.exp (-μ * t)) ∧
      (∀ t ∈ Set.Ici t₀, Clower * Real.exp (-ν * t) ≤ Metric.infDist (g t) (frictionBall r)) ∧
      ∀ t ∈ Set.Ici t₀, g t ∉ frictionBall r := by
  rcases hcoercive with ⟨μ, ν, hμ, hν, hquad⟩
  let E : ℝ → ℝ := fun t => Metric.infDist (g t) (frictionBall r) ^ 2 / 2
  have hd0 : 0 < Metric.infDist (g t₀) (frictionBall r) :=
    frictionBall_not_mem_initial_infDist_pos (le_of_lt hr) hinitial
  have hEderiv : ∀ t, HasDerivAt E
      (- inner ℝ (g t - p t) (A (g t - p t))) t := by
    intro t
    simpa [E] using henergyDeriv t
  have hupperDiff : ∀ t, deriv E t + 2 * μ * E t ≤ 0 := by
    intro t
    have hq := (hquad (g t - p t)).1
    have hdist := (hdualDrygrad t).1.2
    have hnorm : ‖g t - p t‖ = Metric.infDist (g t) (frictionBall r) := by
      simpa [dist_eq_norm] using hdist
    rw [hnorm] at hq
    rw [(hEderiv t).deriv]
    rw [real_inner_comm (A (g t - p t)) (g t - p t)]
    dsimp [E]
    nlinarith
  have hlowerDiff : ∀ t, 0 ≤ deriv E t + 2 * ν * E t := by
    intro t
    have hq := (hquad (g t - p t)).2
    have hdist := (hdualDrygrad t).1.2
    have hnorm : ‖g t - p t‖ = Metric.infDist (g t) (frictionBall r) := by
      simpa [dist_eq_norm] using hdist
    rw [hnorm] at hq
    rw [(hEderiv t).deriv]
    rw [real_inner_comm (A (g t - p t)) (g t - p t)]
    dsimp [E]
    nlinarith
  have hEderiv' : ∀ t, HasDerivAt E (deriv E t) t := by
    intro t
    convert hEderiv t using 1
    exact (hEderiv t).deriv
  have hlowerDistance : ∀ t ∈ Set.Ici t₀,
      Metric.infDist (g t₀) (frictionBall r) * Real.exp (-ν * (t - t₀)) ≤
        Metric.infDist (g t) (frictionBall r) := by
    intro t ht
    have henergy : E t₀ * Real.exp (-(2 * ν) * (t - t₀)) ≤ E t := by
      have hdiv : (Real.exp (2 * ν * t₀) * E t₀) / Real.exp (2 * ν * t) ≤ E t :=
        (div_le_iff₀ (Real.exp_pos _)).mpr
          (by simpa [mul_comm] using weighted_energy_monotone hEderiv' hlowerDiff ht)
      calc
        E t₀ * Real.exp (-(2 * ν) * (t - t₀)) =
            E t₀ * (Real.exp (2 * ν * t₀) / Real.exp (2 * ν * t)) := by
              rw [← Real.exp_sub]
              congr 2 <;> ring
        _ = (Real.exp (2 * ν * t₀) * E t₀) / Real.exp (2 * ν * t) := by ring
        _ ≤ E t := hdiv
    have hsq : Metric.infDist (g t₀) (frictionBall r) ^ 2 *
        Real.exp (-(2 * ν) * (t - t₀)) ≤ Metric.infDist (g t) (frictionBall r) ^ 2 := by
      dsimp [E] at henergy
      nlinarith
    have hident : (Metric.infDist (g t₀) (frictionBall r) *
        Real.exp (-ν * (t - t₀))) ^ 2 =
        Metric.infDist (g t₀) (frictionBall r) ^ 2 * Real.exp (-(2 * ν) * (t - t₀)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2 <;> ring
    exact (sq_le_sq₀ (mul_nonneg Metric.infDist_nonneg (le_of_lt (Real.exp_pos _)))
      Metric.infDist_nonneg).mp (by rwa [hident])
  refine ⟨Metric.infDist (g t₀) (frictionBall r) * Real.exp (μ * t₀),
    Metric.infDist (g t₀) (frictionBall r) * Real.exp (ν * t₀), μ, ν,
    mul_pos hd0 (Real.exp_pos _), mul_pos hd0 (Real.exp_pos _), hμ, hν, ?_, ?_, ?_⟩
  · intro t ht
    have henergy : E t ≤ E t₀ * Real.exp (-(2 * μ) * (t - t₀)) := by
      have hdiv : E t ≤ (Real.exp (2 * μ * t₀) * E t₀) / Real.exp (2 * μ * t) :=
        (le_div_iff₀ (Real.exp_pos _)).mpr
          (by simpa [mul_comm] using weighted_energy_antitone hEderiv' hupperDiff ht)
      calc
        E t ≤ (Real.exp (2 * μ * t₀) * E t₀) / Real.exp (2 * μ * t) := hdiv
        _ = E t₀ * (Real.exp (2 * μ * t₀) / Real.exp (2 * μ * t)) := by ring
        _ = E t₀ * Real.exp (2 * μ * t₀ - 2 * μ * t) := by rw [Real.exp_sub]
        _ = E t₀ * Real.exp (-(2 * μ) * (t - t₀)) := by congr 2 <;> ring
    have hsq : Metric.infDist (g t) (frictionBall r) ^ 2 ≤
        Metric.infDist (g t₀) (frictionBall r) ^ 2 * Real.exp (-(2 * μ) * (t - t₀)) := by
      dsimp [E] at henergy
      nlinarith
    have hident : (Metric.infDist (g t₀) (frictionBall r) *
        Real.exp (-μ * (t - t₀))) ^ 2 =
        Metric.infDist (g t₀) (frictionBall r) ^ 2 * Real.exp (-(2 * μ) * (t - t₀)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2 <;> ring
    have hdist : Metric.infDist (g t) (frictionBall r) ≤
        Metric.infDist (g t₀) (frictionBall r) * Real.exp (-μ * (t - t₀)) :=
      (sq_le_sq₀ Metric.infDist_nonneg (mul_nonneg Metric.infDist_nonneg (le_of_lt (Real.exp_pos _)))).mp
        (by rwa [hident])
    convert hdist using 1
    calc
      Metric.infDist (g t₀) (frictionBall r) * Real.exp (μ * t₀) * Real.exp (-μ * t) =
          Metric.infDist (g t₀) (frictionBall r) * (Real.exp (μ * t₀) * Real.exp (-μ * t)) := by ring
      _ = Metric.infDist (g t₀) (frictionBall r) * Real.exp (μ * t₀ + -μ * t) := by rw [← Real.exp_add]
      _ = Metric.infDist (g t₀) (frictionBall r) * Real.exp (-μ * (t - t₀)) := by congr 2 <;> ring
  · intro t ht
    have hdist := hlowerDistance t ht
    convert hdist using 1
    calc
      Metric.infDist (g t₀) (frictionBall r) * Real.exp (ν * t₀) * Real.exp (-ν * t) =
          Metric.infDist (g t₀) (frictionBall r) * (Real.exp (ν * t₀) * Real.exp (-ν * t)) := by ring
      _ = Metric.infDist (g t₀) (frictionBall r) * Real.exp (ν * t₀ + -ν * t) := by rw [← Real.exp_add]
      _ = Metric.infDist (g t₀) (frictionBall r) * Real.exp (-ν * (t - t₀)) := by congr 2 <;> ring
  · intro t ht hmem
    have hlower := hlowerDistance t ht
    have hposdist : 0 < Metric.infDist (g t) (frictionBall r) :=
      lt_of_lt_of_le (mul_pos hd0 (Real.exp_pos _)) hlower
    have hzero := Metric.infDist_zero_of_mem hmem
    linarith

end AttouchAdlyDryFrictionDynamics2023
