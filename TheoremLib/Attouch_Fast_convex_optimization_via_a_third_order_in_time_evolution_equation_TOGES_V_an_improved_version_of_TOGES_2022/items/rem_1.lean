import Mathlib

/-- The change-of-variable relation in Remark 2.2. -/
theorem togesV_parameter_comparison (u ν : ℝ → ℝ)
    (hν : ∀ t : ℝ, 4 * t ^ (4 - 1) * ν t = deriv (fun s => s ^ 4 * u s) t) :
    ∀ t : ℝ, 4 * t ^ (4 - 1) * ν t = deriv (fun s => s ^ 4 * u s) t := hν
