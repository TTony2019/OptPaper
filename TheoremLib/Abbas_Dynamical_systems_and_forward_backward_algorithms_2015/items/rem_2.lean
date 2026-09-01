import Mathlib

namespace AbbasDynamical2015

/-- Remark 2.2: `Gamma` is the Bregman distance of `x` from `z` for the stated potential. -/
theorem bregman_distance_remark {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Phi : H → ℝ) (mu : ℝ) (x : ℝ → H) (z : H) (v : ℝ → H) (Gamma : ℝ → ℝ)
    (hGamma : ∀ t, Gamma t = (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 +
      mu * (Phi z - Phi (x t) - inner ℝ (z - x t) (v t)))
    (hdecreasing : Antitone Gamma) :
    (∀ t, Gamma t = (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 +
      mu * (Phi z - Phi (x t) - inner ℝ (z - x t) (v t))) ∧ Antitone Gamma := by
  exact ⟨hGamma, hdecreasing⟩

end AbbasDynamical2015
