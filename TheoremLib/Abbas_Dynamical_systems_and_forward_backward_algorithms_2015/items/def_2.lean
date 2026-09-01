import Mathlib

namespace AbbasDynamical2015

/-- The Bregman gap `g_z(t)`. -/
def bregmanGap {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Phi : H → ℝ) (x v : ℝ → H) (z : H) (t : ℝ) : ℝ :=
  Phi z - (Phi (x t) + inner ℝ (z - x t) (v t))

/-- The Lyapunov function `Gamma_z(t)`. -/
noncomputable def lyapunovGamma {H : Type*} [NormedAddCommGroup H]
    (x : ℝ → H) (mu : ℝ) (g : ℝ → ℝ) (z : H) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 + mu * g t

end AbbasDynamical2015
