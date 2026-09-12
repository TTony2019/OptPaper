import Mathlib
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.def_4

/-!
# Second energy sequence $(F_n)$
The second energy-like sequence $(F_n)$ is defined by:
$$F_n = E_n - f(x_\infty) - \langle \nabla f(x_\infty), x_{n+1} - x_\infty \rangle,$$
where $x_\infty = s-\lim_{n \to +\infty} x_n$ and $(E_n)$ is the energy sequence
defined in (2).
-/
variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
/-- The second energy-like sequence: `F_n = E_n - f(x∞) - ⟨∇f(x∞), x_{n+1} - x∞⟩`,
where `x∞` is the strong limit of the sequence `x` and `E_n` is the energy sequence. -/
noncomputable def secondEnergySeq (x : ℕ → H) (lam : ℕ → ℝ) (f : H → ℝ) (xInf : H) (n : ℕ) : ℝ :=
  (energySeq x lam (fun y => (f y : EReal)) n).toReal - f xInf -
    inner ℝ (gradient f xInf) (x (n+1) - xInf)
