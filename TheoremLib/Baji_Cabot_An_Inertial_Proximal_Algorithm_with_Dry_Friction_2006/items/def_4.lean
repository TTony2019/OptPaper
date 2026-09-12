import Mathlib
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.def_3

/-!
# Energy sequence $(E_n)$
When $B = \partial f$ for a convex function $f: H \to \mathbb{R} \cup \{+\infty\}$,
the energy-like sequence $(E_n)$ is defined by:
$$E_n = \frac{1}{2\lambda_n^2} |x_{n+1} - x_n|^2 + f(x_{n+1}).$$
-/
open Real
variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
/-- The energy sequence `E_n = (1/(2λ_n^2)) |x_{n+1} - x_n|^2 + f(x_{n+1})`. -/
noncomputable def energySeq (x : ℕ → H) (lam : ℕ → ℝ) (f : H → EReal) (n : ℕ) : EReal :=
  (((2 * (lam n)^2)⁻¹) * ‖x (n+1) - x n‖^2 : ℝ) + f (x (n+1))
