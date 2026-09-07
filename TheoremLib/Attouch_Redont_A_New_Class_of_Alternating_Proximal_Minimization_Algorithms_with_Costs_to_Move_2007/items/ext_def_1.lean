import Mathlib

/-!
# Resolvent (Proximal) Operator

For a convex, proper, lower semicontinuous function φ : H → ℝ ∪ {+∞} on a Hilbert space H
and a parameter λ > 0, the resolvent (proximal) operator is defined by

  J_λ^{∂φ}(x) = (I + λ ∂φ)⁻¹(x) = argmin_{ξ∈H} {φ(ξ) + ‖ξ - x‖² / (2λ)}.

In this paper, the notation T_f^n = (I + 1/(α_n+β) ∂f)⁻¹ and
T_g^n = (I + 1/(μ+ν_n) ∂g)⁻¹ is used.

From: H. Attouch, P. Redont, A. Soubeyran (2007).
-/

open Set
open Real

/-- The resolvent (proximal) operator J_λ^{∂φ} of a function φ at point x with parameter λ.
J_λ^{∂φ}(x) = argmin_{ξ∈H} {φ(ξ) + ‖ξ - x‖²/(2λ)}.

When φ is convex, proper, and lower semicontinuous on a Hilbert space and λ > 0,
the argmin exists and is unique — the operator is well-defined and single-valued.

The existence of the minimizer is proved under the convexity/lsc/properness hypotheses
using the Moreau-Yosida theorem (see Bauschke & Combettes, Theorem 23.46). -/
noncomputable def resolventOperator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : H → ℝ) (lam : ℝ) (x : H) : H :=
  Classical.epsilon (λ p => ∀ ξ : H, φ p + (1 / (2 * lam)) * ‖p - x‖ ^ 2 ≤ φ ξ + (1 / (2 * lam)) * ‖ξ - x‖ ^ 2)

/-- Notation from the paper (Section 4): T_f^n = (I + 1/(α_n+β) ∂f)⁻¹.
This is the resolvent operator of f with parameter 1/(α_n+β).
Appears in the Hilbert space quadratic case where f is convex, lsc, proper
and α_n+β > 0. -/
noncomputable def T_n_f {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (α_n β : ℝ) (x : H) : H :=
  resolventOperator f (1 / (α_n + β)) x

/-- Notation from the paper (Section 4): T_g^n = (I + 1/(μ+ν_n) ∂g)⁻¹.
This is the resolvent operator of g with parameter 1/(μ+ν_n). -/
noncomputable def T_n_g {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : H → ℝ) (μ ν_n : ℝ) (x : H) : H :=
  resolventOperator g (1 / (μ + ν_n)) x
