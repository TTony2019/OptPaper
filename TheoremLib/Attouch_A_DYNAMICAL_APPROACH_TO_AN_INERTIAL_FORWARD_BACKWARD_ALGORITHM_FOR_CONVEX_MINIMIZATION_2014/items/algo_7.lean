import Mathlib
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_5

namespace AttouchPeypouquetRedont2014

/-- ISTA update (5.18). -/
def IsISTATrajectory {n : Type*} [Fintype n] [DecidableEq n]
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    [InnerProductSpace ℝ K] (prox : (n → ℝ) → n → ℝ) (A : (n → ℝ) → K) (At : K → n → ℝ)
    (data : K) (lam γ : ℝ) (_hAt : ∀ x z, inner ℝ (A x) z = ∑ i, x i * (At z) i)
    (f : (n → ℝ) → EReal) (_hf : ∀ v, f v = ((lam * γ * ∑ i, |v i| : ℝ) : EReal))
    (hfproper : ERealFunction.IsProper f) (hflsc : IsClosed (ERealFunction.epigraph f))
    (hfconvex : Convex ℝ (ERealFunction.epigraph f))
    (_hprox : ∀ x, ERealFunction.IsProxPoint (ERealFunction.properIoi f hfproper) x (prox x))
    (u : ℕ → n → ℝ) : Prop :=
  ∀ k, u (k + 1) = prox (u k - (2 * lam) • At (A (u k) - data))

end AttouchPeypouquetRedont2014
