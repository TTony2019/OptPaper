import Mathlib
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.algo_1
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_5

namespace AttouchPeypouquetRedont2014

/-- IFB signal-recovery iteration (5.19). -/
def IsIFBSignalRecoveryTrajectory {n : Type*} [Fintype n] [DecidableEq n]
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    [InnerProductSpace ℝ K] (prox : (n → ℝ) → n → ℝ) (A : (n → ℝ) → K) (At : K → n → ℝ)
    (data : K) (a b lam γ : ℝ) (_hAt : ∀ x z, inner ℝ (A x) z = ∑ i, x i * (At z) i)
    (f : (n → ℝ) → EReal) (_hf : ∀ v, f v = ((lam * γ * ∑ i, |v i| : ℝ) : EReal))
    (hfproper : ERealFunction.IsProper f) (hflsc : IsClosed (ERealFunction.epigraph f))
    (hfconvex : Convex ℝ (ERealFunction.epigraph f))
    (_hprox : ∀ x, ERealFunction.IsProxPoint (ERealFunction.properIoi f hfproper) x (prox x))
    (u y : ℕ → n → ℝ) : Prop := ∀ k,
  u (k + 1) = prox ((1 - lam * a) • u k + (lam * b) • y k) ∧
  y (k + 1) = (1 / (1 + lam * b)) • y k + (lam * a / (1 + lam * b)) • u (k + 1) -
    (2 * lam / (1 + lam * b)) • At (A (u (k + 1)) - data)

end AttouchPeypouquetRedont2014
