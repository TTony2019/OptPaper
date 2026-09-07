import Mathlib
namespace Alvarez2002
/-- Finite-dimensional real analyticity, expressed with Mathlib's local power-series predicate. -/
def IsRealAnalyticOn {N : Type*} [Fintype N] (Ω : Set (EuclideanSpace ℝ N))
    (Φ : EuclideanSpace ℝ N → ℝ) : Prop :=
  IsOpen Ω ∧ AnalyticOnNhd ℝ Φ Ω
end Alvarez2002
