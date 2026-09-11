import Mathlib

/-- Predicate saying that a map is `L`-Lipschitz. -/
def HasLipschitzGradient {H : Type*} [PseudoMetricSpace H] [NormedAddCommGroup H]
    (g : H → H) (L : ℝ) : Prop := ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖

/-- A differentiable function whose `gradient` is Lipschitz continuous. -/
def HasLipschitzGradientOf {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (L : ℝ) : Prop :=
  Differentiable ℝ f ∧ (∀ x, fderiv ℝ f x = innerSL ℝ (gradient f x)) ∧
    HasLipschitzGradient (gradient f) L

/-- The mathlib `gradient` of a continuously differentiable function is its Fréchet
derivative, seen through the Riesz representation `innerSL`. -/
theorem hasFDerivAt_gradient {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (hf : ContDiff ℝ 1 f) (x : H) :
    HasFDerivAt f (innerSL ℝ (gradient f x)) x :=
  (hf.differentiable (by norm_num) x).hasGradientAt.hasFDerivAt

/-- Version of `hasFDerivAt_gradient` assuming only differentiability. -/
theorem hasFDerivAt_gradient_of_differentiable {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f : H → ℝ) (hf : Differentiable ℝ f) (x : H) :
    HasFDerivAt f (innerSL ℝ (gradient f x)) x :=
  (hf x).hasGradientAt.hasFDerivAt

/-- The `gradient` of a continuously differentiable function is continuous. -/
theorem continuous_gradient_of_contDiff {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {f : H → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (gradient f) := by
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  simpa [gradient, Function.comp_def] using
    (InnerProductSpace.toDual ℝ H).symm.continuous.comp hfd
