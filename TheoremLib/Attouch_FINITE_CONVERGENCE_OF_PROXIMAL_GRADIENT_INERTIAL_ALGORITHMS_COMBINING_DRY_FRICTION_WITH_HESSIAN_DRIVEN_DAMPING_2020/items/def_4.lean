import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.def_3
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_def_1
import Mathlib

open scoped InnerProductSpace

open ERealFunction

noncomputable section

/-- Squared norm induced by a linear metric operator `M`. -/
def metricNormSq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : H →L[ℝ] H) (x : H) : ℝ := @inner ℝ H _ (M x) x

/-- The objective whose minimizer is the proximal point of `x` in the metric induced by `M`.
This is the extended-real form of the objective in (5.2). -/
noncomputable def variableMetricProximalObjective {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) (M : H →L[ℝ] H) (lam : PosReal)
    (x : H) : H → EReal :=
  fun p ↦ f p + ((metricNormSq M (x - p) / (2 * (lam : ℝ)) : ℝ) : EReal)

/-- The set of proximal points of `x` in the metric induced by `M`. -/
def variableMetricProximalPoints {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) (M : H →L[ℝ] H) (lam : PosReal)
    (x : H) : Set H :=
  Argmin (variableMetricProximalObjective f M lam x)

/-- A variable-metric proximal objective has a unique minimizer at every base point. -/
def HasUniqueVariableMetricProxPoint {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) (M : H →L[ℝ] H) (lam : PosReal) : Prop :=
  ∀ x : H, ∃! p : H, p ∈ variableMetricProximalPoints f M lam x

/-- The variable-metric proximity operator, defined as the unique minimizer in (5.2). -/
noncomputable def variableMetricProximityOperator {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) (M : H →L[ℝ] H) (lam : PosReal)
    (hf : HasUniqueVariableMetricProxPoint f M lam) : H → H :=
  fun x ↦ (hf x).choose

/-- The variable-metric proximity operator realizes the minimum in (5.2). -/
theorem variableMetricProximityOperator_isProxPoint {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) (M : H →L[ℝ] H) (lam : PosReal)
    (hf : HasUniqueVariableMetricProxPoint f M lam) (x : H) :
    variableMetricProximityOperator f M lam hf x ∈
      variableMetricProximalPoints f M lam x :=
  (hf x).choose_spec.1

/-- The variable-metric Moreau envelope (5.2). -/
noncomputable def variableMetricMoreauEnvelope {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) (M : H →L[ℝ] H) (lam : PosReal) :
    H → EReal :=
  fun x ↦ ⨅ p : H, variableMetricProximalObjective f M lam x p

/-- The value of the variable-metric Moreau envelope is the infimum in (5.2). -/
theorem variableMetricMoreauEnvelope_apply {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) (M : H →L[ℝ] H) (lam : PosReal)
    (x : H) :
    variableMetricMoreauEnvelope f M lam x =
      ⨅ p : H, f p + ((metricNormSq M (x - p) / (2 * (lam : ℝ)) : ℝ) : EReal) := by
  rfl
