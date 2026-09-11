import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.def_3
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_def_1
import Mathlib

open scoped InnerProductSpace

open ERealFunction

noncomputable section

/-- Squared norm induced by a linear metric operator `M`. -/
def metricNormSq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : H →L[ℝ] H) (x : H) : ℝ := @inner ℝ H _ (M x) x

/-- The variable-metric Moreau envelope, expressed using an infimum. -/
def variableMetricMoreauEnvelope {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (M : H →L[ℝ] H)
    (hM_symm : ∀ x y, @inner ℝ H _ (M x) y = @inner ℝ H _ x (M y))
    (hM_pos : ∀ x, x ≠ 0 → 0 < metricNormSq M x) (lam : ℝ) (hlam : 0 < lam) (x : H) : ℝ :=
  let _ := hM_symm
  let _ := hM_pos
  let _ := hlam
  sInf (Set.range fun xi ↦ f xi + metricNormSq M (x - xi) / (2 * lam))

/-- All data and identities in the variable-metric Moreau construction (5.2)--(5.5). -/
structure VariableMetricMoreauData {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (M : H →L[ℝ] H) (lam : ℝ) (hlam : 0 < lam) where
  symmetric : ∀ x y, @inner ℝ H _ (M x) y = @inner ℝ H _ x (M y)
  positive_definite : ∀ x, x ≠ 0 → 0 < metricNormSq M x
  envelope : H → ℝ
  prox : H → H
  envelope_eq (x : H) : envelope x = variableMetricMoreauEnvelope f M symmetric positive_definite lam hlam x
  prox_minimizes (x xi : H) : f (prox x) + metricNormSq M (x - prox x) / (2 * lam) ≤
    f xi + metricNormSq M (x - xi) / (2 * lam)
  prox_unique (x p : H) :
    f p + metricNormSq M (x - p) / (2 * lam) = envelope x → p = prox x
  optimality (x : H) : M (x - prox x) ∈ (fun u ↦ lam • u) '' subdifferential f (prox x)
  gradient : H → H
  gradient_eq (x : H) : gradient x = (1 / lam) • M (x - prox x)
  muMin : ℝ
  muMax : ℝ
  muMin_pos : 0 < muMin
  muMin_isLeast : ∀ μ : ℝ, (∃ v : H, v ≠ 0 ∧ M v = μ • v) → muMin ≤ μ
  muMin_isEigenvalue : ∃ v : H, v ≠ 0 ∧ M v = muMin • v
  muMax_isGreatest : ∀ μ : ℝ, (∃ v : H, v ≠ 0 ∧ M v = μ • v) → μ ≤ muMax
  muMax_isEigenvalue : ∃ v : H, v ≠ 0 ∧ M v = muMax • v
  prox_lipschitz : ∀ x y,
    ‖prox x - prox y‖ ≤ (muMax / muMin) * ‖x - y‖
  gradient_lipschitz : ∀ x y,
    ‖gradient x - gradient y‖ ≤ (1 / lam) * Real.sqrt (muMax / muMin) * ‖x - y‖
  minimizers : ∀ x, (envelope x = sInf (Set.range f)) ↔ (f x = sInf (Set.range f))
