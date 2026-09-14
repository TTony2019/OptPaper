import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_2
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_1

open scoped InnerProductSpace

/-- The estimate quadratics `varphi_k` defined by (2.7). -/
noncomputable def estimateQuadratic {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (A : ℝ) (x0 : H) (α lam : ℕ → ℝ) (y p : ℕ → H) : ℕ → H → ℝ
  | 0 => fun x => f x0 + (A / 2) * ‖x - x0‖ ^ 2
  | k + 1 => fun x => (1 - α k) * estimateQuadratic f A x0 α lam y p k x + α k *
    (f (p k) + inner ℝ ((1 / lam k) • (y k - p k)) (x - p k))

/-- The standing conditions accompanying (2.7). -/
def EstimateQuadraticStandingConditions {H : Type*} [NormedAddCommGroup H]
    (f : H → ℝ) (A : ℝ) (x0 : H) (α lam : ℕ → ℝ) (y p : ℕ → H) : Prop :=
  0 < A ∧ (∀ k, 0 < lam k) ∧ (∀ k, α k ∈ Set.Ico (0 : ℝ) 1) ∧
    IsFeasible (fun z => (f z : EReal)) x0 ∧
    ∀ k, p k ∈ proximalPoints f (lam k) (y k)
