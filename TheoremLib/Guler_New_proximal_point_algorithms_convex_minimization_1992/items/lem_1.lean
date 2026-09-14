import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_3
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_2
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_thm_1

open scoped InnerProductSpace

open ERealFunction

/-- Lemma 2.1: every estimate quadratic satisfies the one-step lower-model inequality. -/
theorem estimateQuadratic_step_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (A : ℝ) (x0 : H) (α lam : ℕ → ℝ) (y p : ℕ → H)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hα : ∀ i, α i ∈ Set.Ico (0 : ℝ) 1)
    (hp : ∀ k, p k ∈ proximalPoints f (lam k) (y k)) (k : ℕ) (x : H) :
    estimateQuadratic f A x0 α lam y p (k + 1) x - f x ≤
      (1 - α k) * (estimateQuadratic f A x0 α lam y p k x - f x) := by
  have hpk := hp k
  change 0 < lam k ∧
    IsMinOn (fun z => f z + ‖z - y k‖ ^ 2 / (2 * lam k)) Set.univ (p k) at hpk
  rcases hpk with ⟨hlam, hmin⟩
  have hsub : (1 / lam k) • (y k - p k) ∈
      subdifferential (fun y => (f y : EReal)) (p k) :=
    proximal_optimality_condition f hlam hconvex hmin
  rw [mem_convexSubdifferential_iff] at hsub
  have hmodel : f (p k) +
      inner ℝ ((1 / lam k) • (y k - p k)) (x - p k) ≤ f x :=
    hsub x
  have hα0 : 0 ≤ α k := (hα k).1
  change
    ((1 - α k) * estimateQuadratic f A x0 α lam y p k x +
      α k * (f (p k) +
        inner ℝ ((1 / lam k) • (y k - p k)) (x - p k))) - f x ≤
      (1 - α k) * (estimateQuadratic f A x0 α lam y p k x - f x)
  calc
    (1 - α k) * estimateQuadratic f A x0 α lam y p k x +
          α k * (f (p k) +
            inner ℝ ((1 / lam k) • (y k - p k)) (x - p k)) - f x =
        (1 - α k) * (estimateQuadratic f A x0 α lam y p k x - f x) +
          α k * ((f (p k) +
            inner ℝ ((1 / lam k) • (y k - p k)) (x - p k)) - f x) := by ring
    _ ≤ (1 - α k) * (estimateQuadratic f A x0 α lam y p k x - f x) := by
      have herror : (f (p k) +
          inner ℝ ((1 / lam k) • (y k - p k)) (x - p k)) - f x ≤ 0 :=
        sub_nonpos.mpr hmodel
      have hweighted : α k * ((f (p k) +
          inner ℝ ((1 / lam k) • (y k - p k)) (x - p k)) - f x) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hα0 herror
      linarith
