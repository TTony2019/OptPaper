import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_2
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_3
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.lem_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_6

open scoped InnerProductSpace

open ERealFunction

/-- Theorem 2.1, the lower bound for the next estimate-quadratic minimum. -/
theorem estimateQuadratic_minimum_lower_bound {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (params : EstimateQuadraticParameters)
    (k : ℕ) (x : H) (hconvex : ConvexOn ℝ Set.univ f)
    (hlam : 0 < params.lam k) (hα : params.alpha k ∈ Set.Ico (0 : ℝ) 1)
    (hA : 0 < params.curvature (k + 1)) (hx : f x ≤ params.phi_star k)
    (hp : params.p k ∈ proximalPoints f (params.lam k) (params.y k))
    (hupdate : ∀ z, params.phi (k + 1) z =
      (1 - params.alpha k) * params.phi k z + params.alpha k *
        (f (params.p k) + inner ℝ ((1 / params.lam k) •
          (params.y k - params.p k)) (z - params.p k))) :
    params.phi_star (k + 1) ≥ f (params.p k) +
      (1 / (2 * params.lam k)) *
        (2 - params.alpha k ^ 2 /
          (params.curvature (k + 1) * params.lam k)) *
        ‖params.y k - params.p k‖ ^ 2 +
      (1 / params.lam k) * inner ℝ (params.y k - params.p k)
        ((1 - params.alpha k) • x + params.alpha k • params.nu k - params.y k) := by
  let a := params.alpha k
  let lam := params.lam k
  let A := params.curvature (k + 1)
  let p := params.p k
  let y := params.y k
  let ν := params.nu k
  let ν' := params.nu (k + 1)
  let q := y - p
  have hsupport : f p + (1 / lam) * inner ℝ q (x - p) ≤ f x := by
    rcases hp with ⟨_, hpmin⟩
    have hs := proximal_optimality_condition f hlam hconvex hpmin
    rw [mem_convexSubdifferential_iff] at hs
    specialize hs x
    simpa [p, y, q, lam, inner_smul_left, smul_eq_mul] using hs
  have hprox : f p + (1 / lam) * inner ℝ q (x - p) ≤ params.phi_star k :=
    hsupport.trans hx
  have hstar : params.phi_star (k + 1) = params.phi (k + 1) ν' := by
    rw [params.quadratic_representation]
    simp [ν']
  have h14 : params.phi_star (k + 1) =
      (1 - a) * params.phi_star k + A / 2 * ‖ν' - ν‖ ^ 2 + a * f p +
        (a / lam) * inner ℝ q (ν' - p) := by
    calc
      params.phi_star (k + 1) =
          (1 - a) * (params.phi_star k + params.curvature k / 2 * ‖ν' - ν‖ ^ 2) +
            a * (f p + (1 / lam) * inner ℝ q (ν' - p)) := by
              rw [hstar, hupdate, params.quadratic_representation]
              simp only [inner_smul_left]
              simp [a, p, y, ν, ν', q, lam]
      _ = (1 - a) * params.phi_star k +
          ((1 - a) * params.curvature k) / 2 * ‖ν' - ν‖ ^ 2 + a * f p +
            (a / lam) * inner ℝ q (ν' - p) := by ring
      _ = (1 - a) * params.phi_star k + A / 2 * ‖ν' - ν‖ ^ 2 + a * f p +
            (a / lam) * inner ℝ q (ν' - p) := by
              rw [← params.curvature_succ k]
  have hweight : (1 - a) * (f p + (1 / lam) * inner ℝ q (x - p)) ≤
      (1 - a) * params.phi_star k := by
    exact mul_le_mul_of_nonneg_left hprox (by dsimp [a]; linarith [hα.2])
  have hinter : (1 - a) * ((1 / lam) * inner ℝ q (x - p)) +
      (a / lam) * inner ℝ q (ν' - p) =
      (1 / lam) * inner ℝ q ((1 - a) • x + a • ν' - p) := by
    have hv : (1 - a) • x + a • ν' - p =
        (1 - a) • (x - p) + a • (ν' - p) := by
      module
    rw [hv, inner_add_right, inner_smul_right, inner_smul_right]
    ring
  have h15 : f p + A / 2 * ‖ν' - ν‖ ^ 2 +
      (1 / lam) * inner ℝ q ((1 - a) • x + a • ν' - p) ≤
      params.phi_star (k + 1) := by
    rw [h14]
    rw [← hinter]
    nlinarith
  have hdelta : ν' - ν = -(a / (A * lam)) • q := by
    rw [show ν' = params.nu (k + 1) by rfl, show ν = params.nu k by rfl,
      params.center_succ]
    simp [a, A, lam, q]
    module
  have hvec : (1 - a) • x + a • ν' - p =
      ((1 - a) • x + a • ν - y) + (1 - a ^ 2 / (A * lam)) • q := by
    calc
      (1 - a) • x + a • ν' - p =
          ((1 - a) • x + a • ν - y) + a • (ν' - ν) + q := by
            dsimp [q]
            module
      _ = ((1 - a) • x + a • ν - y) + (1 - a ^ 2 / (A * lam)) • q := by
            rw [hdelta]
            module
  have hinner : inner ℝ q ((1 - a) • x + a • ν' - p) =
      inner ℝ q ((1 - a) • x + a • ν - y) +
        (1 - a ^ 2 / (A * lam)) * ‖q‖ ^ 2 := by
    rw [hvec, inner_add_right, inner_smul_right]
    simp only [real_inner_self_eq_norm_sq]
  have hnorm : A / 2 * ‖ν' - ν‖ ^ 2 =
      (a ^ 2 / (2 * A * lam ^ 2)) * ‖q‖ ^ 2 := by
    rw [hdelta, norm_smul]
    rw [mul_pow]
    have habs : ‖-(a / (A * lam))‖ ^ 2 = (a / (A * lam)) ^ 2 := by
      simp only [Real.norm_eq_abs, sq_abs]
      ring
    rw [habs]
    field_simp [ne_of_gt hA, ne_of_gt hlam]
  change f p + (1 / (2 * lam)) * (2 - a ^ 2 / (A * lam)) * ‖q‖ ^ 2 +
      (1 / lam) * inner ℝ q ((1 - a) • x + a • ν - y) ≤
        params.phi_star (k + 1)
  calc
    f p + (1 / (2 * lam)) * (2 - a ^ 2 / (A * lam)) * ‖q‖ ^ 2 +
        (1 / lam) * inner ℝ q ((1 - a) • x + a • ν - y) =
        f p + A / 2 * ‖ν' - ν‖ ^ 2 +
          (1 / lam) * inner ℝ q ((1 - a) • x + a • ν' - p) := by
            rw [hnorm, hinner]
            field_simp [ne_of_gt hA, ne_of_gt hlam]
            ring
    _ ≤ params.phi_star (k + 1) := h15
