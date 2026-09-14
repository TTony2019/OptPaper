import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_2

open scoped InnerProductSpace

open ERealFunction

private theorem proximal_minimizer_supporting_inequality {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) {p y : H} {lam : ℝ} (hlam : 0 < lam)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hp : IsMinOn (fun z => f z + ‖z - y‖ ^ 2 / (2 * lam)) Set.univ p) :
    ∀ z : H, f p + inner ℝ ((1 / lam) • (y - p)) (z - p) ≤ f z := by
  intro z
  by_contra h
  push_neg at h
  let d : H := z - p
  let gap : ℝ := f p + inner ℝ ((1 / lam) • (y - p)) d - f z
  have hgap : 0 < gap := by
    dsimp [gap, d]
    linarith
  let C : ℝ := ‖d‖ ^ 2 / (2 * lam)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (sq_nonneg _) (by positivity)
  let t : ℝ := gap / (2 * (C + gap))
  have hden : 0 < 2 * (C + gap) := by positivity
  have ht : 0 < t := by
    dsimp [t]
    exact div_pos hgap hden
  have ht_lt_one : t < 1 := by
    have ht_le_half : t ≤ 1 / 2 := by
      apply (div_le_iff₀ hden).2
      dsimp [t]
      nlinarith [hC]
    linarith
  have htC_lt_gap : t * C < gap := by
    have ht_eq : t * (2 * (C + gap)) = gap := by
      dsimp [t]
      field_simp
    nlinarith [hC, hgap, ht]
  have hconv := hconvex.2 (Set.mem_univ p) (Set.mem_univ z)
    (sub_nonneg.mpr (le_of_lt ht_lt_one)) (le_of_lt ht) (by ring)
  have hmin := hp (Set.mem_univ ((1 - t) • p + t • z))
  change f p + ‖p - y‖ ^ 2 / (2 * lam) ≤
    f ((1 - t) • p + t • z) + ‖(1 - t) • p + t • z - y‖ ^ 2 / (2 * lam) at hmin
  have hcomb :
      f p + ‖p - y‖ ^ 2 / (2 * lam) ≤
        (1 - t) * f p + t * f z + ‖(1 - t) • p + t • z - y‖ ^ 2 / (2 * lam) := by
    calc
      f p + ‖p - y‖ ^ 2 / (2 * lam) ≤
          f ((1 - t) • p + t • z) + ‖(1 - t) • p + t • z - y‖ ^ 2 / (2 * lam) := hmin
      _ ≤ (1 - t) * f p + t * f z + ‖(1 - t) • p + t • z - y‖ ^ 2 / (2 * lam) :=
        by
          have hc : f ((1 - t) • p + t • z) ≤ (1 - t) * f p + t * f z := by
            simpa [smul_eq_mul] using hconv
          linarith
  have hu : (1 - t) • p + t • z - y = (p - y) + t • d := by
    dsimp [d]
    module
  have hnorm : ‖(1 - t) • p + t • z - y‖ ^ 2 =
      ‖p - y‖ ^ 2 + 2 * t * inner ℝ (p - y) d + t ^ 2 * ‖d‖ ^ 2 := by
    rw [hu, norm_add_sq_real]
    rw [inner_smul_right]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    ring
  have hlinear : inner ℝ ((1 / lam) • (y - p)) d = - inner ℝ (p - y) d / lam := by
    rw [inner_smul_left]
    have hpy : y - p = -(p - y) := by module
    rw [hpy, inner_neg_left]
    rw [div_eq_mul_inv]
    rw [starRingEnd_apply, star_trivial]
    ring
  have hdescent : 0 ≤ -gap + t * C := by
    rw [hnorm] at hcomb
    dsimp [gap, C]
    rw [hlinear]
    field_simp [ne_of_gt hlam] at hcomb ⊢
    nlinarith
  linarith

/-- Proximal optimality: a minimizer of the proximal objective has the stated subgradient. -/
theorem proximal_optimality_condition {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) {p y : H} {lam : ℝ} (hlam : 0 < lam)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hp : IsMinOn (fun z => f z + ‖z - y‖ ^ 2 / (2 * lam)) Set.univ p) :
    (1 / lam) • (y - p) ∈ subdifferential (fun y => (f y : EReal)) p := by
  rw [mem_convexSubdifferential_iff]
  exact proximal_minimizer_supporting_inequality f hlam hconvex hp
