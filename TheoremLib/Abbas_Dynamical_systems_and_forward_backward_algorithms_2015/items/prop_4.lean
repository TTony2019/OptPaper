import Mathlib
import Foundation.Hilbert.WeakTopology
import Foundation.FixedPoint.Nonexpansive
import Foundation.Differentiation.ODE
import Foundation.Hilbert.WeakConvergence
import Foundation.Convex.WeakClosed
import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_2015.items.lem_6

namespace AbbasDynamical2015

open MeasureTheory Filter Gradient

private theorem supplied_projection_eq_canonical {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (C : Set H) (projection : H → H)
    (hC : IsClosed C ∧ Convex ℝ C) (hprojection_mem : ∀ q, projection q ∈ C)
    (hprojection_min_dist : ∀ q z, z ∈ C → ‖q - projection q‖ ≤ ‖q - z‖) :
    ∀ q, projection q = projectionPoint C
      (isChebyshev_of_nonempty_isClosed_convex ⟨projection 0, hprojection_mem 0⟩ hC.1 hC.2) q := by
  intro q
  apply eq_projectionPoint_of_isBestApproximation C
    (isChebyshev_of_nonempty_isClosed_convex ⟨projection 0, hprojection_mem 0⟩ hC.1 hC.2)
  refine ⟨hprojection_mem q, ?_⟩
  refine le_antisymm ?_ (Metric.infDist_le_dist_of_mem (hprojection_mem q))
  rw [Metric.le_infDist ⟨projection 0, hprojection_mem 0⟩]
  intro z hz
  simpa only [dist_eq_norm] using hprojection_min_dist q z hz

private theorem canonical_projection_nonexpansive {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (C : Set H) (hC : IsClosed C ∧ Convex ℝ C)
    (hCne : C.Nonempty) :
    ∀ q r : H,
      ‖projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hCne hC.1 hC.2) q -
          projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hCne hC.1 hC.2) r‖ ≤
        ‖q - r‖ := by
  intro q r
  simpa [dist_eq_norm] using
    (lipschitzWith_one_of_firmlyNonexpansive
      (firmlyNonexpansive_projectionPoint_of_nonempty_isClosed_convex hCne hC.1 hC.2)).dist_le_mul q
      r

theorem gradient_uniform_locally_lipschitz_of_lipschitz_closedBalls {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (Psi : H → ℝ) (x0 : H)
    (hgrad_lipschitz_bounded : ∀ r : ℝ, ∃ L : ℝ, 0 ≤ L ∧
      LipschitzOnWith (Real.toNNReal L) (fun q ↦ ∇ Psi q) (Metric.closedBall x0 r)) :
    IsUniformLocallyLipschitzInState_nonautonomous (fun (_ : ℝ) q ↦ ∇ Psi q) := by
  intro t x
  let r : ℝ := ‖x - x0‖ + 1
  obtain ⟨L, hL, hLip⟩ := hgrad_lipschitz_bounded r
  refine ⟨Set.univ, univ_mem, Metric.ball x 1, Metric.ball_mem_nhds _ zero_lt_one,
    L, hL, ?_⟩
  intro s hs y hy z hz
  have hmem (w : H) (hw : w ∈ Metric.ball x 1) : w ∈ Metric.closedBall x0 r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hw' : ‖w - x‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    calc
      ‖w - x0‖ = ‖(w - x) + (x - x0)‖ := by congr 1; abel
      _ ≤ ‖w - x‖ + ‖x - x0‖ := norm_add_le _ _
      _ ≤ r := by dsimp [r]; linarith
  simpa [dist_eq_norm, Real.coe_toNNReal L hL] using hLip.dist_le_mul y (hmem y hy) z (hmem z hz)

private theorem canonical_projection_continuous {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (C : Set H) (hCne : C.Nonempty)
    (hC : IsClosed C ∧ Convex ℝ C) :
    Continuous (projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hCne hC.1 hC.2)) := by
  exact (lipschitzWith_one_of_firmlyNonexpansive
    (firmlyNonexpansive_projectionPoint_of_nonempty_isClosed_convex hCne hC.1 hC.2)).continuous

private theorem gradient_continuous_of_lipschitz_closedBalls {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Psi : H → ℝ) (x0 : H)
    (hgrad_lipschitz_bounded : ∀ r : ℝ, ∃ L : ℝ, 0 ≤ L ∧
      LipschitzOnWith (Real.toNNReal L) (fun q ↦ ∇ Psi q) (Metric.closedBall x0 r)) :
    Continuous (fun q : H => ∇ Psi q) := by
  have hgradlocal := gradient_uniform_locally_lipschitz_of_lipschitz_closedBalls Psi x0
    hgrad_lipschitz_bounded
  apply LocallyLipschitz.continuous
  intro q
  obtain ⟨I, hI, U, hU, L, hL, hLip⟩ := hgradlocal 0 q
  refine ⟨L.toNNReal, U, hU, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro y hy z hz
  simpa only [dist_eq_norm, Real.coe_toNNReal L hL] using
    hLip 0 (mem_of_mem_nhds hI) y hy z hz

private lemma neg_norm_mul_le_inner {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (a b : H) : -(‖a‖ * ‖b‖) ≤ inner ℝ a b := by
  simpa [inner_neg_left, norm_neg] using neg_le_neg (real_inner_le_norm (-a) b)

private theorem projection_gradient_dissipation {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Psi : H → ℝ) (C : Set H)
    (projection : H → H) (mu : ℝ) (hmu : 0 < mu)
    (hconvex : ConvexOn ℝ Set.univ Psi) (hgrad : Differentiable ℝ Psi)
    (hC : IsClosed C ∧ Convex ℝ C) (hprojection_mem : ∀ q, projection q ∈ C)
    (hprojection_min_dist : ∀ q z, z ∈ C → ‖q - projection q‖ ≤ ‖q - z‖)
    (c q : H) (hc : c ∈ C) :
    inner ℝ (projection (q - mu • ∇ Psi q) - q) (q - c) +
        mu * inner ℝ (∇ Psi q) (projection (q - mu • ∇ Psi q) - q) ≤
      mu * (Psi c - Psi q) - ‖projection (q - mu • ∇ Psi q) - q‖ ^ 2 := by
  let hCne : C.Nonempty := ⟨projection 0, hprojection_mem 0⟩
  let Pc : H := projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hCne hC.1 hC.2)
      (q - mu • ∇ Psi q)
  have hcanon : projection (q - mu • ∇ Psi q) = Pc := by
    simpa [Pc] using supplied_projection_eq_canonical C projection hC hprojection_mem
      hprojection_min_dist _
  have hvi : Pc ∈ C ∧ ∀ y ∈ C, inner ℝ (y - Pc) (q - mu • ∇ Psi q - Pc) ≤ 0 := by
    exact (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
      hCne hC.1 hC.2).mp (show projectionPoint C
        (isChebyshev_of_nonempty_isClosed_convex hCne hC.1 hC.2) (q - mu • ∇ Psi q) = Pc
      from rfl)
  have hsupport := convex_supporting_baillon_haddad Psi (fun q : H => ∇ Psi q) hconvex
      (fun q => (hgrad q).hasGradientAt) q c
  rw [hcanon]
  have hident :
      inner ℝ (Pc - q) (q - c) + mu * inner ℝ (∇ Psi q) (Pc - q) +
        ‖Pc - q‖ ^ 2 + mu * inner ℝ (∇ Psi q) (q - c) =
        inner ℝ (c - Pc) (q - mu • ∇ Psi q - Pc) := by
    rw [norm_sub_sq_real]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    nlinarith [real_inner_comm c q, real_inner_comm c Pc, real_inner_comm (∇ Psi q) c,
      real_inner_comm (∇ Psi q) Pc, real_inner_comm Pc q]
  have hsupport' : -inner ℝ (∇ Psi q) (q - c) ≤ Psi c - Psi q := by
    rw [inner_sub_right] at hsupport ⊢
    linarith
  nlinarith [hvi.2 c hc]

private theorem projection_gradient_energy_deriv {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Psi : H → ℝ) (C : Set H)
    (projection : H → H) (mu : ℝ) (x : ℝ → H) (c : H) (t : ℝ) (hc : c ∈ C)
    (hmu : 0 < mu) (hconvex : ConvexOn ℝ Set.univ Psi) (hgrad : Differentiable ℝ Psi)
    (hC : IsClosed C ∧ Convex ℝ C) (hprojection_mem : ∀ q, projection q ∈ C)
    (hprojection_min_dist : ∀ q z, z ∈ C → ‖q - projection q‖ ≤ ‖q - z‖)
    (hxt : HasDerivAt x (projection (x t - mu • ∇ Psi (x t)) - x t) t) :
    deriv (fun s ↦ (1 / 2) * ‖x s - c‖ ^ 2 + mu * (Psi (x s) - Psi c)) t +
        ‖projection (x t - mu • ∇ Psi (x t)) - x t‖ ^ 2 ≤
      mu * (Psi c - Psi (x t)) := by
  let F : H := projection (x t - mu • ∇ Psi (x t)) - x t
  have hdistance : HasDerivAt (fun s ↦ (1 / 2 : ℝ) * ‖x s - c‖ ^ 2)
      ((1 / 2 : ℝ) * (2 * inner ℝ (x t - c) F)) t := by
    simpa [F] using (hxt.sub_const c).norm_sq.const_mul (1 / 2 : ℝ)
  have hPsi : HasDerivAt (fun s ↦ Psi (x s)) (inner ℝ (∇ Psi (x t)) F) t := by
    simpa [F] using
      ((hgrad (x t)).hasGradientAt.hasFDerivAt.comp t hxt.hasFDerivAt).hasDerivAt
  have henergy := hdistance.add ((hPsi.sub_const (Psi c)).const_mul mu)
  have hderiv : deriv (fun s ↦ (1 / 2) * ‖x s - c‖ ^ 2 +
      mu * (Psi (x s) - Psi c)) t =
      inner ℝ F (x t - c) + mu * inner ℝ (∇ Psi (x t)) F := by
    calc
      deriv (fun s ↦ (1 / 2) * ‖x s - c‖ ^ 2 + mu * (Psi (x s) - Psi c)) t =
          (1 / 2 : ℝ) * (2 * inner ℝ (x t - c) F) +
            mu * inner ℝ (∇ Psi (x t)) F := by
        convert henergy.deriv using 1
      _ = inner ℝ F (x t - c) + mu * inner ℝ (∇ Psi (x t)) F := by
        rw [real_inner_comm (x t - c) F]
        ring_nf
  have hdiss := projection_gradient_dissipation Psi C projection mu hmu hconvex hgrad hC
    hprojection_mem hprojection_min_dist c (x t) hc
  rw [hderiv]
  nlinarith [hdiss]

private theorem projection_gradient_energy_lower_bound {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Psi : H → ℝ) (mu : ℝ) (c q : H)
    (hmu : 0 < mu) (hconvex : ConvexOn ℝ Set.univ Psi) (hgrad : Differentiable ℝ Psi) :
    -((mu * ‖∇ Psi c‖) ^ 2 / 2) ≤
      (1 / 2) * ‖q - c‖ ^ 2 + mu * (Psi q - Psi c) := by
  have hsupport := convex_supporting_baillon_haddad Psi (fun z : H ↦ ∇ Psi z) hconvex
    (fun z ↦ (hgrad z).hasGradientAt) c q
  nlinarith [sq_nonneg (‖q - c‖ - mu * ‖∇ Psi c‖),
    neg_norm_mul_le_inner (∇ Psi c) (q - c)]

private theorem projection_gradient_shifted_energy_antitone {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Psi : H → ℝ) (C : Set H) (projection : H → H) (mu T : ℝ) (z : ℝ → H) (c : H)
    (hmu : 0 < mu) (hconvex : ConvexOn ℝ Set.univ Psi) (hgrad : Differentiable ℝ Psi)
    (hC : IsClosed C ∧ Convex ℝ C) (hc : c ∈ C) (hprojection_mem : ∀ q, projection q ∈ C)
    (hprojection_min_dist : ∀ q w, w ∈ C → ‖q - projection q‖ ≤ ‖q - w‖)
    (hderiv : ∀ t, t ∈ Set.Ico 0 T →
      HasDerivAt z (projection (z t - mu • ∇ Psi (z t)) - z t) t) :
    AntitoneOn (fun t => Real.exp (-t) *
      ((1 / 2) * ‖z t - c‖ ^ 2 + mu * (Psi (z t) - Psi c) +
        2 * (mu * ‖∇ Psi c‖) ^ 2)) (Set.Ico 0 T) := by
  let E : ℝ → ℝ := fun t =>
    (1 / 2) * ‖z t - c‖ ^ 2 + mu * (Psi (z t) - Psi c)
  let a : ℝ := mu * ‖∇ Psi c‖
  let Y : ℝ → ℝ := fun t => E t + 2 * a ^ 2
  have hEhas (t : ℝ) (ht : t ∈ Set.Ico 0 T) : HasDerivAt E
      (inner ℝ (projection (z t - mu • ∇ Psi (z t)) - z t) (z t - c) +
        mu * inner ℝ (∇ Psi (z t)) (projection (z t - mu • ∇ Psi (z t)) - z t)) t := by
    let F : H := projection (z t - mu • ∇ Psi (z t)) - z t
    have hdistance : HasDerivAt (fun s ↦ (1 / 2 : ℝ) * ‖z s - c‖ ^ 2)
        ((1 / 2 : ℝ) * (2 * inner ℝ (z t - c) F)) t := by
      simpa [F] using ((hderiv t ht).sub_const c).norm_sq.const_mul (1 / 2 : ℝ)
    have hPsi : HasDerivAt (fun s ↦ Psi (z s)) (inner ℝ (∇ Psi (z t)) F) t := by
      simpa [F] using
        ((hgrad (z t)).hasGradientAt.hasFDerivAt.comp t (hderiv t ht).hasFDerivAt).hasDerivAt
    have hsum := hdistance.add ((hPsi.sub_const (Psi c)).const_mul mu)
    simpa [E, F, Function.comp_def, real_inner_comm] using hsum
  have hEderiv (t : ℝ) (ht : t ∈ Set.Ico 0 T) : deriv E t +
      ‖projection (z t - mu • ∇ Psi (z t)) - z t‖ ^ 2 ≤ Psi c * mu - Psi (z t) * mu := by
    rw [hEhas t ht |>.deriv]
    have hdiss := projection_gradient_dissipation Psi C projection mu hmu hconvex hgrad hC
      hprojection_mem hprojection_min_dist c (z t) hc
    nlinarith [hdiss]
  have hElower (t : ℝ) : -(a ^ 2 / 2) ≤ E t := by
    simpa [E, a] using projection_gradient_energy_lower_bound Psi mu c (z t) hmu hconvex hgrad
  have hEcomplete (t : ℝ) : (1 / 2) * ‖z t - c‖ ^ 2 - a * ‖z t - c‖ ≤ E t := by
    have hsupport := convex_supporting_baillon_haddad Psi (fun q : H => ∇ Psi q) hconvex
      (fun q => (hgrad q).hasGradientAt) c (z t)
    dsimp [E, a]
    nlinarith [neg_norm_mul_le_inner (∇ Psi c) (z t - c)]
  have hEupper (t : ℝ) : Psi c * mu - Psi (z t) * mu ≤ a * ‖z t - c‖ := by
    have hsupport := convex_supporting_baillon_haddad Psi (fun q : H => ∇ Psi q) hconvex
      (fun q => (hgrad q).hasGradientAt) c (z t)
    dsimp [a]
    nlinarith [neg_norm_mul_le_inner (∇ Psi c) (z t - c)]
  have hYderiv (t : ℝ) (ht : t ∈ Set.Ico 0 T) : deriv Y t ≤ Y t := by
    have hE := hEderiv t ht
    have hu := hEupper t
    have hl := hEcomplete t
    have hsquare := sq_nonneg (‖z t - c‖ - 2 * a)
    have hYhas := (hEhas t ht).add_const (2 * a ^ 2)
    rw [(hEhas t ht).deriv] at hE
    have hYeq := hYhas.deriv
    change deriv (fun s => E s + 2 * a ^ 2) t ≤ E t + 2 * a ^ 2
    rw [hYeq]
    nlinarith [sq_nonneg (‖projection (z t - mu • ∇ Psi (z t)) - z t‖)]
  apply antitoneOn_of_deriv_nonpos (convex_Ico 0 T)
  · intro t ht
    have hY := (hEhas t ht).add_const (2 * a ^ 2)
    have hG := (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t) |>.mul hY
    exact hG.continuousAt.continuousWithinAt
  · intro t ht
    have ht' : t ∈ Set.Ico 0 T := interior_subset ht
    have hY := (hEhas t ht').add_const (2 * a ^ 2)
    exact ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t) |>.mul hY).differentiableAt
      |>.differentiableWithinAt
  · intro t ht
    have ht' : t ∈ Set.Ico 0 T := interior_subset ht
    have hY := hYderiv t ht'
    have hY' := (hEhas t ht').add_const (2 * a ^ 2)
    have hYeq := hY'.deriv
    have hYbound : inner ℝ (projection (z t - mu • ∇ Psi (z t)) - z t) (z t - c) +
        mu * inner ℝ (∇ Psi (z t)) (projection (z t - mu • ∇ Psi (z t)) - z t) ≤ Y t := by
      rw [← hYeq]
      exact hY
    have hG := (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t) |>.mul hY'
    change deriv (fun s => Real.exp (-s) * Y s) t ≤ 0
    have hGderiv : deriv (fun s => Real.exp (-s) * Y s) t =
        Real.exp (-t) * -1 * Y t + Real.exp (-t) *
          (inner ℝ (projection (z t - mu • ∇ Psi (z t)) - z t) (z t - c) +
            mu * inner ℝ (∇ Psi (z t)) (projection (z t - mu • ∇ Psi (z t)) - z t)) := by
      simpa [Function.comp_def] using hG.deriv
    rw [hGderiv]
    have hexp : 0 < Real.exp (-t) := Real.exp_pos _
    have hYnonneg : 0 ≤ Y t := by
      dsimp [Y]
      nlinarith [hElower t, sq_nonneg a]
    nlinarith

private theorem projection_gradient_objective_dissipation {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Psi : H → ℝ) (C : Set H)
    (projection : H → H) (mu : ℝ) (x : ℝ → H) (t : ℝ) (hq : x t ∈ C)
    (hmu : 0 < mu) (hconvex : ConvexOn ℝ Set.univ Psi)
    (hgradient : ∀ z, HasGradientAt Psi (∇ Psi z) z)
    (hC : IsClosed C ∧ Convex ℝ C) (hprojection_mem : ∀ q, projection q ∈ C)
    (hprojection_min_dist : ∀ q z, z ∈ C → ‖q - projection q‖ ≤ ‖q - z‖)
    (hxt : HasDerivAt x (projection (x t - mu • ∇ Psi (x t)) - x t) t) :
    mu * deriv (fun s ↦ Psi (x s)) t +
        ‖projection (x t - mu • ∇ Psi (x t)) - x t‖ ^ 2 ≤ 0 := by
  let F : H := projection (x t - mu • ∇ Psi (x t)) - x t
  have hdiff : Differentiable ℝ Psi := fun z ↦ (hgradient z).differentiableAt
  have hPsi : HasDerivAt (fun s ↦ Psi (x s)) (inner ℝ (∇ Psi (x t)) F) t := by
    simpa [F] using
      ((hgradient (x t)).hasFDerivAt.comp t hxt.hasFDerivAt).hasDerivAt
  have hderiv : deriv (fun s ↦ Psi (x s)) t = inner ℝ (∇ Psi (x t)) F := hPsi.deriv
  have hdiss := projection_gradient_dissipation Psi C projection mu hmu hconvex hdiff hC
    hprojection_mem hprojection_min_dist (x t) (x t) hq
  rw [hderiv]
  dsimp [F]
  have hdiss' : mu * inner ℝ (∇ Psi (x t))
      (projection (x t - mu • ∇ Psi (x t)) - x t) ≤
      -‖projection (x t - mu • ∇ Psi (x t)) - x t‖ ^ 2 := by
    simpa only [sub_self, inner_zero_right, mul_zero, zero_add, zero_sub] using hdiss
  linarith

private theorem gradient_projection_field_regular {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Psi : H → ℝ) (C : Set H)
    (projection : H → H) (mu : ℝ) (x0 : H)
    (_hgrad : Differentiable ℝ Psi)
    (hgrad_lipschitz_bounded : ∀ r : ℝ, ∃ L : ℝ, 0 ≤ L ∧
      LipschitzOnWith (Real.toNNReal L) (fun q ↦ ∇ Psi q) (Metric.closedBall x0 r))
    (hC : IsClosed C ∧ Convex ℝ C) (hprojection_mem : ∀ q, projection q ∈ C)
    (hprojection_min_dist : ∀ q z, z ∈ C → ‖q - projection q‖ ≤ ‖q - z‖) :
    Continuous (fun p : ℝ × H => projection (p.2 - mu • ∇ Psi p.2) - p.2) ∧
      IsUniformLocallyLipschitzInState_nonautonomous
        (fun (_ : ℝ) q ↦ projection (q - mu • ∇ Psi q) - q) := by
  let hCne : C.Nonempty := ⟨projection 0, hprojection_mem 0⟩
  let P : H → H := projectionPoint C
    (isChebyshev_of_nonempty_isClosed_convex hCne hC.1 hC.2)
  have hPfirm := firmlyNonexpansive_projectionPoint_of_nonempty_isClosed_convex
    hCne hC.1 hC.2
  have hPcont : Continuous P := by
    simpa [P] using canonical_projection_continuous C hCne hC
  have hgradlocal := gradient_uniform_locally_lipschitz_of_lipschitz_closedBalls
    Psi x0 hgrad_lipschitz_bounded
  have hgradcont : Continuous (fun q : H => ∇ Psi q) :=
    gradient_continuous_of_lipschitz_closedBalls Psi x0 hgrad_lipschitz_bounded
  have harg : Continuous (fun p : ℝ × H => p.2 - mu • ∇ Psi p.2) := by
    exact continuous_snd.sub (continuous_const.smul (hgradcont.comp continuous_snd))
  have hproj : (fun p : ℝ × H => projection (p.2 - mu • ∇ Psi p.2)) =
      (fun p : ℝ × H => P (p.2 - mu • ∇ Psi p.2)) := by
    funext p
    exact supplied_projection_eq_canonical C projection hC hprojection_mem
      hprojection_min_dist _
  have hcont : Continuous (fun p : ℝ × H => projection (p.2 - mu • ∇ Psi p.2) - p.2) := by
    have hproj' : (fun p : ℝ × H => projection (p.2 - mu • ∇ Psi p.2) - p.2) =
        (fun p : ℝ × H => P (p.2 - mu • ∇ Psi p.2) - p.2) := by
      funext p
      exact congrArg (fun q => q - p.2) (congrFun hproj p)
    rw [hproj']
    exact (hPcont.comp harg).sub continuous_snd
  refine ⟨hcont, ?_⟩
  intro t x
  obtain ⟨I, hI, U, hU, L, hL, hLip⟩ := hgradlocal t x
  refine ⟨I, hI, U, hU, 2 + |mu| * L, by positivity, ?_⟩
  intro s hs y hy z hz
  have hgradYZ : ‖∇ Psi y - ∇ Psi z‖ ≤ L * ‖y - z‖ := by
    simpa only [dist_eq_norm] using hLip s hs y hy z hz
  have hprojYZ := canonical_projection_nonexpansive C hC hCne
    (y - mu • ∇ Psi y) (z - mu • ∇ Psi z)
  have hfield (w : H) : projection (w - mu • ∇ Psi w) = P (w - mu • ∇ Psi w) :=
    supplied_projection_eq_canonical C projection hC hprojection_mem
      hprojection_min_dist _
  change ‖(projection (y - mu • ∇ Psi y) - y) -
      (projection (z - mu • ∇ Psi z) - z)‖ ≤
        (2 + |mu| * L) * ‖y - z‖
  rw [hfield y, hfield z]
  calc
    ‖(P (y - mu • ∇ Psi y) - y) -
        (P (z - mu • ∇ Psi z) - z)‖ ≤
        ‖P (y - mu • ∇ Psi y) - P (z - mu • ∇ Psi z)‖ + ‖y - z‖ :=
      by
        rw [show (P (y - mu • ∇ Psi y) - y) -
            (P (z - mu • ∇ Psi z) - z) =
            (P (y - mu • ∇ Psi y) - P (z - mu • ∇ Psi z)) - (y - z) by
          module]
        exact norm_sub_le _ _
    _ ≤ ‖(y - mu • ∇ Psi y) - (z - mu • ∇ Psi z)‖ + ‖y - z‖ := by
      gcongr
    _ = ‖(y - z) - mu • (∇ Psi y - ∇ Psi z)‖ + ‖y - z‖ := by
      congr 2
      module
    _ ≤ (‖y - z‖ + |mu| * ‖∇ Psi y - ∇ Psi z‖) + ‖y - z‖ := by
      gcongr
      simpa [norm_smul, Real.norm_eq_abs] using
        norm_sub_le (y - z) (mu • (∇ Psi y - ∇ Psi z))
    _ ≤ (2 + |mu| * L) * ‖y - z‖ := by
      calc
        (‖y - z‖ + |mu| * ‖∇ Psi y - ∇ Psi z‖) + ‖y - z‖ ≤
            (‖y - z‖ + |mu| * (L * ‖y - z‖)) + ‖y - z‖ := by
          gcongr
        _ = (2 + |mu| * L) * ‖y - z‖ := by ring
/-- Proposition 5.1: the relaxed gradient-projection system and its asymptotic properties. -/
theorem relaxed_gradient_projection_solution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (Psi : H → ℝ) (C : Set H) (projection : H → H) (mu : ℝ) (x0 : H)
    (hmu : 0 < mu)
    (hconvex : ConvexOn ℝ Set.univ Psi) (hgrad : Differentiable ℝ Psi)
    (hgrad_lipschitz_bounded : ∀ r : ℝ, ∃ L : ℝ, 0 ≤ L ∧
      LipschitzOnWith (Real.toNNReal L) (fun q ↦ ∇ Psi q) (Metric.closedBall x0 r))
    (hC : IsClosed C ∧ Convex ℝ C) (_hbelow : ∃ m : ℝ, ∀ x ∈ C, m ≤ Psi x)
    (hprojection_mem : ∀ q, projection q ∈ C)
    (hprojection_min_dist : ∀ q z, z ∈ C → ‖q - projection q‖ ≤ ‖q - z‖) :
    ∃ x : ℝ → H,
      (x 0 = x0 ∧
        (∀ t, 0 ≤ t →
          HasDerivAt x (projection (x t - mu • ∇ Psi (x t)) - x t) t)) ∧
      (∀ y : ℝ → H,
        (y 0 = x0 ∧
          (∀ t, 0 ≤ t →
            HasDerivAt y (projection (y t - mu • ∇ Psi (y t)) - y t) t)) →
        ∀ t, 0 ≤ t → y t = x t) := by
  have hprojection_canonical : ∀ q : H, projection q = projectionPoint C
      (isChebyshev_of_nonempty_isClosed_convex ⟨projection 0, hprojection_mem 0⟩ hC.1 hC.2) q :=
    supplied_projection_eq_canonical C projection hC hprojection_mem hprojection_min_dist
  let F : ℝ → H → H := fun _ q ↦ projection (q - mu • ∇ Psi q) - q
  obtain ⟨hFcont, hFlip⟩ := gradient_projection_field_regular Psi C projection mu x0 hgrad
    hgrad_lipschitz_bounded hC hprojection_mem hprojection_min_dist
  obtain ⟨Tmax, z, hzmax, hzunique, hzextend⟩ :=
    locallyLipschitz_ode_continuation_nonautonomous F 0 x0 (by simpa [F] using hFcont) hFlip
  have hzlocal (t : ℝ) (ht : 0 ≤ t) (htT : (t : WithTop ℝ) < Tmax) :
      HasDerivAt z (projection (z t - mu • ∇ Psi (z t)) - z t) t := by
    simpa [F] using hzmax.2.2.1 t ht htT
  have henergy_local (c : H) (hc : c ∈ C) (t : ℝ) (ht : 0 ≤ t)
      (htT : (t : WithTop ℝ) < Tmax) :
      deriv (fun s ↦ (1 / 2) * ‖z s - c‖ ^ 2 + mu * (Psi (z s) - Psi c)) t +
          ‖projection (z t - mu • ∇ Psi (z t)) - z t‖ ^ 2 ≤
        mu * (Psi c - Psi (z t)) := by
    exact projection_gradient_energy_deriv Psi C projection mu z c t hc hmu hconvex hgrad hC
      hprojection_mem hprojection_min_dist (hzlocal t ht htT)
  let c : H := projection 0
  have hc : c ∈ C := hprojection_mem 0
  let E : ℝ → ℝ := fun t =>
    (1 / 2) * ‖z t - c‖ ^ 2 + mu * (Psi (z t) - Psi c)
  have hTtop : Tmax = (⊤ : WithTop ℝ) := by
    by_contra hnot
    obtain ⟨T, hTmax'⟩ := (WithTop.ne_top_iff_exists).mp hnot
    have hTmax : Tmax = (T : WithTop ℝ) := hTmax'.symm
    have hTpos : 0 < T := by simpa [hTmax] using hzmax.1
    let a : ℝ := mu * ‖∇ Psi c‖
    let Y : ℝ → ℝ := fun t => E t + 2 * a ^ 2
    have hYanti := projection_gradient_shifted_energy_antitone Psi C projection mu T z c hmu
      hconvex hgrad hC hc hprojection_mem hprojection_min_dist
      (fun t ht => hzlocal t ht.1 (by simpa [hTmax] using ht.2))
    have hYbound (t : ℝ) (ht : 0 ≤ t) (htT : t < T) : Y t ≤ Real.exp t * Y 0 := by
      have hanti := hYanti ⟨le_rfl, hTpos⟩ ⟨ht, htT⟩ ht
      have hmul := mul_le_mul_of_nonneg_left hanti (Real.exp_pos t).le
      have hexp : Real.exp t * Real.exp (-t) = 1 := by simp [Real.exp_neg]
      change E t + 2 * a ^ 2 ≤ Real.exp t * (E 0 + 2 * a ^ 2)
      simpa [E, a, mul_assoc, mul_left_comm, mul_comm, hexp] using hmul
    have hEbound (t : ℝ) (ht : 0 ≤ t) (htT : t < T) : E t ≤ Real.exp T * Y 0 := by
      calc
        E t ≤ Y t := by dsimp [Y]; nlinarith [sq_nonneg a]
        _ ≤ Real.exp t * Y 0 := hYbound t ht htT
        _ ≤ Real.exp T * Y 0 := by
          have hexp := Real.exp_le_exp.mpr htT.le
          have hYnonneg : 0 ≤ Y 0 := by
            have hlower := projection_gradient_energy_lower_bound Psi mu c (z 0) hmu hconvex hgrad
            dsimp [E, Y, a] at hlower ⊢
            nlinarith [sq_nonneg (mu * ‖∇ Psi c‖)]
          exact mul_le_mul_of_nonneg_right hexp hYnonneg
    have hElower (t : ℝ) : (1 / 2) * ‖z t - c‖ ^ 2 - a * ‖z t - c‖ ≤ E t := by
      have hsupport := convex_supporting_baillon_haddad Psi (fun q : H => ∇ Psi q) hconvex
        (fun q => (hgrad q).hasGradientAt) c (z t)
      dsimp [E, a]
      nlinarith [neg_norm_mul_le_inner (∇ Psi c) (z t - c)]
    let B : ℝ := max 0 (Real.exp T * Y 0 + a ^ 2 / 2)
    have hB : 0 ≤ B := le_max_left _ _
    let R : ℝ := a + Real.sqrt (2 * B)
    have hR : 0 ≤ R := by
      dsimp [R, a]
      positivity
    have hRbound (t : ℝ) (ht : 0 ≤ t) (htT : t < T) : ‖z t - c‖ ≤ R := by
      have hsq := sq_nonneg (‖z t - c‖ - a)
      have hsqrt : (Real.sqrt (2 * B)) ^ 2 = 2 * B := by
        rw [Real.sq_sqrt]
        positivity
      have hE := hEbound t ht htT
      have hlower := hElower t
      have hBdom : Real.exp T * Y 0 + a ^ 2 / 2 ≤ B := le_max_right _ _
      have hroot : 0 ≤ Real.sqrt (2 * B) := Real.sqrt_nonneg _
      dsimp [B, R] at hE hsq hsqrt ⊢
      nlinarith
    let r : ℝ := R + ‖c - x0‖
    have hr : 0 ≤ r := by dsimp [r]; positivity
    obtain ⟨L, hL, hLip⟩ := hgrad_lipschitz_bounded r
    let P : H → H := projectionPoint C
      (isChebyshev_of_nonempty_isClosed_convex ⟨projection 0, hprojection_mem 0⟩ hC.1 hC.2)
    have hPnonexp := canonical_projection_nonexpansive C hC
      (show C.Nonempty from ⟨projection 0, hprojection_mem 0⟩)
    have hzball (t : ℝ) (ht : 0 ≤ t) (htT : t < T) : z t ∈ Metric.closedBall x0 r := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      calc
        ‖z t - x0‖ = ‖(z t - c) + (c - x0)‖ := by congr 1; abel
        _ ≤ ‖z t - c‖ + ‖c - x0‖ := norm_add_le _ _
        _ ≤ R + ‖c - x0‖ := add_le_add (hRbound t ht htT) le_rfl
        _ = r := rfl
    have hx0ball : x0 ∈ Metric.closedBall x0 r := by
      rw [Metric.mem_closedBall, dist_self]
      exact hr
    let M : ℝ := ‖projection (x0 - mu • ∇ Psi x0) - x0‖ + (2 + |mu| * L) * r
    have hM : 0 ≤ M := by
      dsimp [M]
      positivity
    have hFbound (t : ℝ) (ht : 0 ≤ t) (htT : t < T) :
        ‖projection (z t - mu • ∇ Psi (z t)) - z t‖ ≤ M := by
      have hproj := hPnonexp (z t - mu • ∇ Psi (z t)) (x0 - mu • ∇ Psi x0)
      have hgradlip := hLip.dist_le_mul (z t) (hzball t ht htT) x0 hx0ball
      have hzdist : ‖z t - x0‖ ≤ r := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hzball t ht htT
      rw [dist_eq_norm, dist_eq_norm] at hgradlip
      have harg : (z t - mu • ∇ Psi (z t)) - (x0 - mu • ∇ Psi x0) =
          (z t - x0) - mu • (∇ Psi (z t) - ∇ Psi x0) := by
        rw [smul_sub]
        abel
      have hcanon1 := hprojection_canonical (z t - mu • ∇ Psi (z t))
      have hcanon0 := hprojection_canonical (x0 - mu • ∇ Psi x0)
      calc
        ‖projection (z t - mu • ∇ Psi (z t)) - z t‖ ≤
            ‖projection (z t - mu • ∇ Psi (z t)) - projection (x0 - mu • ∇ Psi x0)‖ +
              ‖projection (x0 - mu • ∇ Psi x0) - x0‖ + ‖z t - x0‖ := by
          have h1 : ‖projection (z t - mu • ∇ Psi (z t)) - z t‖ ≤
              ‖projection (z t - mu • ∇ Psi (z t)) - projection (x0 - mu • ∇ Psi x0)‖ +
                ‖projection (x0 - mu • ∇ Psi x0) - z t‖ := by
            simpa [dist_eq_norm] using
              dist_triangle (projection (z t - mu • ∇ Psi (z t)))
                (projection (x0 - mu • ∇ Psi x0)) (z t)
          have h2 : ‖projection (x0 - mu • ∇ Psi x0) - z t‖ ≤
              ‖projection (x0 - mu • ∇ Psi x0) - x0‖ + ‖z t - x0‖ := by
            simpa [dist_eq_norm, norm_sub_rev] using
              dist_triangle (projection (x0 - mu • ∇ Psi x0)) (x0) (z t)
          nlinarith
        _ ≤ ‖(z t - mu • ∇ Psi (z t)) - (x0 - mu • ∇ Psi x0)‖ +
              ‖projection (x0 - mu • ∇ Psi x0) - x0‖ + ‖z t - x0‖ := by
          gcongr
          simpa [hcanon1, hcanon0] using hproj
        _ ≤ (‖z t - x0‖ + |mu| * ‖∇ Psi (z t) - ∇ Psi x0‖) +
              ‖projection (x0 - mu • ∇ Psi x0) - x0‖ + ‖z t - x0‖ := by
          gcongr
          rw [harg]
          simpa [norm_smul, Real.norm_eq_abs] using
            norm_sub_le (z t - x0) (mu • (∇ Psi (z t) - ∇ Psi x0))
        _ ≤ (2 + |mu| * L) * r + ‖projection (x0 - mu • ∇ Psi x0) - x0‖ := by
          have hgradlip' : ‖∇ Psi (z t) - ∇ Psi x0‖ ≤ L * ‖z t - x0‖ := by
            simpa [Real.coe_toNNReal L hL] using hgradlip
          have hscaled := mul_le_mul_of_nonneg_left hgradlip' (abs_nonneg mu)
          have hcoef : 0 ≤ 2 + |mu| * L := by positivity
          have hscaledr := mul_le_mul_of_nonneg_left hzdist hcoef
          nlinarith [norm_nonneg (z t - x0), abs_nonneg mu]
        _ = M := by dsimp [M]; ring
    obtain ⟨l, hlim⟩ := tendsto_at_right_of_norm_deriv_le hTpos hM
      (fun t ht htT => hzmax.2.2.1 t ht (by simpa [hTmax] using htT))
      (fun t ht htT => hFbound t ht htT)
    have hdomain : Set.Ico 0 T = {t : ℝ | 0 ≤ t ∧ (t : WithTop ℝ) < Tmax} := by
      ext t
      simp [hTmax]
    obtain ⟨U, hTU, w, hwode, hwz⟩ := hzextend T hTmax l (hdomain ▸ hlim)
    have hsub : {t : ℝ | 0 ≤ t ∧ (t : WithTop ℝ) < Tmax} ⊆ Set.Ico 0 U := by
      intro t ht
      refine ⟨ht.1, ?_⟩
      have htT : t < T := by simpa [hTmax] using ht.2
      exact lt_trans htT hTU
    have hmax := hzmax.2.2.2 (Set.Ico 0 U) w Set.ordConnected_Ico
      (by exact ⟨le_rfl, lt_trans hTpos hTU⟩)
      (by intro t ht; exact hwode t ht.1 ht.2)
      hsub
      (by intro t ht htT; exact (hwz t ht (by simpa [hTmax] using htT)).symm)
    have hTin : T ∈ Set.Ico 0 U ∩ Set.Ici 0 := ⟨⟨hTpos.le, hTU⟩, hTpos.le⟩
    have hbad := hmax hTin
    exact (lt_irrefl T) (by simpa [hTmax] using hbad.2)
  refine ⟨z, ⟨by simpa using hzmax.2.1, ?_⟩, ?_⟩
  · intro t ht
    simpa [F] using hzmax.2.2.1 t ht (by simp [hTtop])
  · intro y hy t ht
    have hymax : IsMaximalClassicalSolution_nonautonomous F 0 x0 (⊤ : WithTop ℝ) y := by
      refine ⟨by simp, hy.1, ?_, ?_⟩
      · intro s hs _
        simpa [F] using hy.2 s hs
      · intro I w hI h0 hw hsub heq s hs
        exact ⟨hs.2, by simp⟩
    obtain ⟨_, heq⟩ := hzunique ⊤ y hymax
    simpa [hTtop] using heq t ht (by simp [hTtop])

private theorem relaxed_projection_variation_of_constants
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (t : ℝ) (x p : ℝ → H) (ht : 0 ≤ t)
    (hp : ContinuousOn p (Set.Icc 0 t))
    (hderiv : ∀ s, s ∈ Set.Icc 0 t → HasDerivAt x (p s - x s) s) :
    x t = Real.exp (-t) • x 0 +
      ∫ s in 0..t, Real.exp (-(t - s)) • p s := by
  have hderiv' : ∀ s ∈ Set.Icc 0 t,
      HasDerivAt (fun u : ℝ => Real.exp u • x u) (Real.exp s • p s) s := by
    intro s hs
    convert (Real.hasDerivAt_exp s).smul (hderiv s hs) using 1; module
  have hint : IntervalIntegrable (fun s : ℝ => Real.exp s • p s)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) 0 t := by
    have hp' : ContinuousOn p (Set.uIcc 0 t) := by
      simpa only [Set.uIcc_of_le ht] using hp
    exact (Real.continuous_exp.continuousOn.smul hp').intervalIntegrable
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := t) (f := fun s : ℝ => Real.exp s • x s)
    (f' := fun s : ℝ => Real.exp s • p s)
    (fun s hs => hderiv' s (by simpa [Set.uIcc_of_le ht] using hs)) hint
  have hscaled := congrArg (fun z : H => Real.exp (-t) • z) hfund
  have hkernel : (∫ s in 0..t, Real.exp (-(t - s)) • p s) =
      Real.exp (-t) • ∫ s in 0..t, Real.exp s • p s := by
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro s _
    change Real.exp (-(t - s)) • p s = Real.exp (-t) • (Real.exp s • p s)
    rw [← mul_smul]
    congr 1
    rw [← Real.exp_add]
    congr 1
    ring
  have hsub : x t - Real.exp (-t) • x 0 =
      ∫ s in 0..t, Real.exp (-(t - s)) • p s := by
    rw [hkernel]
    have hexp : Real.exp (-t) * Real.exp t = 1 := by simp [Real.exp_neg]
    simpa [smul_sub, smul_smul, hexp] using hscaled.symm
  simpa [add_comm] using eq_add_of_sub_eq hsub

private theorem exp_weighted_average_mem_closed_convex
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (C : Set H) (p : ℝ → H) (t : ℝ) (ht : 0 < t) (hC : IsClosed C ∧ Convex ℝ C)
    (hp : ContinuousOn p (Set.Icc 0 t))
    (hpmem : ∀ s, s ∈ Set.Icc 0 t → p s ∈ C) :
    (Real.exp t - 1)⁻¹ • (∫ s in 0..t, Real.exp s • p s) ∈ C := by
  let I : Set ℝ := Set.Icc 0 t
  let μI : MeasureTheory.Measure ℝ := volume.restrict I
  let ρ : ℝ → ENNReal := fun s => ENNReal.ofReal (Real.exp s)
  let ν : MeasureTheory.Measure ℝ := μI.withDensity ρ
  have hscalar : MeasureTheory.Integrable (fun s : ℝ => Real.exp s) μI := by
    change IntegrableOn (fun s : ℝ => Real.exp s) I volume
    exact Real.continuous_exp.continuousOn.integrableOn_Icc
  have hρmeas : Measurable ρ := by
    dsimp [ρ]
    fun_prop
  have hρtop : ∀ᵐ s ∂μI, ρ s < (⊤ : ENNReal) :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  letI : MeasureTheory.IsFiniteMeasure ν := by
    dsimp [ν, ρ]
    exact MeasureTheory.isFiniteMeasure_withDensity_ofReal hscalar.hasFiniteIntegral
  have hmassI : ∫ s in I, Real.exp s = Real.exp t - 1 := by
    dsimp [I]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ht.le]
    simp
  have hνmass : ν.real Set.univ = Real.exp t - 1 := by
    rw [MeasureTheory.measureReal_def, show ν = μI.withDensity ρ from rfl,
      MeasureTheory.withDensity_apply ρ MeasurableSet.univ]
    rw [MeasureTheory.setLIntegral_univ]
    change ENNReal.toReal (∫⁻ s, ENNReal.ofReal (Real.exp s) ∂μI) = _
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hscalar]
    · change ENNReal.toReal (ENNReal.ofReal (∫ s in I, Real.exp s)) = _
      rw [hmassI]
      rw [ENNReal.toReal_ofReal (le_of_lt (sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)))]
    · filter_upwards with s
      exact Real.exp_nonneg s
  have hmasspos : 0 < Real.exp t - 1 := by
    exact sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)
  have hνne : ν ≠ 0 := by
    intro hzero
    have hzero' : ν.real Set.univ = 0 := by simp [hzero]
    linarith [hνmass]
  letI : NeZero ν := ⟨hνne⟩
  have hwp : MeasureTheory.Integrable (fun s => Real.exp s • p s) μI := by
    change IntegrableOn (fun s => Real.exp s • p s) I volume
    exact (Real.continuous_exp.continuousOn.smul hp).integrableOn_Icc
  have hpν : MeasureTheory.Integrable p ν := by
    rw [show ν = μI.withDensity ρ from rfl,
      MeasureTheory.integrable_withDensity_iff_integrable_smul' hρmeas hρtop]
    simpa [ρ, ENNReal.toReal_ofReal, Real.exp_nonneg] using hwp
  have hpmemν : ∀ᵐ s ∂ν, p s ∈ C := by
    rw [show ν = μI.withDensity ρ from rfl, MeasureTheory.ae_withDensity_iff hρmeas]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs _
    exact hpmem s (by simpa [I] using hs)
  have hqC : ⨍ s, p s ∂ν ∈ C := hC.2.average_mem hC.1 hpmemν hpν
  have hνintegral : (∫ s, p s ∂ν) = ∫ s in 0..t, Real.exp s • p s := by
    rw [show ν = μI.withDensity ρ from rfl,
      integral_withDensity_eq_integral_toReal_smul hρmeas hρtop]
    change (∫ s in I, (ρ s).toReal • p s) = _
    simp only [ρ, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ht.le]
  rw [MeasureTheory.average_eq, hνmass, hνintegral] at hqC
  exact hqC

private theorem relaxed_projection_variation_mem_closed_convex
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (C : Set H) (x p : ℝ → H) (t : ℝ) (ht : 0 ≤ t) (hx0 : x 0 ∈ C)
    (hC : IsClosed C ∧ Convex ℝ C) (hp : ContinuousOn p (Set.Icc 0 t))
    (hpmem : ∀ s, s ∈ Set.Icc 0 t → p s ∈ C)
    (hformula : x t = Real.exp (-t) • x 0 +
      ∫ s in 0..t, Real.exp (-(t - s)) • p s) : x t ∈ C := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa using hx0
  let A : H := ∫ s in 0..t, Real.exp s • p s
  let q : H := (Real.exp t - 1)⁻¹ • A
  have hqC : q ∈ C := by
    simpa [q, A] using exp_weighted_average_mem_closed_convex C p t ht hC hp hpmem
  have hexp : Real.exp (-t) * Real.exp t = 1 := by
    simp [Real.exp_neg]
  have hdenom : Real.exp t - 1 ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr ht))
  have hcoeff : 1 - Real.exp (-t) = Real.exp (-t) * (Real.exp t - 1) := by
    nlinarith [hexp]
  have hkernel : (∫ s in 0..t, Real.exp (-(t - s)) • p s) = Real.exp (-t) • A := by
    dsimp [A]
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro s _
    change Real.exp (-(t - s)) • p s = Real.exp (-t) • (Real.exp s • p s)
    rw [← mul_smul, ← Real.exp_add]
    congr 1
    ring_nf
  have hline : x t = (AffineMap.lineMap (x 0) q) (1 - Real.exp (-t)) := by
    rw [hformula, hkernel, AffineMap.lineMap_apply]
    dsimp [q]
    rw [smul_sub, smul_smul, hcoeff]
    field_simp
    rw [← hcoeff]
    module
  apply hline ▸ hC.2.lineMap_mem hx0 hqC
  constructor
  · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le))
  · linarith [Real.exp_pos (-t)]

private theorem integrableOn_Ici_of_nonneg_interval_bound_local
    {g : ℝ → ℝ} {a C : ℝ}
    (hlocal : ∀ T, IntegrableOn g (Set.Ioc a T))
    (hnonneg : ∀ s, a ≤ s → 0 ≤ g s)
    (hbound : ∀ T, a ≤ T → ∫ s in a..T, g s ≤ C) :
    IntegrableOn g (Set.Ici a) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded C a hlocal
    Filter.tendsto_id
  filter_upwards [Filter.eventually_ge_atTop a] with T hT
  have hnorm : (∫ s in a..T, ‖g s‖) = ∫ s in a..T, g s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hs
    rw [Set.uIoc_of_le hT] at hs
    exact Real.norm_of_nonneg (hnonneg s hs.1.le)
  rw [hnorm]
  exact hbound T hT

/-- Integrating a nonnegative terminal energy and a pointwise dissipation inequality on a
compact interval.  At applications, `E'` and `D` should be written using the continuous ODE
vector field rather than `deriv x`. -/
private theorem energy_dissipation_interval_bound_local
    {E E' D : ℝ → ℝ} {a T : ℝ}
    (hAT : a ≤ T)
    (hE : ∀ s ∈ Set.Icc a T, HasDerivAt E (E' s) s)
    (hE'cont : ContinuousOn E' (Set.Icc a T))
    (hDcont : ContinuousOn D (Set.Icc a T))
    (hdescent : ∀ s ∈ Set.Icc a T, E' s + D s ≤ 0)
    (hET : 0 ≤ E T) :
    ∫ s in a..T, D s ≤ E a := by
  have hEcont : ContinuousOn E (Set.Icc a T) := fun s hs =>
    (hE s hs).continuousAt.continuousWithinAt
  have hE'int : IntervalIntegrable E' volume a T := by
    have hc : ContinuousOn E' (Set.uIcc a T) := by
      simpa [Set.uIcc_of_le hAT] using hE'cont
    exact hc.intervalIntegrable
  have hDint : IntervalIntegrable D volume a T := by
    have hc : ContinuousOn D (Set.uIcc a T) := by
      simpa [Set.uIcc_of_le hAT] using hDcont
    exact hc.intervalIntegrable
  have hmono : (∫ s in a..T, E' s) ≤ ∫ s in a..T, -D s := by
    apply intervalIntegral.integral_mono_on hAT hE'int hDint.neg
    intro s hs
    change E' s ≤ -D s
    linarith [hdescent s hs]
  have hftc : (∫ s in a..T, E' s) = E T - E a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hAT hEcont
    · intro s hs
      exact hE s ⟨hs.1.le, hs.2.le⟩
    · exact hE'int
  rw [hftc, intervalIntegral.integral_neg] at hmono
  linarith

private theorem tendsto_of_antitone_nonneg_on_Ici_local (F : ℝ → ℝ)
    (hanti : AntitoneOn F (Set.Ici 0))
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ F t) :
    ∃ L, Tendsto F atTop (nhds L) := by
  let G : ℝ → ℝ := fun t => F (max t 0)
  have hGanti : Antitone G := by
    intro s t hst
    exact hanti (le_max_right s 0) (le_max_right t 0) (max_le_max_right 0 hst)
  have hGbelow : BddBelow (Set.range G) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact hnonneg _ (le_max_right _ _)
  refine ⟨⨅ t, G t, ?_⟩
  apply (tendsto_atTop_ciInf hGanti hGbelow).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp [G, max_eq_left ht]

theorem relaxed_gradient_projection_asymptotics {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (Psi : H → ℝ) (projection : H → H) (C S : Set H) (x : ℝ → H) (mu : ℝ)
    (hs : S = {z | z ∈ C ∧ ∀ y ∈ C, Psi z ≤ Psi y}) (hS : S.Nonempty)
    (hmu : 0 < mu)
    (hconvex : ConvexOn ℝ Set.univ Psi)
    (hgradient : ∀ z, HasGradientAt Psi (∇ Psi z) z)
    (hgrad_lipschitz_bounded : ∀ r : ℝ, ∃ L : ℝ, 0 ≤ L ∧
      LipschitzOnWith (Real.toNNReal L) (fun q ↦ ∇ Psi q) (Metric.closedBall (x 0) r))
    (hC : IsClosed C ∧ Convex ℝ C)
    (_hbelow : ∃ m : ℝ, ∀ y ∈ C, m ≤ Psi y)
    (hprojection_mem : ∀ q, projection q ∈ C)
    (hprojection_min_dist : ∀ q z, z ∈ C → ‖q - projection q‖ ≤ ‖q - z‖)
    (_hdynamics : ∀ t, deriv x t + x t - projection (x t - mu • ∇ Psi (x t)) = 0)
    (hclassical : ∀ t, 0 ≤ t →
      HasDerivAt x (projection (x t - mu • ∇ Psi (x t)) - x t) t)
    (hx0 : x 0 ∈ C) :
    (∃ z ∈ S, Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) atTop (nhds (toWeakSpace ℝ H z))) ∧
    (∀ t, 0 ≤ t → x t ∈ C) ∧ AntitoneOn (fun t ↦ Psi (x t)) (Set.Ici 0) ∧
    Tendsto (fun t ↦ Psi (x t)) atTop (nhds (sInf (Psi '' C))) ∧
    ∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))),
      mu * deriv (fun s ↦ Psi (x s)) t + ‖deriv x t‖ ^ 2 ≤ 0 := by
  have hprojection_canonical : ∀ q : H, projection q = projectionPoint C
      (isChebyshev_of_nonempty_isClosed_convex ⟨projection 0, hprojection_mem 0⟩ hC.1 hC.2) q :=
    supplied_projection_eq_canonical C projection hC hprojection_mem hprojection_min_dist
  have hcanonical_nonexpansive := canonical_projection_nonexpansive C hC
    (show C.Nonempty from ⟨projection 0, hprojection_mem 0⟩)
  have hpointwise (t : ℝ) (ht : 0 ≤ t) (hxtC : x t ∈ C) :
      mu * deriv (fun s ↦ Psi (x s)) t + ‖deriv x t‖ ^ 2 ≤ 0 := by
    have h := projection_gradient_objective_dissipation Psi C projection mu x t hxtC hmu hconvex
      hgradient hC hprojection_mem hprojection_min_dist (hclassical t ht)
    simpa only [(hclassical t ht).deriv] using h
  let P : H → H := projectionPoint C
    (isChebyshev_of_nonempty_isClosed_convex ⟨projection 0, hprojection_mem 0⟩ hC.1 hC.2)
  have hPcont : Continuous P := by
    simpa [P] using canonical_projection_continuous C ⟨projection 0, hprojection_mem 0⟩ hC
  have hgradcont : Continuous (fun q : H => ∇ Psi q) :=
    gradient_continuous_of_lipschitz_closedBalls Psi (x 0) hgrad_lipschitz_bounded
  have hforward (t : ℝ) (ht : 0 ≤ t) : x t ∈ C := by
    let p : ℝ → H := fun s => projection (x s - mu • ∇ Psi (x s))
    have hp : ContinuousOn p (Set.Icc 0 t) := by
      intro s hs
      have hxcont : ContinuousAt x s := (hclassical s hs.1).continuousAt
      have hgradcont' : ContinuousAt (fun u : ℝ => ∇ Psi (x u)) s :=
        hgradcont.continuousAt.comp hxcont
      have harg : ContinuousAt (fun u : ℝ => x u - mu • ∇ Psi (x u)) s :=
        hxcont.sub (continuousAt_const.smul hgradcont')
      change ContinuousWithinAt (fun u : ℝ => projection (x u - mu • ∇ Psi (x u)))
        (Set.Icc 0 t) s
      have hprojfun : (fun u : ℝ => projection (x u - mu • ∇ Psi (x u))) =
          (fun u : ℝ => P (x u - mu • ∇ Psi (x u))) := by
        funext u
        exact hprojection_canonical _
      rw [hprojfun]
      exact (hPcont.continuousAt.comp harg).continuousWithinAt
    have hformula := relaxed_projection_variation_of_constants t x p ht hp
      (fun s hs => by simpa [p] using hclassical s hs.1)
    exact relaxed_projection_variation_mem_closed_convex C x p t ht hx0 hC hp
      (fun s _ => hprojection_mem _) hformula
  have hPsiDeriv (t : ℝ) (ht : 0 ≤ t) : HasDerivAt (fun s => Psi (x s))
      (inner ℝ (∇ Psi (x t)) (projection (x t - mu • ∇ Psi (x t)) - x t)) t := by
    simpa using ((hgradient (x t)).hasFDerivAt.comp t
      (hclassical t ht).hasFDerivAt).hasDerivAt
  have hanti : AntitoneOn (fun t => Psi (x t)) (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro t ht
      exact (hPsiDeriv t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hPsiDeriv t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have h := hpointwise t (interior_subset ht) (hforward t (interior_subset ht))
      have hnorm : 0 ≤ ‖deriv x t‖ ^ 2 := sq_nonneg _
      nlinarith [hmu]
  have haediss : ∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))),
      mu * deriv (fun s ↦ Psi (x s)) t + ‖deriv x t‖ ^ 2 ≤ 0 := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
    exact hpointwise t ht (hforward t ht)
  obtain ⟨z0, hz0⟩ := hS
  have hz0' : z0 ∈ C ∧ ∀ y ∈ C, Psi z0 ≤ Psi y := by
    rw [hs] at hz0
    exact hz0
  have hInf : sInf (Psi '' C) = Psi z0 := by
    apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
    · exact ⟨Psi z0, ⟨z0, hz0'.1, rfl⟩⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact hz0'.2 y hy
    · intro w hw
      exact ⟨Psi z0, ⟨z0, hz0'.1, rfl⟩, hw⟩
  let G : ℝ → ℝ := fun t => Psi (x t) - Psi z0
  have hGnonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ G t := by
    exact sub_nonneg.mpr (hz0'.2 (x t) (hforward t ht))
  let E : ℝ → ℝ := fun t => (1 / 2) * ‖x t - z0‖ ^ 2 + mu * G t
  have hEhas (t : ℝ) (ht : 0 ≤ t) : HasDerivAt E
      (inner ℝ (projection (x t - mu • ∇ Psi (x t)) - x t) (x t - z0) +
        mu * inner ℝ (∇ Psi (x t))
          (projection (x t - mu • ∇ Psi (x t)) - x t)) t := by
    let F : H := projection (x t - mu • ∇ Psi (x t)) - x t
    have hdistance : HasDerivAt (fun s ↦ (1 / 2 : ℝ) * ‖x s - z0‖ ^ 2)
        ((1 / 2 : ℝ) * (2 * inner ℝ (x t - z0) F)) t := by
      simpa [F] using ((hclassical t ht).sub_const z0).norm_sq.const_mul (1 / 2 : ℝ)
    have hPsi : HasDerivAt (fun s ↦ Psi (x s)) (inner ℝ (∇ Psi (x t)) F) t := by
      simpa [F] using ((hgradient (x t)).hasFDerivAt.comp t
        (hclassical t ht).hasFDerivAt).hasDerivAt
    have hsum := hdistance.add ((hPsi.sub_const (Psi z0)).const_mul mu)
    simpa [E, G, F, real_inner_comm] using hsum
  have hEderiv (t : ℝ) (ht : 0 ≤ t) :
      deriv E t + ‖deriv x t‖ ^ 2 + mu * G t ≤ 0 := by
    have h := projection_gradient_energy_deriv Psi C projection mu x z0 t hz0'.1 hmu hconvex
      (fun q ↦ (hgradient q).differentiableAt) hC hprojection_mem hprojection_min_dist
      (hclassical t ht)
    rw [(hclassical t ht).deriv]
    change deriv (fun s ↦ (1 / 2) * ‖x s - z0‖ ^ 2 +
      mu * (Psi (x s) - Psi z0)) t +
        ‖projection (x t - mu • ∇ Psi (x t)) - x t‖ ^ 2 +
          mu * (Psi (x t) - Psi z0) ≤ 0
    nlinarith [hz0'.2 (x t) (hforward t ht)]
  have hEanti : AntitoneOn E (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro t ht
      exact (hEhas t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hEhas t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have h := hEderiv t (interior_subset ht)
      nlinarith [sq_nonneg ‖deriv x t‖, mul_nonneg hmu.le
        (hGnonneg t (interior_subset ht))]
  have hEnonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ E t := by
    dsimp [E]
    exact add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (mul_nonneg hmu.le (hGnonneg t ht))
  obtain ⟨einf, hElim⟩ := tendsto_of_antitone_nonneg_on_Ici_local E hEanti hEnonneg
  have hPsiCont : Continuous Psi := continuous_iff_continuousAt.mpr fun q =>
    (hgradient q).continuousAt
  let F : ℝ → H := fun t => projection (x t - mu • ∇ Psi (x t)) - x t
  let E' : ℝ → ℝ := fun t =>
    inner ℝ (F t) (x t - z0) + mu * inner ℝ (∇ Psi (x t)) (F t)
  have hxcontOn (T : ℝ) : ContinuousOn x (Set.Icc 0 T) := by
    intro t ht
    exact (hclassical t ht.1).continuousAt.continuousWithinAt
  have hFcontOn (T : ℝ) : ContinuousOn F (Set.Icc 0 T) := by
    have hxcont := hxcontOn T
    have hgradx : ContinuousOn (fun t => ∇ Psi (x t)) (Set.Icc 0 T) :=
      hgradcont.continuousOn.comp hxcont (Set.mapsTo_univ x _)
    have harg : ContinuousOn (fun t => x t - mu • ∇ Psi (x t)) (Set.Icc 0 T) :=
      hxcont.sub (continuousOn_const.smul hgradx)
    have hParg : ContinuousOn (fun t => P (x t - mu • ∇ Psi (x t)))
        (Set.Icc 0 T) := hPcont.continuousOn.comp harg (Set.mapsTo_univ _ _)
    apply (hParg.sub hxcont).congr
    intro t _
    simp only [F]
    rw [hprojection_canonical]
  have hE'contOn (T : ℝ) : ContinuousOn E' (Set.Icc 0 T) := by
    have hxcont := hxcontOn T
    have hFc := hFcontOn T
    have hgradx : ContinuousOn (fun t => ∇ Psi (x t)) (Set.Icc 0 T) :=
      hgradcont.continuousOn.comp hxcont (Set.mapsTo_univ x _)
    exact ((hFc.inner (hxcont.sub continuousOn_const)).add
      (continuousOn_const.mul (hgradx.inner hFc))).congr fun _ _ => rfl
  have hGcontOn (T : ℝ) : ContinuousOn G (Set.Icc 0 T) := by
    exact ((hPsiCont.continuousOn.comp (hxcontOn T) (Set.mapsTo_univ x _)).sub
      continuousOn_const).congr fun _ _ => rfl
  have hfinite (T : ℝ) (hT : 0 ≤ T) :
      ∫ t in 0..T, mu * G t ≤ E 0 := by
    apply energy_dissipation_interval_bound_local hT
    · intro t ht
      simpa [E'] using hEhas t ht.1
    · exact hE'contOn T
    · exact continuousOn_const.mul (hGcontOn T)
    · intro t ht
      have h := hEderiv t ht.1
      rw [(hEhas t ht.1).deriv, (hclassical t ht.1).deriv] at h
      change E' t + mu * G t ≤ 0
      dsimp [E', F]
      nlinarith [sq_nonneg ‖projection (x t - mu • ∇ Psi (x t)) - x t‖]
    · exact hEnonneg T hT
  have hGanti : AntitoneOn G (Set.Ici 0) := by
    intro s hs t ht hst
    exact sub_le_sub_right (hanti hs ht hst) _
  have hGrate (T : ℝ) (hT : 0 < T) : G T ≤ E 0 / (mu * T) := by
    have hconstInt : ∫ _ in (0 : ℝ)..T, mu * G T = T * (mu * G T) := by
      simp
      ring
    have hmonoInt : (∫ _ in (0 : ℝ)..T, mu * G T) ≤ ∫ t in 0..T, mu * G t := by
      apply intervalIntegral.integral_mono_on hT.le
      · exact intervalIntegrable_const
      · exact (continuousOn_const.mul (hGcontOn T)).intervalIntegrable_of_Icc hT.le
      · intro t ht
        exact mul_le_mul_of_nonneg_left
          (hGanti (Set.mem_Ici.mpr ht.1) (Set.mem_Ici.mpr hT.le) ht.2) hmu.le
    have hbound : T * (mu * G T) ≤ E 0 := by
      rw [← hconstInt]
      exact hmonoInt.trans (hfinite T hT.le)
    apply (le_div_iff₀ (mul_pos hmu hT)).2
    nlinarith
  have hGlim : Tendsto G atTop (nhds 0) := by
    have hupper : Tendsto (fun T : ℝ => E 0 / (mu * T)) atTop (nhds 0) := by
      simpa [div_div] using
        (tendsto_const_nhds.div_atTop Filter.tendsto_id :
          Tendsto (fun T : ℝ => (E 0 / mu) / T) atTop (nhds 0))
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      exact hGnonneg T hT
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      exact hGrate T hT
    · exact hupper
  have hobjlim : Tendsto (fun t => Psi (x t)) atTop (nhds (Psi z0)) := by
    simpa [G] using hGlim.add_const (Psi z0)
  have hdist : ∀ z ∈ S, ∃ l : ℝ, Tendsto (fun t => ‖x t - z‖) atTop (nhds l) := by
    intro z hz
    have hz' : z ∈ C ∧ ∀ y ∈ C, Psi z ≤ Psi y := by
      rw [hs] at hz
      exact hz
    have hzval : Psi z = Psi z0 := le_antisymm (hz'.2 z0 hz0'.1) (hz0'.2 z hz'.1)
    let Ez : ℝ → ℝ := fun t => (1 / 2) * ‖x t - z‖ ^ 2 + mu * G t
    have hEzhas (t : ℝ) (ht : 0 ≤ t) : HasDerivAt Ez
        (inner ℝ (F t) (x t - z) + mu * inner ℝ (∇ Psi (x t)) (F t)) t := by
      have hdistance := ((hclassical t ht).sub_const z).norm_sq.const_mul (1 / 2 : ℝ)
      have hpsi := hPsiDeriv t ht
      simpa [Ez, G, F, real_inner_comm] using
        hdistance.add ((hpsi.sub_const (Psi z0)).const_mul mu)
    have hEzderiv (t : ℝ) (ht : 0 ≤ t) : deriv Ez t ≤ 0 := by
      have h := projection_gradient_energy_deriv Psi C projection mu x z t hz'.1 hmu hconvex
        (fun q ↦ (hgradient q).differentiableAt) hC hprojection_mem
        hprojection_min_dist (hclassical t ht)
      have hfun : Ez = fun s => (1 / 2) * ‖x s - z‖ ^ 2 +
          mu * (Psi (x s) - Psi z) := by
        funext s
        simp [Ez, G, hzval]
      rw [← hfun, (hEzhas t ht).deriv] at h
      rw [(hEzhas t ht).deriv]
      dsimp [F] at h ⊢
      calc
        inner ℝ (projection (x t - mu • ∇ Psi (x t)) - x t) (x t - z) +
            mu * inner ℝ (∇ Psi (x t))
              (projection (x t - mu • ∇ Psi (x t)) - x t) ≤
            _ + ‖projection (x t - mu • ∇ Psi (x t)) - x t‖ ^ 2 :=
          le_add_of_nonneg_right (sq_nonneg _)
        _ ≤ mu * (Psi z - Psi (x t)) := h
        _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hmu.le
          (sub_nonpos.mpr (hz'.2 (x t) (hforward t ht)))
    have hEzanti : AntitoneOn Ez (Set.Ici 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      · intro t ht
        exact (hEzhas t ht).continuousAt.continuousWithinAt
      · intro t ht
        exact (hEzhas t (interior_subset ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        exact hEzderiv t (interior_subset ht)
    have hEznonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ Ez t := by
      exact add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
        (mul_nonneg hmu.le (hGnonneg t ht))
    obtain ⟨l, hEzlim⟩ := tendsto_of_antitone_nonneg_on_Ici_local Ez hEzanti hEznonneg
    have hsq : Tendsto (fun t => ‖x t - z‖ ^ 2) atTop (nhds (2 * l)) := by
      convert (hEzlim.sub (hGlim.const_mul mu)).const_mul 2 using 1
      · ext t
        simp [Ez]
      · ring_nf
    refine ⟨Real.sqrt (2 * l), ?_⟩
    have hsqrt := Real.continuous_sqrt.tendsto (2 * l) |>.comp hsq
    convert hsqrt using 1
    ext t
    simp
  have hcluster : ∀ z, (∃ u : ℕ → ℝ, Tendsto u atTop atTop ∧
      Tendsto (fun n ↦ toWeakSpace ℝ H (x (u n))) atTop
        (nhds (toWeakSpace ℝ H z))) → z ∈ S := by
    rintro z ⟨u, huTop, huWeak⟩
    have huNonneg : ∀ᶠ n in atTop, 0 ≤ u n := (tendsto_atTop.1 huTop) 0
    have hCweak : IsClosed (toWeakSpace ℝ H '' C) :=
      (isClosed_iff_weak_image_isClosed_of_convex hC.2).1 hC.1
    have hzWeakC : toWeakSpace ℝ H z ∈ toWeakSpace ℝ H '' C :=
      hCweak.mem_of_tendsto huWeak (huNonneg.mono fun n hn =>
        ⟨x (u n), hforward (u n) hn, rfl⟩)
    have hzC : z ∈ C := by
      rcases hzWeakC with ⟨y, hyC, hyz⟩
      have : y = z := (toWeakSpace ℝ H).injective hyz
      simpa [this] using hyC
    have hzPsi : Psi z ≤ Psi z0 := by
      by_contra hnot
      have hlt : Psi z0 < Psi z := lt_of_not_ge hnot
      let eps : ℝ := (Psi z - Psi z0) / 2
      have heps : 0 < eps := by dsimp [eps]; linarith
      let L : Set H := {y | Psi y ≤ Psi z0 + eps}
      have hLclosed : IsClosed L := by
        exact isClosed_Iic.preimage hPsiCont
      have hLconvex : Convex ℝ L := by
        intro a ha b hb α β hα hβ hab
        dsimp [L] at ha hb ⊢
        have hcv := hconvex.2 (Set.mem_univ a) (Set.mem_univ b) hα hβ hab
        change Psi (α • a + β • b) ≤ α * Psi a + β * Psi b at hcv
        calc
          Psi (α • a + β • b) ≤ α * Psi a + β * Psi b := hcv
          _ ≤ α * (Psi z0 + eps) + β * (Psi z0 + eps) :=
            add_le_add (mul_le_mul_of_nonneg_left ha hα)
              (mul_le_mul_of_nonneg_left hb hβ)
          _ = Psi z0 + eps := by rw [← add_mul, hab, one_mul]
      have hLweak : IsClosed (toWeakSpace ℝ H '' L) :=
        (isClosed_iff_weak_image_isClosed_of_convex hLconvex).1 hLclosed
      have hvalues : Tendsto (fun n => Psi (x (u n))) atTop (nhds (Psi z0)) :=
        hobjlim.comp huTop
      have hevent : ∀ᶠ n in atTop, x (u n) ∈ L := by
        filter_upwards [(tendsto_order.1 hvalues).2 _ (lt_add_of_pos_right _ heps)] with n hn
        exact hn.le
      have hzLweak : toWeakSpace ℝ H z ∈ toWeakSpace ℝ H '' L :=
        hLweak.mem_of_tendsto huWeak (hevent.mono fun n hn => ⟨x (u n), hn, rfl⟩)
      rcases hzLweak with ⟨y, hyL, hyz⟩
      have hyz' : y = z := (toWeakSpace ℝ H).injective hyz
      dsimp [L] at hyL
      rw [hyz'] at hyL
      dsimp [eps] at hyL
      linarith
    rw [hs]
    exact ⟨hzC, fun y hy => hzPsi.trans (hz0'.2 y hy)⟩
  obtain ⟨z, hzS, hweak⟩ := opial_trajectory_lemma S x ⟨z0, hz0⟩ hdist hcluster
  exact ⟨⟨z, hzS, hweak⟩, hforward, hanti, by simpa [hInf] using hobjlim, haediss⟩

end AbbasDynamical2015
