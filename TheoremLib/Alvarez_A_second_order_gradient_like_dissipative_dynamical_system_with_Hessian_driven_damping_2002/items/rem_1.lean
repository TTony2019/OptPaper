import Mathlib
import Foundation.Projection.BestApproximation

namespace Alvarez2002

open Filter
open scoped InnerProductSpace

/-- Quadratic-potential remark: the limit is the projection of `x₀ + α⁻¹v₀`
onto the kernel of the positive self-adjoint operator. -/
theorem quadratic_potential_limit_remark {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (A : H →L[ℝ] H)
    (hselfadjoint : ∀ u v, ⟪A u, v⟫_ℝ = ⟪u, A v⟫_ℝ)
    (hpositive : ∀ u, 0 ≤ ⟪A u, u⟫_ℝ)
    (hyp : DINHypotheses H) (sys : DINSystem H) (hmatch : sys.MatchesHypotheses hyp)
    (sol : DINSolution sys) (x₀ v₀ : H) (hx₀ : sol.x 0 = x₀) (hv₀ : sol.dx 0 = v₀)
    (hphi : ∀ u, sys.phi u = (1 / 2 : ℝ) * ⟪A u, u⟫_ℝ)
    (hgrad : ∀ u, sys.grad u = A u) (hhess : ∀ u, sys.hess u = A) :
    ({z | ∀ y, sys.phi z ≤ sys.phi y} : Set H) = (A.ker : Set H) ∧
    ∃ p, p ∈ A.ker ∧
      ‖x₀ + (sys.alpha⁻¹ : ℝ) • v₀ - p‖ =
        Metric.infDist (x₀ + (sys.alpha⁻¹ : ℝ) • v₀) (A.ker : Set H) ∧
      Tendsto sol.x atTop (nhds p) := by
  have hquad := quadratic_din_limit_characterization A hselfadjoint hpositive hyp sys hmatch sol
    x₀ v₀ hx₀ hv₀ hphi hgrad hhess
  rcases hquad.2 with ⟨xInf, hxInfKer, hxInf, hvZero, horth⟩
  refine ⟨hquad.1, xInf, hxInfKer, ?_, hxInf⟩
  let q : H := x₀ + (sys.alpha⁻¹ : ℝ) • v₀
  let K : Set H := (A.ker : Set H)
  have hKnonempty : K.Nonempty := by
    refine ⟨0, ?_⟩
    simp [K]
  have hKclosed : IsClosed K := by
    simpa [K] using (A.isClosed_ker : IsClosed (A.ker : Set H))
  have hKconvex : Convex ℝ K := by
    simpa [K] using (A.ker.convex : Convex ℝ (A.ker : Set H))
  let hCheb := isChebyshev_of_nonempty_isClosed_convex hKnonempty hKclosed hKconvex
  have hvariational : ∀ z ∈ K, ⟪z - xInf, q - xInf⟫_ℝ ≤ 0 := by
    intro z hz
    have hzsub : z - xInf ∈ A.ker := A.ker.sub_mem (by simpa [K] using hz) hxInfKer
    have hzorth := horth (z - xInf) hzsub
    have hrewrite : xInf - x₀ - (sys.alpha⁻¹ : ℝ) • v₀ = xInf - q := by
      simp [q]
      abel
    rw [hrewrite] at hzorth
    have hzero : ⟪z - xInf, q - xInf⟫_ℝ = 0 := by
      calc
        ⟪z - xInf, q - xInf⟫_ℝ = -⟪z - xInf, xInf - q⟫_ℝ := by
          rw [show q - xInf = -(xInf - q) by abel, inner_neg_right]
        _ = -⟪xInf - q, z - xInf⟫_ℝ := by rw [real_inner_comm]
        _ = 0 := by rw [hzorth, neg_zero]
    exact le_of_eq hzero
  have hxproj : xInf = projectionPoint K hCheb q := by
    refine (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos hCheb hKconvex).mpr ?_
    exact ⟨by simpa [K] using hxInfKer, hvariational⟩
  calc
    ‖x₀ + (sys.alpha⁻¹ : ℝ) • v₀ - xInf‖ = dist q xInf := by
      simp [q, dist_eq_norm]
    _ = dist q (projectionPoint K hCheb q) := by rw [← hxproj]
    _ = Metric.infDist q K := (projectionPoint_isBestApproximation K hCheb q).2
    _ = Metric.infDist (x₀ + (sys.alpha⁻¹ : ℝ) • v₀) (A.ker : Set H) := by simp [q, K]

end Alvarez2002
