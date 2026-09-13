import Mathlib
import Foundation.Analysis.ExtendedRealFunctions

namespace LorenzPock

/-- Data of the convex--concave saddle-point problem (19). -/
structure SaddlePointProblem (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [InnerProductSpace ℝ Y] [CompleteSpace Y] where
  G : X → EReal
  Q : X → EReal
  FStar : Y → EReal
  PStar : Y → EReal
  K : X →L[ℝ] Y
  convex_G : Convex ℝ (ERealFunction.epigraph G)
  convex_Q : Convex ℝ (ERealFunction.epigraph Q)
  convex_FStar : Convex ℝ (ERealFunction.epigraph FStar)
  convex_PStar : Convex ℝ (ERealFunction.epigraph PStar)
  gradQ : X → X
  gradPStar : Y → Y
  QReal : X → ℝ
  PStarReal : Y → ℝ
  Q_real_valued : ∀ x, Q x = QReal x
  PStar_real_valued : ∀ y, PStar y = PStarReal y
  differentiable_Q : Differentiable ℝ QReal
  differentiable_PStar : Differentiable ℝ PStarReal
  gradQ_is_gradient : ∀ x v, fderiv ℝ QReal x v = inner ℝ (gradQ x) v
  gradPStar_is_gradient : ∀ y v, fderiv ℝ PStarReal y v = inner ℝ (gradPStar y) v
  LQ : ℝ
  LP : ℝ
  gradQ_lipschitz : ∀ x y, ‖gradQ x - gradQ y‖ ≤ LQ * ‖x - y‖
  gradPStar_lipschitz : ∀ x y, ‖gradPStar x - gradPStar y‖ ≤ LP * ‖x - y‖

end LorenzPock
