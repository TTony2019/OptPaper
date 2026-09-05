import Mathlib
import Foundation.FixedPoint.Nonexpansive

namespace AttouchAdlyDryFrictionDynamics2023

open scoped InnerProductSpace

/-- The closed ball centred at zero, using Mathlib's canonical metric ball. -/
def frictionBall {H : Type*} [PseudoMetricSpace H] [Zero H] (r : ℝ) : Set H := Metric.closedBall 0 r

/-- Points of the friction ball which realize the metric distance from `x`. -/
def IsFrictionBallBestApproximation {H : Type*} [PseudoMetricSpace H] [Zero H]
    (r : ℝ) (x p : H) : Prop :=
  p ∈ frictionBall r ∧ dist x p = Metric.infDist x (frictionBall r)

/-- The set-valued metric projector onto the friction ball. -/
noncomputable def frictionBallProjector {H : Type*} [PseudoMetricSpace H] [Zero H] (r : ℝ) : H → Set H :=
  fun x ↦ {p | IsFrictionBallBestApproximation r x p}

/-- A closed friction ball in a complete real Hilbert space has a unique nearest point. -/
theorem frictionBall_isChebyshev {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {r : ℝ} (hr : 0 ≤ r) :
    ∀ x : H, ∃! p : H, IsFrictionBallBestApproximation r x p := by
  intro x
  have hnonempty : (frictionBall (H := H) r).Nonempty := by
    simpa [frictionBall] using (Metric.nonempty_closedBall.mpr hr : (Metric.closedBall (0 : H) r).Nonempty)
  have hclosed : IsClosed (frictionBall (H := H) r) := by
    simpa [frictionBall] using (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0 : H) r))
  have hconvex : Convex ℝ (frictionBall (H := H) r) := by
    simpa [frictionBall] using (convex_closedBall (0 : H) r)
  rcases exists_norm_eq_iInf_of_complete_convex hnonempty hclosed.isComplete hconvex x with
    ⟨p, hp, hpmin⟩
  refine ⟨p, ?_, ?_⟩
  · constructor
    · exact hp
    · rw [Metric.infDist_eq_iInf]
      simpa [dist_eq_norm] using hpmin
  · intro q hq
    have hpmin' : ‖x - p‖ = ⨅ y : frictionBall (H := H) r, ‖x - (y : H)‖ := by
      simpa [dist_eq_norm, Metric.infDist_eq_iInf] using
        (show dist x p = Metric.infDist x (frictionBall r) from
          (by
            rw [Metric.infDist_eq_iInf]
            simpa [dist_eq_norm] using hpmin))
    have hqmin : ‖x - q‖ = ⨅ y : frictionBall (H := H) r, ‖x - (y : H)‖ := by
      simpa [dist_eq_norm, Metric.infDist_eq_iInf] using hq.2
    have hp_inner := (norm_eq_iInf_iff_real_inner_le_zero hconvex hp).mp hpmin' q hq.1
    have hq_inner := (norm_eq_iInf_iff_real_inner_le_zero hconvex hq.1).mp hqmin p hp
    have hq_inner' : 0 ≤ ⟪x - q, q - p⟫_ℝ := by
      rw [show q - p = -(p - q) by abel, inner_neg_right]
      exact neg_nonneg.mpr hq_inner
    have hp_expand :
        ⟪x - p, q - p⟫_ℝ = ⟪x - q, q - p⟫_ℝ + ‖q - p‖ ^ 2 := by
      calc
        ⟪x - p, q - p⟫_ℝ = ⟪(x - q) + (q - p), q - p⟫_ℝ := by
          congr 1
          abel
        _ = ⟪x - q, q - p⟫_ℝ + ⟪q - p, q - p⟫_ℝ := by rw [inner_add_left]
        _ = ⟪x - q, q - p⟫_ℝ + ‖q - p‖ ^ 2 := by rw [real_inner_self_eq_norm_sq, sq]
    have hpq_sq : ‖q - p‖ ^ 2 ≤ 0 := by
      rw [hp_expand] at hp_inner
      nlinarith
    have hpq_eq : q - p = 0 := by
      exact norm_eq_zero.mp <| sq_eq_zero_iff.mp <| le_antisymm hpq_sq (sq_nonneg ‖q - p‖)
    exact sub_eq_zero.mp hpq_eq

/-- The unique metric projection onto a positive-radius friction ball. -/
noncomputable def frictionBallProjection {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (r : ℝ) (hr : 0 < r) : H → H :=
  fun x ↦ (frictionBall_isChebyshev (le_of_lt hr) x).choose

/-- The paper-local ball projection is the residual complement of soft thresholding. -/
theorem frictionBallProjection_eq_sub_softThresholder {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (r : ℝ) (hr : 0 < r) (x : H) :
    frictionBallProjection r hr x = x - softThresholder r x := by
  let C : Set H := Metric.closedBall 0 r
  have hCnonempty : C.Nonempty := by
    simpa [C] using (Metric.nonempty_closedBall.mpr hr.le : (Metric.closedBall (0 : H) r).Nonempty)
  have hCclosed : IsClosed C := by
    simpa [C] using (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0 : H) r))
  have hCconvex : Convex ℝ C := by
    simpa [C] using (convex_closedBall (0 : H) r)
  let hC : IsChebyshev C := isChebyshev_of_nonempty_isClosed_convex hCnonempty hCclosed hCconvex
  have hlocal : frictionBallProjection r hr x = projectionPoint C hC x := by
    apply (hC x).unique
    · exact (frictionBall_isChebyshev hr.le x).choose_spec.1
    · exact projectionPoint_isBestApproximation C hC x
  rw [hlocal, softThresholder_eq_sub_projection_closedBall r hr x]
  abel

noncomputable def frictionBallDistance {H : Type*} [PseudoMetricSpace H] [Zero H] (r : ℝ) (x : H) : ℝ :=
  Metric.infDist x (frictionBall r)

def IsFrictionBallProjection {H : Type*} [PseudoMetricSpace H] [Zero H]
    (r : ℝ) (x p : H) : Prop := p ∈ frictionBallProjector r x

end AttouchAdlyDryFrictionDynamics2023
