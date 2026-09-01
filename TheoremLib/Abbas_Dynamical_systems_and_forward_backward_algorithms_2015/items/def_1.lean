import Mathlib
import Foundation.Convex.Subdifferential

namespace AbbasDynamical2015

open MeasureTheory

/-- A strong global solution of (8)--(10). -/
structure StrongGlobalSolution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (lam : ℝ) (x0 v0 : H) where
  x : ℝ → H
  v : ℝ → H
  x_absolutelyContinuous : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval x 0 b
  v_absolutelyContinuous : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval v 0 b
  subgradient : ∀ t, 0 ≤ t → v t ∈ ERealFunction.subdifferential Phi (x t)
  differential_equation : ∀ᵐ t ∂volume.restrict (Set.Ici 0),
    lam • deriv x t + deriv v t + v t + B (x t) = 0
  initial_x : x 0 = x0
  initial_v : v 0 = v0

/-- A constant-parameter strong solution expressed through the differentiable
combined variable `lam • x + v`.  This is equivalent to the differential
equation in the paper wherever the two component derivatives exist, while it
does not require recovering Hilbert-valued derivatives from absolute
continuity merely to state the dynamics. -/
def IsStrongGlobalSolutionCombined {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (B : H → H) (lam : ℝ) (x0 v0 : H)
    (x v : ℝ → H) : Prop :=
  (∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval x 0 b) ∧
  (∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval v 0 b) ∧
  (∀ t, 0 ≤ t → v t ∈ ERealFunction.subdifferential Phi (x t)) ∧
  (∀ᵐ t ∂volume.restrict (Set.Ici 0),
    HasDerivAt (fun s => lam • x s + v s) (-(v t + B (x t))) t) ∧
  x 0 = x0 ∧ v 0 = v0

/-- Strong-orbit data with explicit component velocities.  Downstream chain
rules and Lyapunov arguments should consume these witnesses instead of trying
to infer differentiability from Lean's total `deriv`. -/
def IsStrongOrbitWithVelocity {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (B : H → H) (lam : ℝ)
    (x v dx dv : ℝ → H) : Prop :=
  (∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval x 0 b) ∧
  (∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval v 0 b) ∧
  (∀ t, 0 ≤ t → v t ∈ ERealFunction.subdifferential Phi (x t)) ∧
  (∀ᵐ t ∂volume.restrict (Set.Ici 0),
    HasDerivAt x (dx t) t ∧ HasDerivAt v (dv t) t ∧
      lam • dx t + dv t + v t + B (x t) = 0)

end AbbasDynamical2015
