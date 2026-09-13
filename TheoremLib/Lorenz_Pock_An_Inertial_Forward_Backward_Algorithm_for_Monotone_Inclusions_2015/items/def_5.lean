import Mathlib
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.def_3

namespace LorenzPock

/-- The operator-valued primal--dual preconditioner of §3.2,

`M = [[T⁻¹, -K*], [-K, Σ⁻¹]]`,

realized as a bounded linear operator on the `L²`-product.  Following the paper,
`T` and `Σ` are the (self-adjoint, positive definite) maps whose inverses appear in the
preconditioner, so the arguments here are their inverses. -/
noncomputable def operatorPreconditioner {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] [CompleteSpace Y] (Tinv : X →L[ℝ] X) (Sigmainv : Y →L[ℝ] Y)
    (K : X →L[ℝ] Y) : WithLp 2 (X × Y) →L[ℝ] WithLp 2 (X × Y) :=
  blockOperator Tinv Sigmainv K

theorem operatorPreconditioner_apply {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] [CompleteSpace Y] (Tinv : X →L[ℝ] X) (Sigmainv : Y →L[ℝ] Y)
    (K : X →L[ℝ] Y) (u : WithLp 2 (X × Y)) :
    operatorPreconditioner Tinv Sigmainv K u
      = WithLp.toLp 2 (Tinv u.ofLp.1 - K.adjoint u.ofLp.2,
          -K u.ofLp.1 + Sigmainv u.ofLp.2) := by
  simp [operatorPreconditioner]

end LorenzPock
