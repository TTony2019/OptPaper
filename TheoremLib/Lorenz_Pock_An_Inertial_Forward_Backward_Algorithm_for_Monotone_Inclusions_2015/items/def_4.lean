import Mathlib
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.def_3

namespace LorenzPock

/-- The scalar-step primal--dual preconditioner (20), realized as a bounded linear
operator on the `L²`-product:

`M = [[τ⁻¹ Id, -K*], [-K, σ⁻¹ Id]]`.

The paper requires `M` to be a bounded linear self-adjoint positive definite map; the
positive definiteness is *derived* from condition (22) in `thm_5`, not assumed here. -/
noncomputable def primalDualPreconditioner {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] [CompleteSpace Y] (K : X →L[ℝ] Y) (τ σ : ℝ) :
    WithLp 2 (X × Y) →L[ℝ] WithLp 2 (X × Y) :=
  blockOperator (τ⁻¹ • ContinuousLinearMap.id ℝ X) (σ⁻¹ • ContinuousLinearMap.id ℝ Y) K

theorem primalDualPreconditioner_apply {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] [CompleteSpace Y] (K : X →L[ℝ] Y) (τ σ : ℝ)
    (u : WithLp 2 (X × Y)) :
    primalDualPreconditioner K τ σ u
      = WithLp.toLp 2 (τ⁻¹ • u.ofLp.1 - K.adjoint u.ofLp.2,
          -K u.ofLp.1 + σ⁻¹ • u.ofLp.2) := by
  simp [primalDualPreconditioner]

/-- The quadratic form of the preconditioner (20), i.e. the `M`-squared norm of
Theorem 5: `‖(x, y)‖²_M = τ⁻¹‖x‖² - 2⟪K x, y⟫ + σ⁻¹‖y‖²`. -/
noncomputable def primalDualMnormSq {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] [CompleteSpace Y] (K : X →L[ℝ] Y) (τ σ : ℝ)
    (z : X × Y) : ℝ :=
  τ⁻¹ * ‖z.1‖ ^ 2 + σ⁻¹ * ‖z.2‖ ^ 2 - 2 * inner ℝ (K z.1) z.2

/-- Condition (23) is the summability of `α_k ‖(x^k,y^k) - (x^{k-1},y^{k-1})‖²_M`; this
identifies the quadratic form `primalDualMnormSq` with `⟪M z, z⟫` for the operator of (20). -/
theorem primalDualMnormSq_eq_inner {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] [CompleteSpace Y] (K : X →L[ℝ] Y) (τ σ : ℝ) (z : X × Y) :
    primalDualMnormSq K τ σ z
      = inner ℝ (primalDualPreconditioner K τ σ (WithLp.toLp 2 z)) (WithLp.toLp 2 z) := by
  rw [primalDualMnormSq, primalDualPreconditioner, blockOperator_inner]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  ring

/-- The diagonal operator `C = diag(D, E)` of the preconditioned setting (§3.2). -/
noncomputable def diagonalPreconditioner {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] [CompleteSpace Y] (D : X →L[ℝ] X) (E : Y →L[ℝ] Y) :
    WithLp 2 (X × Y) →L[ℝ] WithLp 2 (X × Y) :=
  diagonalBlockOperator D E

@[simp] theorem diagonalPreconditioner_apply {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] [CompleteSpace Y] (D : X →L[ℝ] X) (E : Y →L[ℝ] Y)
    (u : WithLp 2 (X × Y)) :
    diagonalPreconditioner D E u = WithLp.toLp 2 (D u.ofLp.1, E u.ofLp.2) := by
  simp [diagonalPreconditioner]

end LorenzPock
