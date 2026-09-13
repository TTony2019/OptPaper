import Mathlib
import Foundation.SetValued.Monotone
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.def_2
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.ext_def_2

namespace LorenzPock

/-- The primal--dual monotone operators associated with (19). -/
structure PrimalDualOperators (X Y : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y] where
  A : SetValuedOperator (X × Y) (X × Y)
  B : (X × Y) → X × Y
  K : X →L[ℝ] Y
  subG : SetValuedOperator X X
  subFStar : SetValuedOperator Y Y
  gradQ : X → X
  gradPStar : Y → Y
  optimalitySystem : X × Y → Prop
  A_formula : ∀ x y, A (x, y) = {uv | uv.1 - K.adjoint y ∈ subG x ∧ uv.2 + K x ∈ subFStar y}
  B_formula : ∀ x y, B (x, y) = (gradQ x, gradPStar y)
  optimality_system_formula : ∀ x y, optimalitySystem (x, y) ↔
    ∃ a ∈ A (x, y), (0, 0) = a + B (x, y)

/-! ## The concrete operators of (19) on the product Hilbert space

The paper regards `A` and `B` as operators on `X × Y`; the formalization works on the
`L²`-product `WithLp 2 (X × Y)`, whose inner product is
`⟪(x₁,y₁), (x₂,y₂)⟫ = ⟪x₁,x₂⟫ + ⟪y₁,y₂⟫` (`WithLp.prod_inner_apply`).

The generic block constructor below packages the bounded operator
`[[f, -K*], [-K, g]]` — the shape of every preconditioner in §§3.1--3.2 — as a genuine
element of `WithLp 2 (X × Y) →L[ℝ] WithLp 2 (X × Y)`. -/

/-- The block operator `[[f, -K*], [-K, g]]` on the `L²`-product. -/
noncomputable def blockOperator {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (f : X →L[ℝ] X) (g : Y →L[ℝ] Y) (K : X →L[ℝ] Y) :
    WithLp 2 (X × Y) →L[ℝ] WithLp 2 (X × Y) :=
  let e : WithLp 2 (X × Y) →L[ℝ] X × Y := WithLp.prodContinuousLinearEquiv 2 ℝ X Y
  let e' : X × Y →L[ℝ] WithLp 2 (X × Y) := (WithLp.prodContinuousLinearEquiv 2 ℝ X Y).symm
  e'.comp ((ContinuousLinearMap.prod
        (f.comp (ContinuousLinearMap.fst ℝ X Y) -
          K.adjoint.comp (ContinuousLinearMap.snd ℝ X Y))
        (g.comp (ContinuousLinearMap.snd ℝ X Y) -
          K.comp (ContinuousLinearMap.fst ℝ X Y)) :
      X × Y →L[ℝ] X × Y).comp e)

@[simp] theorem blockOperator_apply {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (f : X →L[ℝ] X) (g : Y →L[ℝ] Y) (K : X →L[ℝ] Y) (u : WithLp 2 (X × Y)) :
    blockOperator f g K u
      = WithLp.toLp 2 (f u.ofLp.1 - K.adjoint u.ofLp.2, -K u.ofLp.1 + g u.ofLp.2) := by
  simp [blockOperator, sub_eq_add_neg, add_comm]

/-- The quadratic form of `[[f, -K*], [-K, g]]`, with the off-diagonal contribution
combined: `⟪f x, x⟫ - 2⟪K x, y⟫ + ⟪g y, y⟫`. -/
theorem blockOperator_inner {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (f : X →L[ℝ] X) (g : Y →L[ℝ] Y) (K : X →L[ℝ] Y) (u : WithLp 2 (X × Y)) :
    inner ℝ (blockOperator f g K u) u
      = inner ℝ (f u.ofLp.1) u.ofLp.1 - 2 * inner ℝ (K u.ofLp.1) u.ofLp.2
        + inner ℝ (g u.ofLp.2) u.ofLp.2 := by
  rw [blockOperator_apply, WithLp.prod_inner_apply]
  simp only [inner_sub_left, inner_add_left, inner_neg_left,
    ContinuousLinearMap.adjoint_inner_left]
  rw [real_inner_comm u.ofLp.2 (K u.ofLp.1)]
  ring

/-- The block operator `[[f, -K*], [-K, g]]` is self-adjoint as soon as `f` and `g` are. -/
theorem blockOperator_inner_comm {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (f : X →L[ℝ] X) (g : Y →L[ℝ] Y) (K : X →L[ℝ] Y)
    (hf : ∀ x y, inner ℝ (f x) y = inner ℝ x (f y))
    (hg : ∀ a b, inner ℝ (g a) b = inner ℝ a (g b)) (u v : WithLp 2 (X × Y)) :
    inner ℝ (blockOperator f g K u) v = inner ℝ u (blockOperator f g K v) := by
  rw [blockOperator_apply, blockOperator_apply, WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  simp only [inner_sub_left, inner_sub_right, inner_neg_left, inner_neg_right,
    inner_add_left, inner_add_right, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right, hf, hg]
  ring

/-- The diagonal block operator `diag(f, g)`. -/
noncomputable def diagonalBlockOperator {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y] (f : X →L[ℝ] X) (g : Y →L[ℝ] Y) :
    WithLp 2 (X × Y) →L[ℝ] WithLp 2 (X × Y) :=
  blockOperator f g 0

@[simp] theorem diagonalBlockOperator_apply {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y] (f : X →L[ℝ] X) (g : Y →L[ℝ] Y) (u : WithLp 2 (X × Y)) :
    diagonalBlockOperator f g u = WithLp.toLp 2 (f u.ofLp.1, g u.ofLp.2) := by
  simp [diagonalBlockOperator]

/-- The zero map on `Y`, used to turn `K` into a `CLM` in the generic block constructor.

The block constructor expects its third argument to be a map `X →L[ℝ] Y`; the diagonal
operators below pass `K = 0`. -/
theorem blockOperator_inner_diag {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (f : X →L[ℝ] X) (g : Y →L[ℝ] Y) (u : WithLp 2 (X × Y)) :
    inner ℝ (diagonalBlockOperator f g u) u
      = inner ℝ (f u.ofLp.1) u.ofLp.1 + inner ℝ (g u.ofLp.2) u.ofLp.2 := by
  rw [diagonalBlockOperator_apply, WithLp.prod_inner_apply]

/-- The set-valued operator `A = [[∂G, K*], [-K, ∂F*]]` of (19) on the `L²`-product. -/
noncomputable def primalDualSetOperator {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y] (G : X → EReal) (FStar : Y → EReal) (K : X →L[ℝ] Y) :
    SetValuedOperator (WithLp 2 (X × Y)) (WithLp 2 (X × Y)) :=
  fun u ↦ {v | v.ofLp.1 - K.adjoint u.ofLp.2 ∈ ERealFunction.subdifferential G u.ofLp.1 ∧
    v.ofLp.2 + K u.ofLp.1 ∈ ERealFunction.subdifferential FStar u.ofLp.2}

@[simp] theorem mem_primalDualSetOperator {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y] (G : X → EReal) (FStar : Y → EReal) (K : X →L[ℝ] Y)
    (u v : WithLp 2 (X × Y)) :
    v ∈ primalDualSetOperator G FStar K u ↔
      v.ofLp.1 - K.adjoint u.ofLp.2 ∈ ERealFunction.subdifferential G u.ofLp.1 ∧
        v.ofLp.2 + K u.ofLp.1 ∈ ERealFunction.subdifferential FStar u.ofLp.2 :=
  Iff.rfl

/-- The single-valued operator `B = diag(∇Q, ∇P^*)` of (19) on the `L²`-product. -/
noncomputable def primalDualGradientOperator {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y] (gradQ : X → X) (gradPStar : Y → Y) :
    WithLp 2 (X × Y) → WithLp 2 (X × Y) :=
  fun u ↦ WithLp.toLp 2 (gradQ u.ofLp.1, gradPStar u.ofLp.2)

@[simp] theorem primalDualGradientOperator_apply {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y] (gradQ : X → X) (gradPStar : Y → Y) (u : WithLp 2 (X × Y)) :
    primalDualGradientOperator gradQ gradPStar u
      = WithLp.toLp 2 (gradQ u.ofLp.1, gradPStar u.ofLp.2) :=
  rfl

/-- The quadratic form of the gradient operator on the product. -/
theorem primalDualGradientOperator_inner {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y] (gradQ : X → X) (gradPStar : Y → Y) (u v : WithLp 2 (X × Y)) :
    inner ℝ (primalDualGradientOperator gradQ gradPStar u) v
      = inner ℝ (gradQ u.ofLp.1) v.ofLp.1 + inner ℝ (gradPStar u.ofLp.2) v.ofLp.2 := by
  rw [primalDualGradientOperator_apply, WithLp.prod_inner_apply]

/-- The optimality system `0 ∈ (A + B)(x, y)` of (19), spelled out: `z` is a saddle point
of (19) precisely when these two inclusions hold.  Theorems 5 and 9 conclude that the
iterates converge weakly to a point satisfying this system. -/
def IsPrimalDualSolution {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (G : X → EReal) (FStar : Y → EReal) (gradQ : X → X) (gradPStar : Y → Y)
    (K : X →L[ℝ] Y) (z : WithLp 2 (X × Y)) : Prop :=
  (∃ g ∈ ERealFunction.subdifferential G z.ofLp.1,
    g + gradQ z.ofLp.1 + K.adjoint z.ofLp.2 = 0) ∧
  (∃ f ∈ ERealFunction.subdifferential FStar z.ofLp.2,
    f + gradPStar z.ofLp.2 - K z.ofLp.1 = 0)

end LorenzPock
